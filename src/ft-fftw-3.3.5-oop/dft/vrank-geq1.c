/*
 * Copyright (c) 2003, 2007-14 Matteo Frigo
 * Copyright (c) 2003, 2007-14 Massachusetts Institute of Technology
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */



/* Plans for handling vector transform loops.  These are *just* the
   loops, and rely on child plans for the actual DFTs.
 
   They form a wrapper around solvers that don't have apply functions
   for non-null vectors.
 
   vrank-geq1 plans also recursively handle the case of multi-dimensional
   vectors, obviating the need for most solvers to deal with this.  We
   can also play games here, such as reordering the vector loops.
 
   Each vrank-geq1 plan reduces the vector rank by 1, picking out a
   dimension determined by the vecloop_dim field of the solver. */

#include "dft.h"
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

typedef struct {
     solver super;
     int vecloop_dim;
     const int *buddies;
     size_t nbuddies;
} S;

typedef struct {
     plan_dft super;

     plan *cld;
     INT vl;
     INT ivs, ovs;
     const S *solver;
} P;

// copied from trig.c begin
#if defined(TRIGREAL_IS_LONG_DOUBLE)
#  define COS cosl
#  define SIN sinl
#  define KTRIG(x) (x##L)
#  if defined(HAVE_DECL_SINL) && !HAVE_DECL_SINL
     extern long double sinl(long double x);
#  endif
#  if defined(HAVE_DECL_COSL) && !HAVE_DECL_COSL
     extern long double cosl(long double x);
#  endif
#elif defined(TRIGREAL_IS_QUAD)
#  define COS cosq
#  define SIN sinq
#  define KTRIG(x) (x##Q)
   extern __float128 sinq(__float128 x);
   extern __float128 cosq(__float128 x);
#else
#  define COS cos
#  define SIN sin
#  define KTRIG(x) (x)
#endif

static const trigreal K2PI =
    KTRIG(6.2831853071795864769252867665590057683943388);
#define by2pi(m, n) ((K2PI * (m)) / (n))

/*
 * Improve accuracy by reducing x to range [0..1/8]
 * before multiplication by 2 * PI.
 */

static void real_cexp(INT m, INT n, trigreal *out)
{
     trigreal theta, c, s, t;
     unsigned octant = 0;
     INT quarter_n = n;

     n += n; n += n;
     m += m; m += m;

     if (m < 0) m += n;
     if (m > n - m) { m = n - m; octant |= 4; }
     if (m - quarter_n > 0) { m = m - quarter_n; octant |= 2; }
     if (m > quarter_n - m) { m = quarter_n - m; octant |= 1; }

     theta = by2pi(m, n);
     register trigreal dmr = by2pi(m, n);
     if(theta!=dmr) printf("real_cexp error! theta\n");

     c = COS(theta); s = SIN(theta);
     dmr = c*c + s*s - 1;
     if(dmr>0.0001 || dmr <-0.0001 ) printf("real_cexp error! c,s\n");

     if (octant & 1) { t = c; c = s; s = t; }
     if (octant & 2) { t = c; c = -s; s = t; }
     if (octant & 4) { s = -s; }

     out[0] = c; 
     out[1] = s; 
}

// copied from trig.c end

// bool start = true;
extern bool FFTstart;
extern int myRadix;
extern bool firstFFT;
extern bool secondFFT;

// int m;
R delta = 0.001;

extern R * checksum1;
extern R * checksum2;
R * dmrOutChecksum1;
R * dmrOutChecksum2;

extern R * coeff;
extern R * simpleCoeff;
extern R * rA1;

// memory checksums
R * simpleCoeff; // 1/i, the coefficients for memory check before twiddle
R * outChecksum1; // sum(a_i), intermediate checksums
R * outChecksum2; // sum(1/i a_i), intermediate checksums

bool DMR = false;
R * dmrInputBuffer;
int radix;

int ratio;
bool inject = false;

R * inputBuffer;

static void apply(const plan *ego_, R *ri, R *ii, R *ro, R *io)
{
     const P *ego = (const P *) ego_;
     INT i, vl = ego->vl;
     INT ivs = ego->ivs, ovs = ego->ovs;
     dftapply cldapply = ((plan_dft *) ego->cld)->apply;
     int radix;
       // printf("vrank-geq1 apply\n");
     if(firstFFT)
     {

       int m;

       R * checksum1; // sum(rA a)
       R * checksum2; // sum(1/i a_i)
       R sumrA0 = 0, sumrA1 = 0;
       R * rA1;
       R * coeff;

       if(FFTstart == true)
       {
          FFTstart = false;
          radix = vl;
          m = myRadix/radix;
          delta = 0.01;
          //printf("firstFFT vrank-geq1 vl, ivs, ovs, m: %td %td %td %td\n", vl, ivs, ovs, m);
          //printf("diff ri ro: %td\n", ri - ro);
          //fflush(stdout);

          checksum1 = (R *) malloc(radix*2*sizeof(R));
          checksum2 = (R *) malloc(radix*2*sizeof(R));

          rA1 = (R *) malloc(m*2*sizeof(R));

          R * rA0;

           {
                int res = m % 3;
                register R c1 = 0.866025403784438818632906986749731004238128662;
                register R numeratorIm;
                if(res == 1) 
                {
                     numeratorIm = - c1;
                     rA1[0] = 1, rA1[1] = 0;
                }
                else 
                {
                     numeratorIm = c1;
                     rA1[0] = 0.5, rA1[1] = c1;  
                }
                rA0 = rA1;
                rA0 += 2;
                 for(int i=1; i<m; i++) // dmr
                 {   
                     R wi[2];
                     real_cexp(i, m, wi);

                     register R temp0, temp1, res0, res1, denom;
                     register R w0, w1;
                     register R dmr0, dmr1;
                     w0 = wi[0], w1 = wi[1];
                     // rA[m]
                     temp0 = 1 + 0.5 * w0 - c1 * w1;
                     dmr0 = 1 + 0.5 * w0 - c1 * w1;
                     
                     temp1 = 0.5 * w1 + c1 * w0;
                     dmr1 = 0.5 * w1 + c1 * w0;

                     if((temp0!=dmr0)||(temp1!=dmr1)) printf("rA error first part! temp0 temp1\n");
                     // if(i==100)
                     //      printf("temp: %f %f\n", temp0, temp1);

                     res0 = 1.5 * temp0 - numeratorIm * temp1;
                     dmr0 = 1.5 * temp0 - numeratorIm * temp1;
                      res1 = 1.5 * temp1 + numeratorIm * temp0;
                      dmr1 = 1.5 * temp1 + numeratorIm * temp0;

                     if((res0!=dmr0)||(res1!=dmr1)) printf("rA error first part! res0 res1\n");

                     denom = temp0 * temp0 + temp1 * temp1;
                     dmr0 = temp0 * temp0 + temp1 * temp1;

                     if(denom!=dmr0) printf("rA error first part! denom\n");
                     
                     w0 = res0 / denom;
                     dmr0 = res0 / denom;

                     w1 = res1 / denom;
                     dmr1 = res1 / denom;
                     if((w0!=dmr0)||(w1!=dmr1)) printf("rA error first part! res0 res1:\n");                   

                     rA0[0] = w0;
                     rA0[1] = w1;
                     sumrA0 += w0;
                     sumrA1 += w1;

                     rA0 += 2;
                 }
           }
            //printf("rA calculation finished\n");fflush(stdout);
          int coeffSize = radix>m? radix:m;
          simpleCoeff = (R *) malloc(radix*2*sizeof(R));
          for(int i=0; i<radix; i++)
            simpleCoeff[i] = 1.0/(i+1);
          
          coeff = (R *) malloc( m*2*sizeof(R));

          R * cof;
          cof = coeff;
          R * posrA;
          posrA = rA1;
          for(int i=0; i<m; i++)
          {
            cof[0] = posrA[0] / (i+1);
            cof[1] = posrA[1] / (i+1);
            cof += 2, posrA += 2;
          }

          outChecksum1 = (R *) malloc(vl*2*sizeof(R)); // fft_1 checksum
          // outChecksum2 = (R *) malloc(m*2*sizeof(R));
          for(int i=0; i<radix*2; i++)
            checksum1[i] = 0;
          for(int i=0; i<radix*2; i++)
            checksum2[i] = 0;
            // checkpoint
            R * posR; 
            R * posI;
            R * pos1;
            R * pos2;
            posR = ri, posI = ii;// pos1 = checksum1, pos2 = checksum2;
            // R * posrA;
            posrA = rA1;
            
            // R * cof;
            cof = coeff;
            R temp0, temp1;
            for(int i=0; i<m; i++)
            {
                R c0 = cof[0];
                R c1 = cof[1];
                R rAc0 = posrA[0];
                R rAc1 = posrA[1];
                pos1 = checksum1, pos2 = checksum2;
                for(int j=0; j<radix; j++)
                {
                  temp0 = posR[0], temp1 = posI[0];
                  pos1[0] += temp0 * rAc0 - temp1 * rAc1;
                  pos1[1] += temp0 * rAc1 + temp1 * rAc0;
                  pos2[0] += c0 * temp0;
                  pos2[1] += c1 * temp1;

                  posR += 2, posI += 2;
                  pos1 += 2, pos2 += 2; 
                }   
                cof += 2;
                posrA += 2;
            }

      }
       if(vl==radix)
       {

         // insert memory error~~~
         //ri[456345] += 20000;
          // ri[20] += 40000;
        //printf("vrank-geq1 start\n");fflush(stdout);
             R * cof0;
             cof0 = simpleCoeff;
            for (i = 0; i < vl; ++i) {

                    cldapply(ego->cld,
                             ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs); 

                }
                // printf("firstFFT %td ffts done\n", vl);

            int outSumSize = vl/2; //2*(vl/4); // vl/4, 4 fft as a group
            R * outSum1 = (R *) malloc(outSumSize *sizeof(R));
            R * outSum2 = (R *) malloc(outSumSize *sizeof(R));
            R * outSum3 = (R *) malloc(outSumSize *sizeof(R));
            for(int i=0; i<outSumSize; i++)
              outSum1[i] = 0;
            for(int i=0; i<outSumSize; i++)
              outSum2[i] = 0;
            for(int i=0; i<outSumSize; i++)
              outSum3[i] = 0;

                R * posR;
                // R * posI;
                // posI = io;
                R * posos1;
                R * posos2;
                R * posos3;
                // printf("fft_1 checking\n");
                // only for vl is multiple of 4
                //test
                posR = ro;

                int i;
                for(i=0; i<m-3; i+=3)
                {
                  posos1 = outSum1;
                  posos2 = outSum2;
                  posos3 = outSum3;
                  for(int j=0; j<vl/4; j++)
                  {
                    posos1[0] += posR[0] + posR[2] + posR[4] + posR[6];
                    posos1[1] += posR[1] + posR[3] + posR[5] + posR[7];
                    posos1 += 2, posR += 8;
                  }
                  for(int j=0; j<vl/4; j++)
                  {
                    posos2[0] += posR[0] + posR[2] + posR[4] + posR[6];
                    posos2[1] += posR[1] + posR[3] + posR[5] + posR[7];
                    posos2 += 2, posR += 8;
                  }
                  for(int j=0; j<vl/4; j++)
                  {
                    posos3[0] += posR[0] + posR[2] + posR[4] + posR[6];
                    posos3[1] += posR[1] + posR[3] + posR[5] + posR[7];
                    posos3 += 2, posR += 8;
                  }
                }
                if(i+1 < m)
                {
                  posos1 = outSum1;
                  posos2 = outSum2;
                  for(int j=0; j<vl/4; j++)
                  {
                    posos1[0] += posR[0] + posR[2] + posR[4] + posR[6];
                    posos1[1] += posR[1] + posR[3] + posR[5] + posR[7];
                    posos1 += 2, posR += 8;
                  }
                  for(int j=0; j<vl/4; j++)
                  {
                    posos2[0] += posR[0] + posR[2] + posR[4] + posR[6];
                    posos2[1] += posR[1] + posR[3] + posR[5] + posR[7];
                    posos2 += 2, posR += 8;
                  }
                }
                else
                {
                  posos1 = outSum1;
                  for(int j=0; j<vl/4; j++)
                  {
                    posos1[0] += posR[0] + posR[2] + posR[4] + posR[6];
                    posos1[1] += posR[1] + posR[3] + posR[5] + posR[7];
                    posos1 += 2, posR += 8;
                  }
                }
                // printf("calculation done\n");

                R diffReal;
                R diffIm;
                R r1 = 0.866025403784438818632906986749731004238128662;
               // diffReal = checksum1[2*i] -o00 + 0.5*o10 + r1*o11 + 0.5*o20 - r1*o21;
               // diffIm = checksum1[2*i+1] -o01 + 0.5*o11 - r1*o10 + 0.5*o21 + r1*o20;
                R o00, o10, o20, o01, o11, o21;
                bool error;
                for(int i=0; i<vl/4; i++)
                {
                  o00 = outSum1[2*i], o01 = outSum1[2*i+1];
                  o10 = outSum2[2*i], o11 = outSum2[2*i+1];
                  o20 = outSum3[2*i], o21 = outSum3[2*i+1];
                  
                  diffReal = checksum1[8*i] + checksum1[8*i+2] + checksum1[8*i+4] + checksum1[8*i+6]
                              - o00 + 0.5*o10 + r1*o11 + 0.5*o20 - r1*o21;
                  diffIm = checksum1[8*i+1] + checksum1[8*i+3] + checksum1[8*i+5] + checksum1[8*i+7]
                              - o01 + 0.5*o11 - r1*o10 + 0.5*o21 + r1*o20;

                  error = (diffReal>delta || diffReal<-delta || diffIm>delta || diffIm<-delta);

                  if(error)
                  {
                    printf("%td~%td error occurs: %f %f\n", 4*i, 4*i+3, diffReal, diffIm); //exit(0);
                    //check memory
                    R * in1;
                    R * in2;
                    R * cof;
                    // 4 in a group
                    in1 = ri + 4*i * ivs, in2 = ii + 4*i * ivs;
                    cof = coeff;
                    R cks1[4] = {0}; // real part
                    R cks2[4] = {0}; // imagine part
                    int step = 2 * vl;

                    for(int j=0; j<m; j++)
                    {
                        cks1[0] += cof[0] * in1[0];
                        cks2[0] += cof[1] * in2[0];
                        cks1[1] += cof[0] * in1[2];
                        cks2[1] += cof[1] * in2[2];
                        cks1[2] += cof[0] * in1[4];
                        cks2[2] += cof[1] * in2[4];
                        cks1[3] += cof[0] * in1[6];
                        cks2[3] += cof[1] * in2[6];
                        
                        in1 += step, in2 += step;
                        cof += 2;
                    }
                    
                    R diffReal2, diffIm2;
                    for(int j=4*i; j<4*i+4; j++)
                    {
                      int offset = j - 4*i;
                      diffReal2 = checksum2[2*j] - cks1[offset];
                      diffIm2 = checksum2[2*j+1] - cks2[offset];
                      // printf("diff2 : %f %f\n", diffReal2, diffIm2);
                      if((diffReal2 < 0.000001) && (diffReal2 > -0.000001) && (diffIm2 < 0.000001) && (diffIm2 > -0.000001))  
                      {
                        // printf("computational error!\n");
                        // exit(0);
                        continue;
                      }
                      printf("memory error!\n");
                      if((diffReal2 < 0.000001) && (diffReal2 > -0.000001))
                      {
                          printf("imaginary part error!");
                          int index =(int) (-diffReal / diffIm2 - 0.5); // -1 for index
                          int pos = index * vl * 2;// + 2 * offset;
                          printf("memory error ocurrs imaginary part, i, offset~ pos -- val: %d, %d~ %d -- %f\n", i, j, pos, (ii + j*ivs)[pos]);
                          (ii + j*ivs)[pos] -= diffReal / rA1[2*index+1]; 
                          printf("index %d diff: %f\n", index, diffReal / rA1[2*index+1]);
                      }
                      else if((diffIm2 < 0.000001) && (diffIm2 > -0.000001))
                      {
                          printf("real part error!");
                          int index =(int) (diffReal / diffReal2 - 0.5); // -1 for index
                          int pos = index * vl * 2;// + 2 * offset; // real part
                          printf("memory error ocurrs real part, i, offset~ pos -- val: %d, %d~ %d -- %f\n", i, j, pos, (ri + j*ivs)[pos]);
                          (ri + j*ivs)[pos] -= -diffReal / rA1[2*index]; 
                          printf("index %d diff: %f\n", index, -diffReal / rA1[2*index]);
                      }
                      else
                      {
                          printf("multiple memory errors, restart is needed.\n");
                          exit(1);
                      }
                      // exit(0);

                    }// end for
                    //recalc here, may add fault tolerance too......
                    for (int j = 4*i; j < 4*i+4; ++j) {
                          cldapply(ego->cld,
                                   ri + j * ivs, ii + j * ivs, ro + j * ovs, io + j * ovs);
                     }

                  }// end if error
                }// end for
                
                free(checksum1);
                free(checksum2);
                free(outChecksum1);
                // free(outChecksum2);
                free(rA1);
                free(coeff);

                // insert memory error~~~
                // (ro + 10*ovs)[0] += 10000;
       }
       else
          {
              // printf("vl ivs ovs: %td %td %td\n", vl, ivs, ovs);
              // printf("vl: %d\n", vl);
               for (i = 0; i < vl; ++i) {
                    cldapply(ego->cld,
                             ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);
               }

          }    
    } // end if firstFFT
    else if(secondFFT)
    {

     int m;
     // R sumrA0 = 0, sumrA1 = 0;

     if(FFTstart == true)
     {
        // printf("secondFFT vrank-geq1 vl, ivs, ovs: %td %td %td\nro ri diff: %td\n", vl, ivs, ovs, ri - ro);

        FFTstart = false;
        radix = vl;
        m = myRadix/radix;
        delta = 0.001;
        outChecksum1 = (R *) malloc(vl*2*sizeof(R));
        outChecksum2 = (R *) malloc(vl*2*sizeof(R));

        DMR = (vl!=m);

    }
     if(vl==radix)
     {

       // insert memory error~~~
        //ri[456345] += 20000;
       // ri[20] += 40000;
      if(DMR)
      {
           R * cof;

           R * inputBuffer2;
           inputBuffer2 = (R *) malloc(2*m*sizeof(R));
           ratio = vl / m;
          for (i = 0; i < vl; ++i) {
            // calc ipc
            cof = simpleCoeff + (i%ratio)*m;
            // printf("%d-th in vrank-geq1 secondFFT\n", i);
            bool recalc = true;

            while(recalc)
            {          
                // memRecalc = 0;
                int cn = m;
                   recalc = false;

                  memcpy(inputBuffer2, ri+i*ivs, 2*m*sizeof(R));
                  // cldapply(ego->cld,
                  //          ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);
                  // printf("calculation start \n");

                  cldapply(ego->cld,
                           ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);

                  // printf("current fft end\n");

                  {
                      R or00, or01, or10, or11, or20, or21;
                      or00 = 0, or01 = 0, or10 = 0, or11 = 0, or20 = 0, or21 = 0; 
                      R* ro0;
                      R* io0;
                      ro0 = ro + i*ovs, io0 = io + i*ovs;

                    // intermediate output checksum~~~ calculation
                     // if(!inject && i==24){
                     //       printf("injected!");
                     //       ro0[0]+=10000;
                     //       inject =true;
                     //   }

                      int j;

                      for(j=0; j<cn - 3; j+=3)
                      {
                         or00 += ro0[0], or01 += io0[0];
                         or10 += ro0[2], or11 += io0[2];
                         or20 += ro0[4], or21 += io0[4];
                         ro0 += 6, io0 += 6;  
                      }
                     if((j+1) < cn )
                     {
                        or00 += ro0[0], or01 += io0[0];
                        or10 += ro0[2], or11 += io0[2];}
                     else
                     {
                       or00 += ro0[0], or01 += io0[0];
                     }                      

                     R r1 = 0.866025403784438818632906986749731004238128662;
                     R diffReal, diffIm;
                     // printf("checksum %d: %f %f\n", i, checksum1[2*i], checksum1[2*i+1]);
                     // printf("output: %f %f\n", -or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21, -or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20);
                     int checkIndex = m*(i%ratio) + i/ratio;
                     diffReal = checksum1[2*checkIndex] -or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21;
                     diffIm = checksum1[2*checkIndex+1] -or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20; 
                     recalc = (diffReal>delta || diffReal<-delta || diffIm>delta || diffIm<-delta);

                     // printf("checkIndex: %d\nrecalc: %d\n", checkIndex, recalc);

                     if(recalc) 
                     { 
                        printf("%d-th diff: %f %f\n", i, diffReal, diffIm);//exit(0);
                        fflush(stdout);

                        {
                            //recalc 2 times, correct memory here
                            // printf("memory error! ivs: %d\tovs: %d\n", ivs, ovs);
                            R * in1;
                            R * in2;
                            R * cof;
                            in1 = inputBuffer2, in2 = inputBuffer2+1;
                            cof = coeff;
                            R cks1 = 0, cks2 = 0;
                            // int step = 2 * vl;

                            for(int j=0; j<m; j++)
                            {
                                cks1 += cof[0] * in1[0];
                                cks2 += cof[1] * in2[0];
                                in1 += 2, in2 += 2;
                                cof += 2;
                            }
                            // printf("checksum2: %f %f\n", checksum2[2*i], checksum2[2*i+1]);
                            // printf("checksum1: %f %f\n", checksum1[2*i], checksum1[2*i+1]);
                            // printf("checksum2: %f %f\n", checksum2[2*i], checksum2[2*i+1]);
                            // printf("rcks1, rcks2: %f %f\n", rcks1, rcks2);
                            // printf("cks1, cks2: %f %f\n", cks1, cks2);
                            R diffReal2, diffIm2;

                            checkIndex = m*(i%ratio) + i/ratio;

                            diffReal2 = checksum2[2*checkIndex] - cks1;
                            diffIm2 = checksum2[2*checkIndex+1] - cks2;

                            // printf("diff2 : %f %f\n", diffReal2, diffIm2);
                            
                            if((diffReal2 < 0.000001) && (diffReal2 > -0.000001) && (diffIm2 < 0.000001) && (diffIm2 > -0.000001)) 
                            {
                                printf("computational error!\n");
                                memcpy(ri+i*ivs, inputBuffer2, 2*m*sizeof(R));
                                continue;
                            }
                            printf("memory error!\n");
                            if((diffReal2 < 0.000001) && (diffReal2 > -0.000001))
                            {
                                printf("imaginary part error!");
                                int index =(int) (-diffReal / diffIm2 - 0.5); // -1 for index
                                int pos = index * 2;
                                printf("memory error ocurrs imaginary part, i~ pos -- val: %d~ %d -- %f\n", i, pos, (inputBuffer2+1)[pos]);
                                (inputBuffer2+1)[pos] -= diffReal / rA1[2*index+1]; 
                                printf("index %d diff: %f\n", index, diffReal / rA1[2*index+1]);
                            }
                            else if((diffIm2 < 0.000001) && (diffIm2 > -0.000001))
                            {
                                printf("real part error!");
                                int index =(int) (diffReal / diffReal2 - 0.5); // -1 for index
                                int pos = index * 2; // real part
                                printf("memory error ocurrs real part, i~ pos -- val: %d~ %d -- %f\n", i, pos, inputBuffer2[pos]);
                                inputBuffer2[pos] -= -diffReal / rA1[2*index]; 
                                printf("index %d diff: %f\n", index, -diffReal / rA1[2*index]);
                            }
                            else
                            {
                                printf("multiplie memory error, restart is needed.\n");
                                exit(1);
                            }
                            memcpy(ri+i*ivs, inputBuffer2, 2*m*sizeof(R));
                            continue;
                        }

                     }//end if recalc
                     // printf("verification done\n");

                    ro0 = ro + i*ovs, io0 = io + i*ovs;
  
                    R outSumReal = 0, outSumIm = 0;
                    R outSumReal2 = 0, outSumIm2 = 0;
                    R temp1, temp2, tempc;
                     for(int j=0; j<m; j++)
                     {
                        temp1 = ro0[0], temp2 = io0[0], tempc = cof[0];
                        outSumReal += temp1, outSumIm += temp2;
                        outSumReal2 += tempc * temp1, outSumIm2 += tempc * temp2;
                        // if((i==10 || i==11)) printf("temp1, tempc: %f %f\n", temp1, tempc);
                        ro0 += 2, io0 += 2, cof ++;
                     }
                     // printf("out %d: %f %f %f %f\n", i, outSumReal, outSumIm, outSumReal2, outSumIm2);
                     outChecksum1[2*i] = outSumReal, outChecksum1[2*i+1] = outSumIm;
                     outChecksum2[2*i] = outSumReal2, outChecksum2[2*i+1] = outSumIm2;

                  }
        
                }//end while 


              }//end for
              // printf("%td ffts done\n", vl);
              DMR = true;
              dmrInputBuffer = (R *) malloc(2*vl*sizeof(R));
              dmrOutChecksum1 = (R *) malloc(2*vl*sizeof(R));
              dmrOutChecksum2 = (R *) malloc(2*vl*sizeof(R));
              for(int i=0; i<4*m; i++)
                dmrOutChecksum1[i] = 0;
              for(int i=0; i<4*m; i++)
                dmrOutChecksum2[i] = 0;
              

              free(checksum1);
              free(checksum2);
              free(coeff);

             // printf("vrank-geq1 dmr done. vl: %td\n", vl);
              // insert memory error~~~
              // (ro + 10*ovs)[0] += 10000;
              // ro[3464356] += 30000;
              // io[437458] += -5000;

              // insert memory error~~~
              // (ro + 10*ovs)[0] += 10000;
           }// end if dmr
         else
         {
        dmrOutChecksum1 = (R *) malloc(vl*2*sizeof(R));
        dmrOutChecksum2 = (R *) malloc(vl*2*sizeof(R));
        for(int i=0; i<2*vl; i++)
        {
            dmrOutChecksum1[i] = 0;
            dmrOutChecksum2[i] = 0;
        }
           R * cof0;
           cof0 = simpleCoeff;
           R * inputBuffer2;
           inputBuffer2 = (R *) malloc(2*m*sizeof(R));

          for (i = 0; i < vl; ++i) {
            // calc ipc
            // printf("%d-th in vrank-geq1\n", i);
            bool recalc = true;

            while(recalc)
            {          
                // memRecalc = 0;
                int cn = m;
                   recalc = false;

                  memcpy(inputBuffer2, ri+i*ivs, 2*m*sizeof(R));
                  // cldapply(ego->cld,
                  //          ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);
                                       // printf("!!!1\n");      

                  cldapply(ego->cld,
                           ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);

                  {
                      R or00, or01, or10, or11, or20, or21;
                      or00 = 0, or01 = 0, or10 = 0, or11 = 0, or20 = 0, or21 = 0; 
                      R* ro0;
                      R* io0;
                      ro0 = ro + i*ovs, io0 = io + i*ovs;

                    // intermediate output checksum~~~ calculation
                    // if(!inject && i==24){
                    //       printf("injected!");
                    //       ro0[0]+=10000;
                    //       inject =true;
                    //   }

                      int j;

                      for(j=0; j<cn - 3; j+=3)
                      {
                         or00 += ro0[0], or01 += io0[0];
                         or10 += ro0[2], or11 += io0[2];
                         or20 += ro0[4], or21 += io0[4];
                         ro0 += 6, io0 += 6;  
                      }
                     if((j+1) < cn )
                     {
                        or00 += ro0[0], or01 += io0[0];
                        or10 += ro0[2], or11 += io0[2];}
                     else
                     {
                       or00 += ro0[0], or01 += io0[0];
                     }                

                     // printf("!!!2\n");      

                     R r1 = 0.866025403784438818632906986749731004238128662;
                     R diffReal, diffIm;
                     // printf("checksum %d: %f %f\n", i, checksum1[2*i], checksum1[2*i+1]);
                     // printf("output: %f %f\n", -or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21, -or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20);
                     diffReal = checksum1[2*i] -or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21;
                     diffIm = checksum1[2*i+1] -or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20; 
                     recalc = (diffReal>delta || diffReal<-delta || diffIm>delta || diffIm<-delta);
                     if(recalc) 
                     { 
                        printf("%d-th diff: %f %f\n", i, diffReal, diffIm);//exit(0);

                        {
                            //recalc 2 times, correct memory here
                            printf("memory error! ivs: %d\tovs: %d\n", ivs, ovs);
                            R * in1;
                            R * in2;
                            R * cof;
                            in1 = inputBuffer2, in2 = inputBuffer2+1;
                            cof = coeff;
                            R cks1 = 0, cks2 = 0;
                            // int step = 2 * vl;
                            printf("second checksum calculation\n");fflush(stdout);

                            for(int j=0; j<m; j++)
                            {
                                cks1 += cof[0] * in1[0];
                                cks2 += cof[1] * in2[0];
                                in1 += 2, in2 += 2;
                                cof += 2;
                            }
                            // printf("checksum2: %f %f\n", checksum2[2*i], checksum2[2*i+1]);
                            // printf("checksum1: %f %f\n", checksum1[2*i], checksum1[2*i+1]);
                            // printf("checksum2: %f %f\n", checksum2[2*i], checksum2[2*i+1]);
                            // printf("rcks1, rcks2: %f %f\n", rcks1, rcks2);
                            // printf("cks1, cks2: %f %f\n", cks1, cks2);
                            R diffReal2, diffIm2;
                            printf("second checksum calculation done\n");fflush(stdout);

                            diffReal2 = checksum2[2*i] - cks1;
                            diffIm2 = checksum2[2*i+1] - cks2;

                            // printf("diff2 : %f %f\n", diffReal2, diffIm2);
                            
                            if((diffReal2 < 0.000001) && (diffReal2 > -0.000001) && (diffIm2 < 0.000001) && (diffIm2 > -0.000001)) 
                            {
                                printf("computational error!\n");
                                memcpy(ri+i*ivs, inputBuffer2, 2*m*sizeof(R));
                                continue;
                            }
                            printf("memory error!\n");
                            if((diffReal2 < 0.000001) && (diffReal2 > -0.000001))
                            {
                                printf("imaginary part error!");
                                int index =(int) (-diffReal / diffIm2 - 0.5); // -1 for index
                                int pos = index * 2;
                                printf("memory error ocurrs imaginary part, i~ pos -- val: %d~ %d -- %f\n", i, pos, (inputBuffer2+1)[pos]);
                                (inputBuffer2+1)[pos] -= diffReal / rA1[2*index+1]; 
                                printf("index %d diff: %f\n", index, diffReal / rA1[2*index+1]);
                            }
                            else if((diffIm2 < 0.000001) && (diffIm2 > -0.000001))
                            {
                                printf("real part error!");
                                int index =(int) (diffReal / diffReal2 - 0.5); // -1 for index
                                int pos = index * 2; // real part
                                printf("memory error ocurrs real part, i~ pos -- val: %d~ %d -- %f\n", i, pos, inputBuffer2[pos]);
                                inputBuffer2[pos] -= -diffReal / rA1[2*index]; 
                                printf("index %d diff: %f\n", index, -diffReal / rA1[2*index]);
                            }
                            else
                            {
                                printf("multiplie memory error, restart is needed.\n");
                                exit(1);
                            }
                            memcpy(ri+i*ivs, inputBuffer2, 2*m*sizeof(R));
                            continue;
                        }

                     }
                     // printf("!!!3\n");      

                      R temp0, temp1, tempc;
                      tempc = cof0[0];
                      cof0 ++;
                      ro0 = ro + i*ovs, io0 = io + i*ovs;

                      R * pos1;
                      pos1 = dmrOutChecksum1;
                      R * pos2;
                      pos2 = dmrOutChecksum2;

                      for(j=0; j<m; j++)
                      {
                         temp0 = ro0[0], temp1 = io0[0];
                         pos1[0] += temp0, pos2[0] += temp0 * tempc;
                         pos1[1] += temp1, pos2[1] += temp1 * tempc;
                         ro0 += 2, io0 += 2;  
                         pos1 += 2, pos2 += 2;
                      }
                    
                                           // printf("!!!2\4");      

                  }
        
                }//end while 


              }//end for
              // printf("%td ffts done\n", vl);

              free(inputBuffer2);
              free(checksum1);
              free(checksum2);
              free(coeff);

             // printf("vrank-geq1 no dmr done. vl: %td\n", vl);
         }
     }
     else
        {
            // printf("vl ivs ovs: %td %td %td\n", vl, ivs, ovs);
            // printf("vl: %d\n", vl);
             for (i = 0; i < vl; ++i) {
                  cldapply(ego->cld,
                           ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);
             }

        } 
      }// end else if secondFFT
      else
      {
               for (i = 0; i < vl; ++i) {
            cldapply(ego->cld,
                     ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);
             }
      }

}

static void awake(plan *ego_, enum wakefulness wakefulness)
{
     P *ego = (P *) ego_;
     X(plan_awake)(ego->cld, wakefulness);
}

static void destroy(plan *ego_)
{
     P *ego = (P *) ego_;
     X(plan_destroy_internal)(ego->cld);
}

static void print(const plan *ego_, printer *p)
{
     const P *ego = (const P *) ego_;
     const S *s = ego->solver;
     p->print(p, "(dft-vrank>=1-x%D/%d%(%p%))",
 	      ego->vl, s->vecloop_dim, ego->cld);
}

static int pickdim(const S *ego, const tensor *vecsz, int oop, int *dp)
{
     return X(pickdim)(ego->vecloop_dim, ego->buddies, ego->nbuddies,
		       vecsz, oop, dp);
}

static int applicable0(const solver *ego_, const problem *p_, int *dp)
{
     const S *ego = (const S *) ego_;
     const problem_dft *p = (const problem_dft *) p_;

     return (1
	     && FINITE_RNK(p->vecsz->rnk)
	     && p->vecsz->rnk > 0

	     /* do not bother looping over rank-0 problems,
		since they are handled via rdft */
	     && p->sz->rnk > 0

	     && pickdim(ego, p->vecsz, p->ri != p->ro, dp)
	  );
}

static int applicable(const solver *ego_, const problem *p_, 
		      const planner *plnr, int *dp)
{
     const S *ego = (const S *)ego_;
     const problem_dft *p;

     if (!applicable0(ego_, p_, dp)) return 0;

     /* fftw2 behavior */
     if (NO_VRANK_SPLITSP(plnr) && (ego->vecloop_dim != ego->buddies[0]))
	  return 0;

     p = (const problem_dft *) p_;

     if (NO_UGLYP(plnr)) {
	  /* Heuristic: if the transform is multi-dimensional, and the
	     vector stride is less than the transform size, then we
	     probably want to use a rank>=2 plan first in order to combine
	     this vector with the transform-dimension vectors. */
	  {
	       iodim *d = p->vecsz->dims + *dp;
	       if (1
		   && p->sz->rnk > 1 
		   && X(imin)(X(iabs)(d->is), X(iabs)(d->os)) 
		   < X(tensor_max_index)(p->sz)
		    )
		    return 0;
	  }

	  if (NO_NONTHREADEDP(plnr)) return 0; /* prefer threaded version */
     }

     return 1;
}

static plan *mkplan(const solver *ego_, const problem *p_, planner *plnr)
{
     const S *ego = (const S *) ego_;
     const problem_dft *p;
     P *pln;
     plan *cld;
     int vdim;
     iodim *d;

     static const plan_adt padt = {
	  X(dft_solve), awake, print, destroy
     };

     if (!applicable(ego_, p_, plnr, &vdim))
          return (plan *) 0;
     p = (const problem_dft *) p_;

     d = p->vecsz->dims + vdim;

     A(d->n > 1);
     cld = X(mkplan_d)(plnr,
		       X(mkproblem_dft_d)(
			    X(tensor_copy)(p->sz),
			    X(tensor_copy_except)(p->vecsz, vdim),
			    TAINT(p->ri, d->is), TAINT(p->ii, d->is),
			    TAINT(p->ro, d->os), TAINT(p->io, d->os)));
     if (!cld) return (plan *) 0;

     pln = MKPLAN_DFT(P, &padt, apply);

     pln->cld = cld;
     pln->vl = d->n;
     pln->ivs = d->is;
     pln->ovs = d->os;

     pln->solver = ego;
     X(ops_zero)(&pln->super.super.ops);
     pln->super.super.ops.other = 3.14159; /* magic to prefer codelet loops */
     X(ops_madd2)(pln->vl, &cld->ops, &pln->super.super.ops);

     if (p->sz->rnk != 1 || (p->sz->dims[0].n > 64))
	  pln->super.super.pcost = pln->vl * cld->pcost;

     return &(pln->super.super);
}

static solver *mksolver(int vecloop_dim, const int *buddies, size_t nbuddies)
{
     static const solver_adt sadt = { PROBLEM_DFT, mkplan, 0 };
     S *slv = MKSOLVER(S, &sadt);
     slv->vecloop_dim = vecloop_dim;
     slv->buddies = buddies;
     slv->nbuddies = nbuddies;
     return &(slv->super);
}

void X(dft_vrank_geq1_register)(planner *p)
{
     /* FIXME: Should we try other vecloop_dim values? */
     static const int buddies[] = { 1, -1 };
     size_t i;
     
     for (i = 0; i < NELEM(buddies); ++i)
          REGISTER_SOLVER(p, mksolver(buddies[i], buddies, NELEM(buddies)));
}
