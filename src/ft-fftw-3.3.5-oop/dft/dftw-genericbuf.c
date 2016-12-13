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

/* express a twiddle problem in terms of dft + multiplication by
   twiddle factors */

#include "ct.h"
#include <math.h>
#include <stdio.h>
#include <stdbool.h>
#include <time.h>

#include <string.h>
typedef struct {
     ct_solver super;
     INT batchsz;
} S;

typedef struct {
     plan_dftw super;

     INT r, rs, m, ms, v, vs, mb, me;
     INT batchsz;
     plan *cld;

     triggen *t;
     const S *slv;
} P;

R * rA2;
int cn;
R ipcReal_2;
R ipcIm_2;

extern R * dmrOutChecksum1; // sum(a_i), intermediate checksums
extern R * dmrOutChecksum2; // sum(1/i a_i), intermediate checksums
extern R * outChecksum1; // sum(a_i), intermediate checksums
extern R * outChecksum2; // sum(1/i a_i), intermediate checksums
extern R * simpleCoeff;
R * coeff2;

R * outputChecksum1; // final output checksum
R * outputChecksum2; // final output checksum

int checkNum; // number of groups to be checked in a row
int count; // count for checksum number

// R * memoryChecksum00, * memoryChecksum01, * memoryChecksum10, * memoryChecksum11;
R * memoryChecksum1;
R * memoryChecksum2;
// R * smallCof;
R * buf2;

int size;
int * offset;

const R threshold = 0.01;

bool inject2 = false;
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


#define BATCHDIST(r) ((r) + 16)

/**************************************************************/
// static void bytwiddle(const P *ego, INT mb, INT me, R *buf, R *rio, R *iio)
// {
//      INT j, k;
//      INT r = ego->r, rs = ego->rs, ms = ego->ms;
//      triggen *t = ego->t;
//      for (j = 0; j < r; ++j) {
//     for (k = mb; k < me; ++k)
//          t->rotate(t, j * k,
//        rio[j * rs + k * ms],
//        iio[j * rs + k * ms],
//        &buf[j * 2 + 2 * BATCHDIST(r) * (k - mb) + 0]);
//      }
// }
static void bytwiddle(const P *ego, INT mb, INT me, R *buf, R *rio, R *iio)
{
     INT j, k;
     INT r = ego->r, rs = ego->rs, ms = ego->ms;
     triggen *t = ego->t;
     bool recalc = true;

     // R memoryChecksum00, memoryChecksum01, memoryChecksum10, memoryChecksum11;

     while(recalc)
     {
       R sumReal, sumIm;
       ipcReal_2 = 0, ipcIm_2 = 0;
       // R memoryChecksum[4] = {0};
       for( k = mb; k< me; k++)
       {
         int coffset = 2*(k - mb);
         memoryChecksum1[coffset] = - dmrOutChecksum1[2*k];
         memoryChecksum1[coffset+1] = - dmrOutChecksum1[2*k+1];
         memoryChecksum2[coffset] = - dmrOutChecksum2[2*k];
         memoryChecksum2[coffset+1] = - dmrOutChecksum2[2*k+1];        
       }

       R * rA0 = rA2;
       int index;
       R temp0, temp1;

       R * cof0;
       cof0 = simpleCoeff;
       for (j = 0; j < r; ++j) {
         sumReal = 0, sumIm = 0;
         
         // R * coff = cof;
         for (k = mb; k < me; ++k)
         {
              // index = j * 2 + 2 * BATCHDIST(r) * (k - mb) + 0;
              // t->rotate(t, j * k,
              //     rio[j * rs + k * ms],
              //     iio[j * rs + k * ms],
              //     &buf[index]);
              index = j * rs + k * ms;
              temp0 = rio[index];
              temp1 = iio[index];

              // memoryChecksum0 -= temp0, memoryChecksum1 -= temp1;

              int coffset = 2*(k-mb);
              memoryChecksum1[coffset] += temp0, memoryChecksum1[coffset+1] += temp1;
              memoryChecksum2[coffset] += temp0 * cof0[0], memoryChecksum2[coffset+1] += temp1 * cof0[0];
              // if(temp0 > 10000) printf("j, k, temp0, coff: %d %d %f %f\n", j, k, temp0, coff[0]);
              // memoryChecksum[0] += temp0, memoryChecksum[1] += temp1;
              // memoryChecksum[2] += temp0 * cof[0], memoryChecksum[3] += temp1 * cof[0];
              // memoryChecksum[2] += temp0 * coff[0], memoryChecksum[3] += temp1 * coff[0];
              // coff += r;
              index = j * 2 + 2 * BATCHDIST(r) * (k - mb) + 0;
              t->rotate(t, j * k,
                  temp0,
                  temp1,
                  &buf[index]);
              //
              sumReal += buf[index], sumIm += buf[index+1];

         }

         ipcReal_2 += rA0[0]*sumReal - rA0[1]*sumIm;
         ipcIm_2 += rA0[0]*sumIm + rA0[1]*sumReal;
         rA0 += 2;
         cof0 ++;
       }
       // printf("memory diff sec mb-me %d %d: %f %f\n", mb, me, memoryChecksum0, memoryChecksum1);
       // smallCof += me - mb;

       recalc = false;
       for(k=mb; k<me; ++k)
       {
         if (memoryChecksum1[2*(k-mb)] < -threshold || memoryChecksum1[2*(k-mb)] > threshold)        
         {
            recalc = true;
             printf("memoryChecksums: %f %f %f %f\n", memoryChecksum1[2*(k-mb)], memoryChecksum1[2*(k-mb)+1], memoryChecksum2[2*(k-mb)], memoryChecksum2[2*(k-mb)+1]);
             printf("real part, k: %td\n", k);
             exit(0);
            int index =(int) (memoryChecksum1[2*(k-mb)] / memoryChecksum2[2*(k-mb)] - 0.5); // -1 for index
            
            int pos = index * rs + k * ms;

            printf("dftw-genericbuf real part error, index %d real pos ~ val: %d ~ %f\n", index, pos, rio[pos]);

            rio[pos] -= memoryChecksum1[2*(k-mb)];

            // exit(0);
         }
         if (memoryChecksum1[2*(k-mb)+1] < -threshold || memoryChecksum1[2*(k-mb)+1] > threshold)
         {
            recalc = true;
           printf("memoryChecksums: %f %f %f %f\n", memoryChecksum1[2*(k-mb)], memoryChecksum1[2*(k-mb)+1], memoryChecksum2[2*(k-mb)], memoryChecksum2[2*(k-mb)+1]);
           printf("imaginary part, k: %td\n", k);
             exit(0);
            int index =(int) (memoryChecksum1[2*(k-mb)+1] / memoryChecksum2[2*(k-mb)+1] - 0.5); // -1 for index
            
            int pos = index * rs + k * ms;

            printf("dftw-genericbuf imaginary part error, index %d real pos ~ val: %d ~ %f\n", index, pos, rio[pos]);

            iio[pos] -= memoryChecksum1[2*(k-mb)+1];

            // exit(0);
         }
       // printf("memoryChecksums: %f %f %f %f\n", memoryChecksum1[2*(k-mb)], memoryChecksum1[2*(k-mb)+1], memoryChecksum2[2*(k-mb)], memoryChecksum2[2*(k-mb)+1]);

       }
       // printf("memoryChecksums: %f %f %f %f\n", memoryChecksum[0], memoryChecksum[1], memoryChecksum[2], memoryChecksum[3]);

      }
}

static int applicable0(const S *ego,
                 INT r, INT irs, INT ors,
                 INT m, INT v,
                 INT mcount)
{
     return (1
          && v == 1
          && irs == ors
          && mcount >= ego->batchsz
          && mcount % ego->batchsz == 0
          && r >= 64 
          && m >= r
       );
}

static int applicable(const S *ego,
                INT r, INT irs, INT ors,
                INT m, INT v,
                INT mcount,
                const planner *plnr)
{
     if (!applicable0(ego, r, irs, ors, m, v, mcount))
       return 0;
     if (NO_UGLYP(plnr) && m * r < 65536)
       return 0;

     return 1;
}
int bsz;
//clock_t start2, end2;
//double cTime2 = 0;
//clock_t start3, end3;
//double cTime3 = 0;

static void dobatch(const P *ego, INT mb, INT me, R *buf, R *rio, R *iio)
{
     plan_dft *cld;
     INT ms = ego->ms;

     // redo?

     // calc ipc
          
     //start3 = clock();
     bytwiddle(ego, mb, me, buf, rio, iio);
     //end3 = clock();

     //cTime3 += end3 - start3;
     R real_Bak, im_Bak;
      
      bool recalc = true;
     
     while(recalc)
     {
          recalc = false;
          real_Bak = ipcReal_2;
          im_Bak = ipcIm_2;

          cld = (plan_dft *) ego->cld;
          // cld->apply(ego->cld, buf, buf + 1, buf2, buf2 + 1);

          memcpy(buf2, buf, bsz);
          cld->apply(ego->cld, buf2, buf2 + 1, buf2, buf2 + 1);

          //start2 = clock();
          {
               // int * offset = (int *)malloc((me-mb)*sizeof(int)); // groups
               int currentOffset;
               INT j, k;
               for(k = mb; k<me; ++k) // offset of each group
               {
                    offset[k-mb] = 2 * BATCHDIST(cn) * (k - mb);
               }

              //  if(!inject2 && mb==44){
              //  printf("injected n2!\n");
              //  buf2[3]+=10000;
              //    recalc = true;
              // inject2 =true;
              //  }

               R or00, or01, or10, or11, or20, or21;
               or00 = 0, or01 = 0, or10 = 0, or11 = 0, or20 = 0, or21 = 0; 

              //  for (j = 0; j < cn-3; j+=3) {

              //    for (k = mb; k < me; ++k)
              //    {
              //          currentOffset = offset[k-mb] + 2*j;
              //          or00 += buf[currentOffset], or01 += buf[currentOffset+1];
              //          or10 += buf[currentOffset+2], or11 += buf[currentOffset+3];
              //          or20 += buf[currentOffset+4], or21 += buf[currentOffset+5];
              //    }
              //  }

              //  for(k=mb; k<me; k++)
              //  {
              //       currentOffset = offset[k-mb] + 2*j;
              //       or00 += buf[currentOffset], or01 += buf[currentOffset +1];
              //  }
              // if((j+1)<cn) 
              // {
              //       for(k=mb; k<me; k++)
              //       {
              //          currentOffset = offset[k-mb] + 2*j + 2;
              //          or10 += buf[currentOffset], or11 += buf[currentOffset+1];
              //       }
              //  }

               R tempc1, tempc2, tempc3;
               R temp0, temp1;
               R sum0 = 0;
               R sum1 = 0;

               R * cof;
               cof = coeff2;

               R * cofk;
               int dis = me - mb;
               int dis2 = dis*2;
               int dis3 = dis2 + dis;

               // printf("start calc~\n");
               for (j = 0; j < cn-3; j+=3) {

                 cofk = cof;
                 for (k = 0; k < dis; ++k)
                 {
                       currentOffset = offset[k] + 2*j;
                       // or00 += buf[currentOffset], or01 += buf[currentOffset+1];
                       // or10 += buf[currentOffset+2], or11 += buf[currentOffset+3];
                       // or20 += buf[currentOffset+4], or21 += buf[currentOffset+5];
                       temp0 = buf2[currentOffset], temp1 = buf2[currentOffset+1];
                       or00 += temp0, sum0 += temp0 * cofk[0];
                       or01 += temp1, sum1 += temp1 * cofk[0];
                       temp0 = buf2[currentOffset+2], temp1 = buf2[currentOffset+3];
                       or10 += temp0, sum0 += temp0 * cofk[dis];
                       or11 += temp1, sum1 += temp1 * cofk[dis];
                       temp0 = buf2[currentOffset+4], temp1 = buf2[currentOffset+5];
                       or20 += temp0, sum0 += temp0 * cofk[dis2];
                       or21 += temp1, sum1 += temp1 * cofk[dis2];

                       cofk ++;
                 }
                 cof += dis3;
               }
               // printf("residue\n");
               // tempc1 = 1.0/(j+1);
               cofk = cof;
              if((j+1)<cn) 
              {
                  // printf("residue is 2~\n");
                    for(k=0; k<dis; k++)
                    {
                       currentOffset = offset[k] + 2*j;
                       temp0 = buf2[currentOffset], temp1 = buf2[currentOffset+1];
                       or00 += temp0, sum0 += temp0 * cofk[0];
                       or01 += temp1, sum1 += temp1 * cofk[0];
                       temp0 = buf2[currentOffset+2], temp1 = buf2[currentOffset+3];
                       or10 += temp0, sum0 += temp0 * cofk[dis];
                       or11 += temp1, sum1 += temp1 * cofk[dis];

                       cofk ++;
                    }
               }
               else
               {
                 for(k=0; k<dis; k++)
                 {
                      currentOffset = offset[k] + 2*j;
                     temp0 = buf2[currentOffset], temp1 = buf2[currentOffset+1];
                     // printf("currentOffset?\n");
                     or00 += temp0, sum0 += temp0 * cofk[0];
                     or01 += temp1, sum1 += temp1 * cofk[0];
                     // printf("cofk?\n");
                     cofk ++;
                 }
               }
              //  for(k=mb; k<me; k++)
              //  {
              //       currentOffset = offset[k-mb] + 2*j;
              //       // or00 += buf[currentOffset], or01 += buf[currentOffset +1];
              //      temp0 = buf[currentOffset], temp1 = buf[currentOffset+1];
              //      or00 += temp0, sum0 += temp0 / tempc1;
              //      or01 += temp1, sum1 += temp1 / tempc1;
              //  }
              // if((j+1)<cn) 
              // {
              //     tempc2 = 1.0/(j+2);
              //       for(k=mb; k<me; k++)
              //       {
              //          currentOffset = offset[k-mb] + 2*j + 2;
              //          // or10 += buf[currentOffset], or11 += buf[currentOffset+1];
              //          temp0 = buf[currentOffset], temp1 = buf[currentOffset+1];
              //          or10 += temp0, sum0 += temp0 / tempc2;
              //          or11 += temp1, sum1 += temp1 / tempc2;
              //       }
              //  }
               // printf("assign\n");
              // outputChecksum1[count] = - or00 - or10 - or20;
              // outputChecksum2[count] = - sum0;
              // count ++;
              // outputChecksum1[count] = - or01 - or11 - or21;
              // outputChecksum2[count] = - sum1;
              // count ++; 
               
              R r1 = 0.866025403784438818632906986749731004238128662;
              // ipcReal_2 += -or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21;
              // ipcIm_2 += -or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20;
              real_Bak += -or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21;
              im_Bak += -or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20;
              // printf("%f %f %f %f %f %f\n", or00, or01, or10, or11, or20, or21);
              // recalc = (ipcReal_2>0.01 || ipcReal_2<-0.01 || ipcIm_2>0.01 || ipcIm_2<-0.01);
          		recalc = (real_Bak >0.01 || real_Bak<-0.01 || im_Bak>0.01 || im_Bak<-0.01);
              if(recalc)
          		{
          			printf("dftw-genericbuf diff: %d %d %f %f\n", mb, me, real_Bak, im_Bak);
                
                //exit(0);
                continue;
          			// exit(0);
          		}
              outputChecksum1[count] = - or00 - or10 - or20;
              outputChecksum2[count] = - sum0;
              count ++;
              outputChecksum1[count] = - or01 - or11 - or21;
              outputChecksum2[count] = - sum1;
              count ++;
          }
          // end2 = clock();
          // cTime2 += end2 - start2;
     }//end while

     X(cpy2d_pair_co)(buf2, buf2 + 1,
                rio + ms * mb, iio + ms * mb,
                me-mb, 2 * BATCHDIST(ego->r), ms,
                ego->r, 2, ego->rs);


}

// DIT, first solve r m-FFT, then m r-FFT
// static void dobatch(const P *ego, INT mb, INT me, R *buf, R *rio, R *iio)
// {
//      plan_dft *cld;
//      INT ms = ego->ms;

//      bytwiddle(ego, mb, me, buf, rio, iio);

//      cld = (plan_dft *) ego->cld;

//      memcpy(buf2, buf, bsz);

//      cld->apply(ego->cld, buf, buf + 1, buf2, buf2 + 1);
//      X(cpy2d_pair_co)(buf2, buf2 + 1,
//           rio + ms * mb, iio + ms * mb,
//           me-mb, 2 * BATCHDIST(ego->r), ms,
//           ego->r, 2, ego->rs);
// }
static void apply(const plan *ego_, R *rio, R *iio)
{
     const P *ego = (const P *) ego_;
     // printf("dftw-genericbuf~ mb, me, r: %td %td %td\n", ego->mb, ego->me, ego->r);
     cn = ego->r;

    free(outChecksum1);
    free(outChecksum2);
     // clock_t start, end;
     // double cTime;

     rA2 = (R *) malloc(cn*2*sizeof(R));

     R * rA0;
    {
         int res = cn % 3;
         R c1 = 0.866025403784438818632906986749731004238128662;
         R numeratorIm;
          if(res == 1) 
         {
              numeratorIm = - c1;
              rA2[0] = 1, rA2[1] = 0;
         }
         else 
         {
              numeratorIm = c1;
              rA2[0] = 0.5, rA2[1] = c1;  
         }
         rA0 = rA2;
         rA0 += 2;
          for(int i=1; i<cn; i++) // dmr
          {   
              R wi[2];
              real_cexp(i, cn, wi);

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
              // if(i==100)
                   // printf("rA0: %f %f\n", rA0[0], rA0[1]);

              rA0 += 2;
          }
    }

    bsz = sizeof(R) * 2 * BATCHDIST(ego->r) * ego->batchsz;

     R *buf = (R *) MALLOC(bsz,
                  BUFFERS);
     buf2 = (R *) MALLOC(bsz,
                  BUFFERS);

     INT m;

         // testing
   //  {
   //   R sum = 0;
   //   int stride = ego->rs;
   //   for(int i=0; i<cn; i++)
   //   {
   //     sum += rio[i*stride];
   //   }
   //   printf("FIRST ELEMENT: %f\n", rio[0]);
   //   printf("Stride, cn: %d %d\nFirst Sum: %f\nOutCKS: %f\n", stride, cn, sum, outChecksum1[0]);
   // }
    //testing

     checkNum = ego->batchsz;

     size = (ego->me - ego->mb) / ego->batchsz;
     outputChecksum1 = (R *) malloc(size*2*sizeof(R));
     outputChecksum2 = (R *) malloc(size*2*sizeof(R));
      // for(int i=0; i<size*2; i++)
      //   outputChecksum1[i] = 0;
      // for(int i=0; i<size*2; i++)
      //   outputChecksum2[i] = 0;
     count = 0;
     // memoryChecksum00 = (R *) malloc(checkNum*sizeof(R));
     // memoryChecksum01 = (R *) malloc(checkNum*sizeof(R));
     // memoryChecksum10 = (R *) malloc(checkNum*sizeof(R));
     // memoryChecksum11 = (R *) malloc(checkNum*sizeof(R));
     memoryChecksum1 = (R *) malloc(checkNum*2*sizeof(R));
     memoryChecksum2 = (R *) malloc(checkNum*2*sizeof(R));
     offset = (int *)malloc(checkNum*sizeof(int));

     int cSize = checkNum * cn; // coefficient size
     coeff2 = (R *) malloc(cSize*sizeof(R));
     for(int i=0; i<cSize; i++)
        coeff2[i] = 1.0/(i+1);
     // smallCof = coeff2;
     
      // insert memory error ~~~
      // rio[243522] += 20000;


    //start = clock();

     for (m = ego->mb; m < ego->me; m += ego->batchsz)
       dobatch(ego, m, m + ego->batchsz, buf, rio, iio);

     A(m == ego->me);
    //end = clock();
    //cTime = (double)(end - start)/CLOCKS_PER_SEC;
    //printf("second fft elapsed time: %f\n", cTime);
    //cTime = (double)(cTime3)/CLOCKS_PER_SEC;
    //printf("second start (inserted) time: %f\n", cTime);
    //cTime = (double)(cTime2)/CLOCKS_PER_SEC;
    //printf("second end (inserted) time: %f\n", cTime);

    //insert memory error  ~~~
    //rio[3425634] += 40000;


     // the last check
      R * posR; 
      R * posI;
      R * pos1;
      R * pos2;
      posR = rio, posI = iio;

      R * cof;
      cof = coeff2;
      R * cofk;

      // start = clock();
      // memory checksum calculation
      for(int i=0; i<cn; i++)
      {
          pos1 = outputChecksum1;
          // pos2 = outputChecksum2;
          for(int j=0; j<size; j++)
          {
            for(int k=0; k<checkNum; k++)
            {
              pos1[0] += posR[0];
              pos1[1] += posI[0];
              posR += 2, posI += 2;
            }
            pos1 += 2;//, pos2 += 2;  
          }
      }
      R delta = 0.01;
       int stepSize = 2*size*checkNum - 2*checkNum;
      for(int i=0; i<size; i++)
      {
          //printf("final checksum %d: %f %f\n", i, outputChecksum1[2*i], outputChecksum1[2*i+1]);
          if(outputChecksum1[2*i] > delta || outputChecksum1[2*i] < -delta)
          {
            posR = rio + i * 2 * checkNum;
            R cks0 = outputChecksum2[2*i];
            R * cof;
            cof = coeff2;
            for(int j=0; j<cn; j++)
            {
               for(int k=0; k<checkNum; k++)
               {
                    cks0 += cof[0] * posR[0];
                    cof ++, posR += 2;
               }
               posR += stepSize;
            }

            int index = (int)(outputChecksum1[2*i]/cks0 - 0.5);
            printf("real part error, i %d, index %d: %f %f\n", i, index, outputChecksum1[2*i], cks0);
            // exit(0);
            int pos = 2*((index / checkNum) * size * checkNum + checkNum * i + index % checkNum);
            printf("index %d pos %d: %f\n", index, pos, rio[pos]);
            rio[pos] -= outputChecksum1[2*i];
            
          }
          if(outputChecksum1[2*i+1] > delta || outputChecksum1[2*i+1] < -delta)
          {

            posI = iio + i * 2 * checkNum;
            R cks0 = outputChecksum2[2*i+1];
            R * cof;
            cof = coeff2;
            for(int j=0; j<cn; j++)
            {
               for(int k=0; k<checkNum; k++)
               {
                    cks0 += cof[0] * posI[0];
                    cof ++, posI += 2;
               }
               posI += stepSize;
            }               
            int index = (int)(outputChecksum1[2*i+1]/cks0 - 0.5);
            printf("imaginary part error, i %d: %f\n", i, outputChecksum1[2*i+1]);
            int pos = 2*((index / checkNum) * size * checkNum + checkNum * i + index % checkNum);
            printf("index %d pos %d: %f\n", index, pos, iio[pos]);
            iio[pos] -= outputChecksum1[2*i+1];            
          }
          // printf("last checksum, index %d: %f %f %f %f\n", i, outputChecksum1[2*i], outputChecksum1[2*i+1], outputChecksum2[2*i], outputChecksum2[2*i+1]);
  }
    // end = clock();
    // cTime = (double)(end - start)/CLOCKS_PER_SEC;
    // printf("last check elapsed time: %f\n", cTime);

    // free(smallCof);
    free(offset);
    free(memoryChecksum1);
    free(memoryChecksum2);
    free(dmrOutChecksum1);
    free(dmrOutChecksum2);
    free(outputChecksum1);
    free(outputChecksum2);
    free(rA2);
     X(ifree)(buf);
     X(ifree)(buf2);
}

static void awake(plan *ego_, enum wakefulness wakefulness)
{
     P *ego = (P *) ego_;
     X(plan_awake)(ego->cld, wakefulness);

     switch (wakefulness) {
      case SLEEPY:
           X(triggen_destroy)(ego->t); ego->t = 0;
           break;
      default:
           ego->t = X(mktriggen)(AWAKE_SQRTN_TABLE, ego->r * ego->m);
           break;
     }
}

static void destroy(plan *ego_)
{
     P *ego = (P *) ego_;
     X(plan_destroy_internal)(ego->cld);
}

static void print(const plan *ego_, printer *p)
{
     const P *ego = (const P *) ego_;
     p->print(p, "(dftw-genericbuf/%D-%D-%D%(%p%))",
           ego->batchsz, ego->r, ego->m, ego->cld);
}

static plan *mkcldw(const ct_solver *ego_,
              INT r, INT irs, INT ors,
              INT m, INT ms,
              INT v, INT ivs, INT ovs,
              INT mstart, INT mcount,
              R *rio, R *iio,
              planner *plnr)
{
     const S *ego = (const S *)ego_;
     P *pln;
     plan *cld = 0;
     R *buf;

     static const plan_adt padt = {
       0, awake, print, destroy
     };
     
     UNUSED(ivs); UNUSED(ovs); UNUSED(rio); UNUSED(iio);

     A(mstart >= 0 && mstart + mcount <= m);
     if (!applicable(ego, r, irs, ors, m, v, mcount, plnr))
          return (plan *)0;

     buf = (R *) MALLOC(sizeof(R) * 2 * BATCHDIST(r) * ego->batchsz, BUFFERS);
     cld = X(mkplan_d)(plnr,
               X(mkproblem_dft_d)(
                    X(mktensor_1d)(r, 2, 2),
                    X(mktensor_1d)(ego->batchsz,
                             2 * BATCHDIST(r),
                             2 * BATCHDIST(r)),
                    buf, buf + 1, buf, buf + 1
                    )
               );
     X(ifree)(buf);
     if (!cld) goto nada;

     pln = MKPLAN_DFTW(P, &padt, apply);
     pln->slv = ego;
     pln->cld = cld;
     pln->r = r;
     pln->m = m;
     pln->ms = ms;
     pln->rs = irs;
     pln->batchsz = ego->batchsz;
     pln->mb = mstart;
     pln->me = mstart + mcount;

     {
       double n0 = (r - 1) * (mcount - 1);
       pln->super.super.ops = cld->ops;
       pln->super.super.ops.mul += 8 * n0;
       pln->super.super.ops.add += 4 * n0;
       pln->super.super.ops.other += 8 * n0;
     }
     return &(pln->super.super);

 nada:
     X(plan_destroy_internal)(cld);
     return (plan *) 0;
}

static void regsolver(planner *plnr, INT r, INT batchsz)
{
     S *slv = (S *)X(mksolver_ct)(sizeof(S), r, DECDIT, mkcldw, 0);
     slv->batchsz = batchsz;
     REGISTER_SOLVER(plnr, &(slv->super.super));

     if (X(mksolver_ct_hook)) {
       slv = (S *)X(mksolver_ct_hook)(sizeof(S), r, DECDIT, mkcldw, 0);
       slv->batchsz = batchsz;
       REGISTER_SOLVER(plnr, &(slv->super.super));
     }

}

void X(ct_genericbuf_register)(planner *p)
{
     static const INT radices[] = { -1, -2, -4, -8, -16, -32, -64 };
     static const INT batchsizes[] = { 4, 8, 16, 32, 64 };
     unsigned i, j;

     for (i = 0; i < sizeof(radices) / sizeof(radices[0]); ++i)
       for (j = 0; j < sizeof(batchsizes) / sizeof(batchsizes[0]); ++j)
            regsolver(p, radices[i], batchsizes[j]);
}
