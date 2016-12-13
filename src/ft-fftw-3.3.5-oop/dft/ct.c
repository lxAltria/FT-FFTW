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


#include "ct.h"
#include <stdio.h>
#include <stdbool.h>

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

ct_solver *(*X(mksolver_ct_hook))(size_t, INT, int, 
				  ct_mkinferior, ct_force_vrecursion) = 0;

typedef struct {
     plan_dft super;
     plan *cld;
     plan *cldw;
     INT r;

     INT size;
} P;

bool ctStart = true;

R * checksum1; // rA x
R * checksum2; // 1/i x
R * simpleCoeff; 
R * coeff;
R * rA1;

extern bool secondFFT;

static void apply_dit(const plan *ego_, R *ri, R *ii, R *ro, R *io)
{
     const P *ego = (const P *) ego_;
     plan_dft *cld;
     plan_dftw *cldw;

  if(secondFFT)
  {
     if(ctStart) 
     {
     	// printf("ct r, size: %td %td\n", ego->r, ego->size);
     	ctStart = false;
        
     	int radix = ego->size / ego->r;
     	int m = ego->r;

        checksum1 = (R *) malloc(radix*2*sizeof(R));
        checksum2 = (R *) malloc(radix*2*sizeof(R));

        rA1 = (R *) malloc(m*2*sizeof(R));

        R * rA0;
        R sumrA0 = 0, sumrA1 = 0;

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

        int coeffSize = radix>m? radix:m;
        simpleCoeff = (R *) malloc(coeffSize*sizeof(R));
        for(int i=0; i<coeffSize; i++)
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
     // printf("ct prepartion done\n");

   }
     cld = (plan_dft *) ego->cld;
     cld->apply(ego->cld, ri, ii, ro, io);

     // printf("ct first part done. r, size: %td %td\n", ego->r, ego->size);

     cldw = (plan_dftw *) ego->cldw;
     cldw->apply(ego->cldw, ro, io);

     // printf("ct second part done. r, size: %td %td\n", ego->r, ego->size);

}

static void apply_dif(const plan *ego_, R *ri, R *ii, R *ro, R *io)
{
     const P *ego = (const P *) ego_;
     plan_dft *cld;
     plan_dftw *cldw;

     cldw = (plan_dftw *) ego->cldw;
     cldw->apply(ego->cldw, ri, ii);

     cld = (plan_dft *) ego->cld;
     cld->apply(ego->cld, ri, ii, ro, io);
}

static void awake(plan *ego_, enum wakefulness wakefulness)
{
     P *ego = (P *) ego_;
     X(plan_awake)(ego->cld, wakefulness);
     X(plan_awake)(ego->cldw, wakefulness);
}

static void destroy(plan *ego_)
{
     P *ego = (P *) ego_;
     X(plan_destroy_internal)(ego->cldw);
     X(plan_destroy_internal)(ego->cld);
}

static void print(const plan *ego_, printer *p)
{
     const P *ego = (const P *) ego_;
     p->print(p, "(dft-ct-%s/%D%(%p%)%(%p%))",
	      ego->super.apply == apply_dit ? "dit" : "dif",
	      ego->r, ego->cldw, ego->cld);
}

static int applicable0(const ct_solver *ego, const problem *p_, planner *plnr)
{
     const problem_dft *p = (const problem_dft *) p_;
     INT r;

     return (1
	     && p->sz->rnk == 1
	     && p->vecsz->rnk <= 1

	     /* DIF destroys the input and we don't like it */
	     && (ego->dec == DECDIT ||
		 p->ri == p->ro ||
		 !NO_DESTROY_INPUTP(plnr))

	     && ((r = X(choose_radix)(ego->r, p->sz->dims[0].n)) > 1)
	     && p->sz->dims[0].n > r);
}


int X(ct_applicable)(const ct_solver *ego, const problem *p_, planner *plnr)
{
     const problem_dft *p;

     if (!applicable0(ego, p_, plnr))
          return 0;

     p = (const problem_dft *) p_;

     return (0
	     || ego->dec == DECDIF+TRANSPOSE
	     || p->vecsz->rnk == 0
	     || !NO_VRECURSEP(plnr)
	     || (ego->force_vrecursionp && ego->force_vrecursionp(ego, p))
	  );
}


static plan *mkplan(const solver *ego_, const problem *p_, planner *plnr)
{
     const ct_solver *ego = (const ct_solver *) ego_;
     const problem_dft *p;
     P *pln = 0;
     plan *cld = 0, *cldw = 0;
     INT n, r, m, v, ivs, ovs;
     iodim *d;

     static const plan_adt padt = {
	  X(dft_solve), awake, print, destroy
     };

     if ((NO_NONTHREADEDP(plnr)) || !X(ct_applicable)(ego, p_, plnr))
          return (plan *) 0;

     p = (const problem_dft *) p_;
     d = p->sz->dims;
     n = d[0].n;
     r = X(choose_radix)(ego->r, n);
     m = n / r;

     X(tensor_tornk1)(p->vecsz, &v, &ivs, &ovs);

     switch (ego->dec) {
	 case DECDIT:
	 {
	      cldw = ego->mkcldw(ego,
				 r, m * d[0].os, m * d[0].os,
				 m, d[0].os,
				 v, ovs, ovs,
				 0, m,
				 p->ro, p->io, plnr);
	      if (!cldw) goto nada;

	      cld = X(mkplan_d)(plnr,
				X(mkproblem_dft_d)(
				     X(mktensor_1d)(m, r * d[0].is, d[0].os),
				     X(mktensor_2d)(r, d[0].is, m * d[0].os,
						    v, ivs, ovs),
				     p->ri, p->ii, p->ro, p->io)
		   );
	      if (!cld) goto nada;

	      pln = MKPLAN_DFT(P, &padt, apply_dit);
	      break;
	 }
	 case DECDIF:
	 case DECDIF+TRANSPOSE:
	 {
	      INT cors, covs; /* cldw ors, ovs */
	      if (ego->dec == DECDIF+TRANSPOSE) {
		   cors = ivs;
		   covs = m * d[0].is;
		   /* ensure that we generate well-formed dftw subproblems */
		   /* FIXME: too conservative */
		   if (!(1
			 && r == v
			 && d[0].is == r * cors))
			goto nada;

		   /* FIXME: allow in-place only for now, like in
		      fftw-3.[01] */
		   if (!(1
			 && p->ri == p->ro
			 && d[0].is == r * d[0].os
			 && cors == d[0].os
			 && covs == ovs
			    ))
			goto nada;
	      } else {
		   cors = m * d[0].is;
		   covs = ivs;
	      }

	      cldw = ego->mkcldw(ego,
				 r, m * d[0].is, cors,
				 m, d[0].is,
				 v, ivs, covs,
				 0, m,
				 p->ri, p->ii, plnr);
	      if (!cldw) goto nada;

	      cld = X(mkplan_d)(plnr,
				X(mkproblem_dft_d)(
				     X(mktensor_1d)(m, d[0].is, r * d[0].os),
				     X(mktensor_2d)(r, cors, d[0].os,
						    v, covs, ovs),
				     p->ri, p->ii, p->ro, p->io)
		   );
	      if (!cld) goto nada;

	      pln = MKPLAN_DFT(P, &padt, apply_dif);
	      break;
	 }

	 default: A(0);

     }

     pln->cld = cld;
     pln->cldw = cldw;
     pln->r = r;

     pln->size = n;
     X(ops_add)(&cld->ops, &cldw->ops, &pln->super.super.ops);

     /* inherit could_prune_now_p attribute from cldw */
     pln->super.super.could_prune_now_p = cldw->could_prune_now_p;
     return &(pln->super.super);

 nada:
     X(plan_destroy_internal)(cldw);
     X(plan_destroy_internal)(cld);
     return (plan *) 0;
}

ct_solver *X(mksolver_ct)(size_t size, INT r, int dec, 
			  ct_mkinferior mkcldw,
			  ct_force_vrecursion force_vrecursionp)
{
     static const solver_adt sadt = { PROBLEM_DFT, mkplan, 0 };
     ct_solver *slv = (ct_solver *)X(mksolver)(size, &sadt);
     slv->r = r;
     slv->dec = dec;
     slv->mkcldw = mkcldw;
     slv->force_vrecursionp = force_vrecursionp;
     return slv;
}

plan *X(mkplan_dftw)(size_t size, const plan_adt *adt, dftwapply apply)
{
     plan_dftw *ego;

     ego = (plan_dftw *) X(mkplan)(size, adt);
     ego->apply = apply;

     return &(ego->super);
}
