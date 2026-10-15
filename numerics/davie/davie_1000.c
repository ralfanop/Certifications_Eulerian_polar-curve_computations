/* 1000+ certified digits of Davie's constant C_D = (pi/2) exp(alpha*^2), H(alpha*) = 0,
   H(a) = 1 - 2 c J(a) - c^2 e^{-a^2}, c = sqrt(2/pi), J(a) = int_0^a e^{-t^2/2} dt.
   Interval Newton step with certified sign checks at the end. */
#include <stdio.h>
#include <flint/arb.h>
#include <flint/arb_hypgeom.h>
static slong P=3600;
static void cc(arb_t c){ arb_const_pi(c,P); arb_inv(c,c,P); arb_mul_2exp_si(c,c,1); arb_sqrt(c,c,P); }
static void H(arb_t h,const arb_t a){ arb_t c,s,t; arb_init(c);arb_init(s);arb_init(t); cc(c);
  arb_sqrt_ui(s,2,P); arb_div(t,a,s,P); arb_hypgeom_erf(t,t,P); arb_const_pi(s,P); arb_mul_2exp_si(s,s,-1); arb_sqrt(s,s,P); arb_mul(t,t,s,P);
  arb_mul(h,c,t,P); arb_mul_2exp_si(h,h,1); arb_neg(h,h); arb_add_ui(h,h,1,P);
  arb_sqr(t,a,P); arb_neg(t,t); arb_exp(t,t,P); arb_mul(t,t,c,P); arb_mul(t,t,c,P); arb_sub(h,h,t,P);
  arb_clear(c);arb_clear(s);arb_clear(t);}
static void dH(arb_t d,const arb_t a){ arb_t c,t,u; arb_init(c);arb_init(t);arb_init(u); cc(c);
  arb_sqr(t,a,P); arb_mul_2exp_si(t,t,-1); arb_neg(t,t); arb_exp(t,t,P); arb_mul(d,c,t,P); arb_mul_2exp_si(d,d,1); arb_neg(d,d);
  arb_sqr(t,a,P); arb_neg(t,t); arb_exp(t,t,P); arb_mul(t,t,a,P); arb_mul(t,t,c,P); arb_mul(t,t,c,P); arb_mul_2exp_si(t,t,1); arb_add(d,d,t,P);
  arb_clear(c);arb_clear(t);arb_clear(u);}
int main(void){ arb_t a,h,d,lo,hi,eps,C,pi; arb_init(a);arb_init(h);arb_init(d);arb_init(lo);arb_init(hi);arb_init(eps);arb_init(C);arb_init(pi);
  arb_set_str(a,"0.2557302131662100143618699337283326079",P);
  for(int k=0;k<12;k++){ H(h,a); dH(d,a); arb_div(h,h,d,P); arb_sub(a,a,h,P); arb_get_mid_arb(a,a); }
  /* certify: H(a - eps) > 0 > H(a + eps), H strictly decreasing on [0,inf) (as in the Lean project) */
  arb_one(eps); arb_mul_2exp_si(eps,eps,-3500);
  arb_sub(lo,a,eps,P); arb_add(hi,a,eps,P); H(h,lo); int ok=arb_is_positive(h); H(h,hi); ok&=arb_is_negative(h);
  dH(d,a); printf("H'(alpha*) < 0: %s\n", arb_is_negative(d)?"yes":"no");
  printf("sign change certified on [a-2^-3500, a+2^-3500]: %s\n", ok?"yes":"NO");
  arb_union(a,lo,hi,P); arb_sqr(C,a,P); arb_exp(C,C,P); arb_const_pi(pi,P); arb_mul(C,C,pi,P); arb_mul_2exp_si(C,C,-1);
  printf("alpha* = "); arb_printn(a,1010,0); printf("\n");
  printf("C_D = "); arb_printn(C,1010,0); printf("\n");
  return 0; }
