/* Independent Arb check of Davie's lower bound (original 2024 formula):
   F_rho(a) = (2/pi) e^{-a^2} + rho (1 - 2 c int_a^inf e^{-x^2/2} dx),  c = sqrt(2/pi),
   rho(a) = c a e^{-a^2/2},  K_G >= sup_{0<a<1} (1 - rho)/max(rho, F_rho(a)).
   Claimed: optimiser alpha* solves H(a) = 1 - 2 c J(a) - c^2 e^{-a^2} = 0, J(a) = int_0^a e^{-t^2/2} dt,
   and the bound equals C_D = (pi/2) e^{alpha*^2}. */
#include <stdio.h>
#include <flint/arb.h>
#include <flint/arb_hypgeom.h>
static slong P=256;
static void cconst(arb_t c){ arb_const_pi(c,P); arb_inv(c,c,P); arb_mul_2exp_si(c,c,1); arb_sqrt(c,c,P); }
/* J(a) = sqrt(pi/2) erf(a/sqrt2) */
static void Jfun(arb_t J,const arb_t a){ arb_t s,t; arb_init(s);arb_init(t);
  arb_sqrt_ui(s,2,P); arb_div(t,a,s,P); arb_hypgeom_erf(t,t,P);
  arb_const_pi(s,P); arb_mul_2exp_si(s,s,-1); arb_sqrt(s,s,P); arb_mul(J,s,t,P); arb_clear(s);arb_clear(t);}
static void Hfun(arb_t H,const arb_t a){ arb_t c,J,t; arb_init(c);arb_init(J);arb_init(t); cconst(c); Jfun(J,a);
  arb_mul(H,c,J,P); arb_mul_2exp_si(H,H,1); arb_neg(H,H); arb_add_ui(H,H,1,P);
  arb_sqr(t,a,P); arb_neg(t,t); arb_exp(t,t,P); arb_mul(t,t,c,P); arb_mul(t,t,c,P); arb_sub(H,H,t,P);
  arb_clear(c);arb_clear(J);arb_clear(t);}
/* ratio R(a) = (1-rho)/max(rho,F) */
static void Rfun(arb_t R,const arb_t a){ arb_t c,rho,F,t,u; arb_init(c);arb_init(rho);arb_init(F);arb_init(t);arb_init(u); cconst(c);
  arb_sqr(t,a,P); arb_mul_2exp_si(t,t,-1); arb_neg(t,t); arb_exp(t,t,P); arb_mul(rho,c,a,P); arb_mul(rho,rho,t,P);
  /* tail = int_a^inf e^{-x^2/2} = sqrt(pi/2) erfc(a/sqrt2) */
  arb_sqrt_ui(t,2,P); arb_div(t,a,t,P); arb_hypgeom_erfc(t,t,P); arb_const_pi(u,P); arb_mul_2exp_si(u,u,-1); arb_sqrt(u,u,P); arb_mul(t,t,u,P);
  arb_mul(t,t,c,P); arb_mul_2exp_si(t,t,1); arb_neg(t,t); arb_add_ui(t,t,1,P); arb_mul(F,rho,t,P);
  arb_sqr(t,a,P); arb_neg(t,t); arb_exp(t,t,P); arb_const_pi(u,P); arb_div(t,t,u,P); arb_mul_2exp_si(t,t,1); arb_add(F,F,t,P);
  arb_max(t,rho,F,P); arb_sub_ui(u,rho,1,P); arb_neg(u,u); arb_div(R,u,t,P);
  arb_clear(c);arb_clear(rho);arb_clear(F);arb_clear(t);arb_clear(u);}
int main(void){ arb_t lo,hi,mid,H,C,R,t; arb_init(lo);arb_init(hi);arb_init(mid);arb_init(H);arb_init(C);arb_init(R);arb_init(t);
  arb_set_str(lo,"0.25",P); arb_set_str(hi,"0.26",P);
  Hfun(H,lo); printf("H(0.25) = "); arb_printd(H,20); printf("\n"); Hfun(H,hi); printf("H(0.26) = "); arb_printd(H,20); printf("\n");
  for(int k=0;k<200;k++){ arb_add(mid,lo,hi,P); arb_mul_2exp_si(mid,mid,-1); arb_get_mid_arb(mid,mid); Hfun(H,mid);
    if(arb_is_positive(H)) arb_set(lo,mid); else if(arb_is_negative(H)) arb_set(hi,mid); else break; }
  printf("alpha* in [");arb_printd(lo,40);printf(", ");arb_printd(hi,40);printf("]\n");
  /* C_D = (pi/2) exp(alpha^2) on the enclosing interval */
  arb_union(t,lo,hi,P); arb_sqr(C,t,P); arb_exp(C,C,P); arb_const_pi(H,P); arb_mul(C,C,H,P); arb_mul_2exp_si(C,C,-1);
  printf("C_D = "); arb_printn(C,40,0); printf("\n");
  /* ratio at alpha* and nearby points */
  Rfun(R,t); printf("R(alpha*) = "); arb_printn(R,40,0); printf("\n");
  const char* pts[]={"0.2","0.25","0.2557","0.2558","0.26","0.3","0.5","0.9"};
  for(int i=0;i<8;i++){ arb_set_str(mid,pts[i],P); Rfun(R,mid); printf("R(%s) = ",pts[i]); arb_printn(R,25,0); printf("\n"); }
  return 0; }
