"""Validated normalized-arclength curvature quadrature with Cauchy remainders.

Reuses the already validated Taylor and inverse-series enclosures, but replaces
wide interval-series remainder evaluation by a certified complex strip bound.
All proof inequalities are Arb comparisons; Newton is only candidate generation.
"""
import argparse,time,json,sys
from pathlib import Path
from flint import arb,acb,arb_poly,arb_series,ctx
from dkappa.certify_dk import Certification
from m11_euler_cauchy import exact_endpoints
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def strip_certificate():
    ctx.prec=128
    pi=arb.pi(); b=2/pi*(pi/2).si(); a=2/pi*((3*pi/2).si()-(pi/2).si())
    count=0
    # Exact rectangle tiling of [-3/8, 11/8] + i[-3/8,3/8].
    for i in range(-24,88):
        for j in range(-24,24):
            t=pi*acb(arb((arb(i)+arb(1)/2)/64,arb(1)/128),
                     arb((arb(j)+arb(1)/2)/64,arb(1)/128))
            z=-t*t/16
            f=z.hypgeom_0f1(arb(5)/2)
            E=[z.hypgeom_0f1(arb(3)/2),-t*f/12,
                -f/12+t*t*z.hypgeom_0f1(arb(7)/2)/240]
            L=[b+a*t.cos(),-a*t.sin(),-a*t.cos()]
            for r,p,q in (E,L):
                F=r*r+p*p
                assert F.real>0, (i,j)
                v=F.sqrt(analytic=True)
                H=pi*v; K=(r*r+2*p*p-r*q)/(F*v)
                assert H.real>arb(6)/5 and H.abs_upper()<4
                assert K.abs_upper()<35
                count+=1
    print('Complex strip bound: positive speed, |H|<4, |K|<35 in',count,'boxes: PASS',flush=True)

class CauchyCertification(Certification):
    def __init__(self,bits,order,panels,terms):
        strip_certificate()
        super().__init__(bits,order,panels,terms)
        self.delta=arb(3)/8
        self.R=arb(3)/20

    def geometry(self,kind,x,order=None):
        if order != 0:
            return super().geometry(kind,x,order)
        # Efficient point evaluation for Newton candidate generation.
        t=self.pi*x
        if kind=='E':
            if not t>0:
                return super().geometry(kind,x,order)
            r=(t/2).sinc(); rp=((t/2).cos()-r)/t
            rpp=-2*rp/t-r/4
        else:
            r=self.b+self.a*t.cos(); rp=-self.a*t.sin(); rpp=-self.a*t.cos()
        F=r*r+rp*rp; H=self.pi*F.sqrt(); K=(r*r+2*rp*rp-r*rpp)/(F*F.sqrt())
        return arb_series([H],prec=1),arb_series([K],prec=1)

    def build_chart(self,kind):
        p,n=self.order,self.panels; h=arb(1)/n
        assert h<self.delta
        # Cauchy: |H_k|<=4/delta^k. Integrating the tail after degree p-1,
        # use 1/(k+1)<=1/(p+1) and geometric sum. Valid for every d<=h.
        B=4/(self.delta**p*(1-h/self.delta))
        cells=[]; total=arb(0)
        for j in range(n):
            lo=arb(j)/n
            point,_=self.geometry(kind,lo)
            poly=arb_poly([arb(0)]+[point[k]/(k+1) for k in range(p)])
            error=B*h**(p+1)/(p+1)
            cells.append({'left':lo,'cumulative':total,'integral':poly,'B':B})
            total=total+poly(h)+arb(0,error.upper())
        assert 0<total<3
        self.charts[kind]={'cells':cells,'length':total}
        return total

    def inverse(self,kind,u):
        # Real speed >= 2 (r_E>=2/pi; pi*(b-a)>2); residual proves root enclosure.
        ell=self.charts[kind]['length']; x=u.mid()
        for _ in range(32):
            residual=self.arclength(kind,x)-u*ell
            H,_=self.geometry(kind,x,order=0)
            nxt=(x-residual/H[0]).mid()
            assert 0<=nxt<=1
            if nxt==x or (nxt-x).abs_upper() < residual.rad():
                x=nxt;break
            x=nxt
        residual=self.arclength(kind,x)-u*ell
        return arb(x,(residual.abs_upper()/2).upper())

    def integrate_discrepancy(self):
        p,n=self.order,self.panels;h=arb(1)/(2*n)
        assert h<self.R
        # Holomorphic inverse: on the convex strip Re H>6/5, hence normalized
        # primitive A/ell is injective. For |z-x|=3/8, its difference from
        # A(x)/ell has modulus > (6/5)*(3/8)/ell > 3/20 (ell<3).
        # Rouche gives an inverse on |u-u0|<=3/20, with nonzero derivative.
        # |K_E-K_L|²<70²=4900 there, so Cauchy bounds the Taylor tail.
        ratio=h/self.R
        rem=2*h*4900*ratio**p/((p+1)*(1-ratio))
        total=arb(0)
        for j in range(n):
            u=(arb(j)+arb(1)/2)/n
            X={k:self.inverse(k,u) for k in ('E','L')}
            assert all(v>=0 and v<=1 for v in X.values())
            jets={k:self.inverse_curvature_jet(k,X[k]) for k in ('E','L')}
            f=(jets['E']-jets['L'])**2
            val=sum((f[k]*2*h**(k+1)/(k+1) for k in range(0,p,2)),arb(0))
            total+=val+arb(0,rem.upper())
            if (j+1)%16==0:
                print('Outer panels',j+1,'/',n,'radius',total.rad().str(8),flush=True)
        assert total>0
        return total.sqrt()

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--bits',type=int,default=2048)
    ap.add_argument('--order',type=int,default=256);ap.add_argument('--panels',type=int,default=64)
    ap.add_argument('--terms',type=int,default=300)
    ap.add_argument('--minimum-bits',type=int,default=500)
    ap.add_argument('--output',default='m11-dk-cauchy.json');args=ap.parse_args()
    t=time.monotonic();c=CauchyCertification(args.bits,args.order,args.panels,args.terms)
    E=c.build_chart('E');print('Eulerian half length relative bits',E.rel_accuracy_bits(),flush=True)
    L=c.build_chart('L');print('Limacon half length relative bits',L.rel_accuracy_bits(),flush=True)
    d=c.integrate_discrepancy()
    assert arb('0.2037837595360494438260805')<d<arb('0.2037837595360494438260815')
    assert d.rel_accuracy_bits()>=args.minimum_bits
    Path(args.output).write_text(json.dumps({'quantity':'D_kappa, Eq. (50)','parameters':vars(args),
        'Eulerian_half_length':exact_endpoints(E),'limacon_half_length':exact_endpoints(L),
        'discrepancy':exact_endpoints(d),'elapsed_seconds':time.monotonic()-t},indent=2)+'\n')
    print('D_kappa',d.str(65),'relative bits',d.rel_accuracy_bits(),'elapsed',time.monotonic()-t,flush=True)
