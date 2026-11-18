"""Fast certified normalized-arclength curvature jets via scalar ODE Newton.

For local variable z=(u-u0)/h, theta'(z)=h*ell/speed(theta(z)).
Avoid generic power-series reversion and composition. Formal Newton doubling
solves the linearized scalar ODE by an integrating factor; all coefficients
are computed using enclosing Arb series arithmetic. Existing complex strip
Cauchy remainder proof and real inverse root enclosures are reused unchanged.
"""
import argparse,json,time,math
from pathlib import Path
from flint import acb,arb,arb_poly,arb_series,ctx
from m11_dk_cauchy import CauchyCertification,exact_endpoints,strip_certificate
from m11_euler_cauchy import analytic_disk

def geom(kind,t,a,b):
    if kind=='E':
        sn,cs=(t/2).sin_cos()
        r=2*sn/t; p=(cs-r)/t; q=-2*p/t-r/4
    else:
        sn,cs=t.sin_cos(); r=b+a*cs; p=-a*sn; q=-a*cs
    V=r*r+p*p; v=V.sqrt()
    return r,p,q,V,v

def theta_jet(kind,theta0,scale,a,b,degree,budget=None,weight_rate=0):
    # Invariant: coeffs contain the exact solution coefficients 0..m-1.
    # Given their exact polynomial y, solve delta'=F'(y) delta+F(y)-y'
    # with delta(0)=0. Since delta=O(z^m), quadratic remainder O(z^(2m));
    # the correction determines coefficients through degree 2m-1 exactly.
    coeffs=[theta0];m=1;work=ctx.prec
    try:
        while m<degree:
            if budget is not None:
                # Heuristic precision allocation only. High-order coefficients
                # are suppressed by (h/s)^m in the final integral. Arb balls
                # remain rigorous at every chosen precision; final accuracy
                # and exact endpoints are checked independently.
                ctx.prec=min(work,max(128,budget-int(m*weight_rate)))
            d=min(2*m,degree)
            y=arb_series(coeffs,prec=d)
            r,p,q,V,v=geom(kind,y,a,b)
            F=scale/v
            # Work on shifted residual R=z^(m-1)*Rtilde and delta=z^m*Dtilde.
            k=d-m
            trunc=lambda s:arb_series([s[j] for j in range(k)],prec=k)
            J=-scale*trunc(p)*(trunc(r)+trunc(q))/(trunc(V)*trunc(v))
            G=trunc(J.integral()).exp()
            Rt=arb_series([F[m-1+j] for j in range(k)],prec=k)
            T=G.inv()*Rt
            W=arb_series([T[j]/(m+j) for j in range(k)],prec=k)
            D=G*W
            coeffs += [D[j] for j in range(k)]
            m=d
    finally:
        ctx.prec=work
    return arb_series(coeffs,prec=degree)

class ODECertification(CauchyCertification):
    def __init__(self,bits,order,panels,terms=None,adaptive=False):
        # No global radial polynomial nor derivative-tail table is needed.
        # All jets use the exact trigonometric speed and curvature identities.
        assert order>=4 and order%2==0 and panels>=4 and panels&(panels-1)==0
        strip_certificate()
        self.bits,self.order,self.panels=bits,order,panels
        ctx.prec=bits; ctx.cap=order+5
        self.pi=arb.pi()
        si1=(self.pi/2).si();si3=(3*self.pi/2).si()
        self.b=2*si1/self.pi;self.a=2*(si3-si1)/self.pi
        assert self.b>2*self.a>0 and self.pi*(self.b-self.a)>2
        self.delta=arb(3)/8;self.R=arb(3)/20;self.charts={};self.adaptive=adaptive

    def build_chart(self,kind):
        if kind=='L':
            # Exact elliptic-integral reduction of the projected limaçon.
            # Direct Arb/Acb evaluations avoid storing a second Taylor chart.
            m=4*self.a*self.b/(self.a+self.b)**2;assert 0<m<1
            E=acb(m).elliptic_e();assert E.imag.contains(0)
            total=2*(self.a+self.b)*E.real;assert 0<total<3
            self.charts[kind]={'length':total,'m':m}
            return total
        # One global Eulerian primitive, with independent zero-free disk proof.
        # Its target is chosen to dominate the outer discrepancy Cauchy tail.
        analytic_disk();ctx.prec=self.bits
        p,n=self.order,self.panels
        target=min(self.bits-128, math.ceil(p*math.log2(float(self.R*(2*n))))+128)
        N=(target+20)*25//33+2
        ctx.cap=N
        pi=self.pi;qmax=pi*pi/25;eta=arb(2)**(-self.bits-20)
        assert 0<qmax<arb('0.4') and 4/pi**2-eta>arb(1)/4
        assert eta<arb(1)/128
        assert 4*pi*qmax**N/(1-qmax)<arb(2)**(-target-4)
        a=arb(1)/24;coeff=[]
        for k in range(N):
            m=2*k+4;term=a*((3*m*(m-1))//2+2*m-2)
            if k>=5 and 2*term.abs_upper()<eta:break
            coeff.append(term);a=-25*a/((m+1)*(m+2))
        if len(coeff)==N:
            m=2*N+4
            assert N>=5 and 2*(a*((3*m*(m-1))//2+2*m-2)).abs_upper()<eta
        # The original analytic_disk certificate proves |F|>1/64 on |t|<=5.
        # P differs uniformly from F by eta; sqrt(P) analytic and bounded by 4.
        S=arb_series(coeff,prec=N).sqrt()
        poly=arb_poly([S[k]/(2*k+1) for k in range(N)])
        self.charts['E']={'poly':poly,'N':N,'eta':eta}
        total=self.euler_primitive(pi)
        assert 0<total<3 and total.rel_accuracy_bits()>=target
        self.charts['E']['length']=total
        ctx.cap=p+5
        return total

    def euler_primitive(self,t):
        c=self.charts['E'];q=t*t/25
        assert 0<=q<1
        # Integrated tail and polynomial speed-square replacement error.
        tail=4*t*q**c['N']/(1-q)+t*c['eta']
        return t*c['poly'](q)+arb(0,tail.upper())

    def arclength(self,kind,x):
        assert x.is_exact() and 0<=x<=1
        if x==0:return arb(0)
        chart=self.charts[kind]
        if x==1:return chart['length']
        if kind=='L':
            v=acb.elliptic_e_inc(self.pi*x/2,chart['m']);assert v.imag.contains(0)
            return 2*(self.a+self.b)*v.real
        return self.euler_primitive(self.pi*x)

    def geometry(self,kind,x,order=None):
        # Ancestor inverse() only requests order zero at an exact interior point.
        assert order==0 and x>0
        return super().geometry(kind,x,order)

    def normalized_curvature_jet(self,kind,X,s,budget=None,weight_rate=0):
        theta0=self.pi*X
        assert theta0>0
        y=theta_jet(kind,theta0,s*self.charts[kind]['length'],self.a,self.b,self.order,budget,weight_rate)
        r,p,q,V,v=geom(kind,y,self.a,self.b)
        return (r*r+2*p*p-r*q)/(V*v)

    def integrate_discrepancy(self):
        p,n=self.order,self.panels; h=arb(1)/(2*n)
        ratio=h/self.R;assert 0<ratio<1
        # Same certified bound as m11_dk_cauchy.py; only the local jets change.
        rem=2*h*4900*ratio**p/((p+1)*(1-ratio))
        total=arb(0)
        for j in range(n):
            u=(arb(j)+arb(1)/2)/n
            X={k:self.inverse(k,u) for k in ('E','L')}
            assert all(v>0 and v<1 for v in X.values())
            s=h;budget=None;rate=0
            if self.adaptive:
                # Keep the artificial removable denominator theta well away
                # from zero for most panels; first panel falls back to h.
                s=max(h,min(self.R/2,u/2));assert h<=s<self.R
                rate=math.log2(float(s/h));budget=math.ceil(p*math.log2(float(self.R/h)))+256
            jets={k:self.normalized_curvature_jet(k,X[k],s,budget,rate) for k in ('E','L')}
            f=(jets['E']-jets['L'])**2
            w=h/s
            val=sum((f[k]*2*h*w**k/(k+1) for k in range(0,p,2)),arb(0))
            total+=val+arb(0,rem.upper())
            if (j+1)%16==0:
                print('ODE outer panels',j+1,'/',n,'radius',total.rad().str(8),flush=True)
        assert total>0
        return total.sqrt()

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--bits',type=int,default=1024)
    ap.add_argument('--order',type=int,default=128);ap.add_argument('--panels',type=int,default=64)
    ap.add_argument('--terms',type=int,default=160);ap.add_argument('--minimum-bits',type=int,default=450)
    ap.add_argument('--adaptive',action='store_true')
    ap.add_argument('--output',default='m11-dk-ode.json');args=ap.parse_args()
    t=time.monotonic();c=ODECertification(args.bits,args.order,args.panels,args.terms,args.adaptive)
    E=c.build_chart('E'); print('Eulerian half length relative bits',E.rel_accuracy_bits(),flush=True)
    L=c.build_chart('L'); print('Limacon half length relative bits',L.rel_accuracy_bits(),flush=True)
    d=c.integrate_discrepancy()
    assert arb('0.2037837595360494438260805')<d<arb('0.2037837595360494438260815')
    assert d.rel_accuracy_bits()>=args.minimum_bits,(d.rel_accuracy_bits(),args.minimum_bits)
    elapsed=time.monotonic()-t
    Path(args.output).write_text(json.dumps({'quantity':'D_kappa, Eq. (50)','method':'formal scalar ODE Newton doubling','parameters':vars(args),
        'Eulerian_half_length':exact_endpoints(E),'limacon_half_length':exact_endpoints(L),
        'discrepancy':exact_endpoints(d),'elapsed_seconds':elapsed},indent=2)+'\n')
    print('D_kappa ODE',d.str(65),'relative bits',d.rel_accuracy_bits(),'elapsed',elapsed,flush=True)
