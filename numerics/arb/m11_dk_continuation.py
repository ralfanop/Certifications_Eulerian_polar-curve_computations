"""Validated simultaneous angle continuation for M11 Eq. (50).

Use the same holomorphic inverse charts and Cauchy bounds as the prior
certificate.  After the first midpoint, no global inverse is evaluated.
Both angle series are advanced using their own rigorously bounded tails;
the same jets integrate the squared curvature discrepancy.
"""
import argparse,json,math,time,resource
from pathlib import Path
from flint import arb,arb_poly,arb_series,ctx
from m11_dk_ode import ODECertification,geom,theta_jet,exact_endpoints
from m11_euler_cauchy import evaluate as length_evaluate


def geom_zero(coeffs,d):
    # Exact removable singularities at theta(0)=0.  To obtain d curvature
    # coefficients, keep three extra coefficients for the shifted divisions.
    assert coeffs[0].is_zero() and not coeffs[1].contains(0)
    t=arb_series(coeffs,prec=d+3)
    sn,cs=(t/2).sin_cos()
    def divide_shift(v,k):
        # The numerator vanishes at zero as an identity, so division by
        # theta is the ordinary quotient after removing one factor z.
        return arb_series([v[j+1] for j in range(k)],prec=k)/arb_series([t[j+1] for j in range(k)],prec=k)
    r=divide_shift(2*sn,d+2)
    rp=divide_shift(cs-r,d+1)
    rpp=-2*divide_shift(rp,d)-r/4
    cut=lambda v:arb_series([v[j] for j in range(d)],prec=d)
    r,rp,rpp=map(cut,(r,rp,rpp));V=r*r+rp*rp
    return r,rp,rpp,V,V.sqrt()


def zero_jet(kind,scale,a,b,degree):
    # First-order coefficient follows exactly from the ODE at the vertex.
    coeffs=[arb(0),scale if kind=='E' else scale/(a+b)];m=2
    while m<degree:
        d=min(2*m,degree);y=arb_series(coeffs,prec=d)
        r,p,q,V,v=geom_zero(coeffs,d) if kind=='E' else geom(kind,y,a,b)
        F=scale/v;k=d-m
        cut=lambda s:arb_series([s[j] for j in range(k)],prec=k)
        J=-scale*cut(p)*(cut(r)+cut(q))/(cut(V)*cut(v))
        G=cut(J.integral()).exp()
        Rt=arb_series([F[m-1+j] for j in range(k)],prec=k)
        T=G.inv()*Rt;W=arb_series([T[j]/(m+j) for j in range(k)],prec=k);D=G*W
        coeffs += [D[j] for j in range(k)];m=d
    return arb_series(coeffs,prec=degree)


class Continuation(ODECertification):
    def build_chart(self,kind):
        if kind=='L':return super().build_chart(kind)
        target=min(self.bits-128,math.ceil(self.order*math.log2(float(self.R*2*self.panels)))+256)
        length=length_evaluate(self.bits,target)/2
        assert 0<length<3
        self.charts[kind]={'length':length}
        return length

    def integrate_discrepancy(self):
        p,n=self.order,self.panels;h=arb(1)/(2*n);step=2*h
        assert step<self.R and self.pi*(1+arb(3)/8)<5
        ratio=h/self.R;advance_ratio=step/self.R
        rem=2*h*4900*ratio**p/((p+1)*(1-ratio))
        angle_rem=5*advance_ratio**p/(1-advance_ratio)
        # Start at the exact symmetry vertex theta_E(0)=theta_L(0)=0.
        # The starter's Cauchy tail follows from the same inverse disk.
        first_rem=5*ratio**p/(1-ratio)
        ctx.cap=p+5
        theta={}
        for k in ('E','L'):
            y=zero_jet(k,h*self.charts[k]['length'],self.a,self.b,p)
            theta[k]=sum((y[i] for i in range(p)),arb(0))+arb(0,first_rem.upper())
        total=arb(0)
        for j in range(n):
            u=(arb(j)+arb(1)/2)/n
            assert all(0<v<self.pi for v in theta.values())
            s=max(step,min(self.R/2,u/2))
            assert step<=s<self.R
            budget=None;rate=0
            # Near the removable pole of the trigonometric quotient use
            # full precision; the formal interval cancellations are larger.
            if self.adaptive and j>=2:
                rate=math.log2(float(s/step))
                budget=math.ceil(p*math.log2(float(self.R/step)))+256
            # Recenter the initial angle at an exact dyadic midpoint.  The
            # corresponding exact flow is a translated normalized-arclength
            # chart.  By |H|<4 its translation in u is at most
            # 4 |theta-mid|/(pi*ell).  This avoids growing interval radii
            # through artificial complex poles of the trigonometric quotient.
            shifts={k:(4*theta[k].rad()/(self.pi*self.charts[k]['length'])).upper() for k in theta}
            assert all(0<=v<self.R/2 for v in shifts.values())
            Y={k:theta_jet(k,theta[k].mid(),s*self.charts[k]['length'],self.a,self.b,p,budget,rate) for k in theta}
            curv={}
            for k,y in Y.items():
                r,rp,rpp,V,v=geom(k,y,self.a,self.b)
                curv[k]=(r*r+2*rp*rp-r*rpp)/(V*v)
            f=(curv['E']-curv['L'])**2
            w=h/s
            val=sum((f[k]*2*h*w**k/(k+1) for k in range(0,p,2)),arb(0))
            # On the radius-R/2 subdisk, Cauchy bounds |K'| by 70/R.
            # Both curvature differences have absolute value <70, yielding
            # a uniform error for their squares of at most 140*deltaK.
            translation_error=2*h*140*70/self.R*sum(shifts.values(),arb(0))
            total+=val+arb(0,(rem+translation_error).upper())
            if j+1<n:
                # Along the translated real inverse, |theta'|<pi*ell/(6/5).
                theta={k:arb_poly([y[i] for i in range(p)])(step/s)+arb(0,(angle_rem+self.pi*self.charts[k]['length']*shifts[k]/(arb(6)/5)).upper()) for k,y in Y.items()}
            if (j+1)%8==0 or j+1==n:
                print('Continuation panels',j+1,'/',n,'integral radius',total.rad().str(8),'angle accuracy',min(v.rel_accuracy_bits() for v in theta.values()),flush=True)
        assert total>0
        return total.sqrt()


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,default=4096);p.add_argument('--order',type=int,default=512);p.add_argument('--panels',type=int,default=32)
    p.add_argument('--minimum-bits',type=int,default=1000);p.add_argument('--adaptive',action='store_true');p.add_argument('--output',default='m11-dk-continuation.json')
    args=p.parse_args();t=time.monotonic();c=Continuation(args.bits,args.order,args.panels,adaptive=args.adaptive)
    E=c.build_chart('E');L=c.build_chart('L');d=c.integrate_discrepancy()
    assert arb('0.2037837595360494438260805')<d<arb('0.2037837595360494438260815')
    assert d.rel_accuracy_bits()>=args.minimum_bits,(d.rel_accuracy_bits(),args.minimum_bits)
    dt=time.monotonic()-t;peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print('D_kappa continuation',d.str(65),'relative bits',d.rel_accuracy_bits(),'elapsed',dt,'peak RSS KiB',peak,flush=True)
    Path(args.output).write_text(json.dumps({'quantity':'D_kappa, Eq. (50)','method':'validated simultaneous angle continuation','parameters':vars(args),'Eulerian_half_length':exact_endpoints(E),'limacon_half_length':exact_endpoints(L),'discrepancy':exact_endpoints(d),'elapsed_seconds':dt,'peak_rss_kib':peak},indent=2)+'\n')
