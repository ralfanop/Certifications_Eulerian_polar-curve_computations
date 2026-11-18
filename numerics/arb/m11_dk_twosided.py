"""M11 curvature discrepancy: wider inverse disks and bidirectional flow.

The phase (normalized-arclength translation) error adds rather than wraps
through interval initial values. Two independent exact endpoint starts
allow the integrations on the two halves to run in separate processes.
"""
import argparse,json,math,resource,time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from flint import acb,arb,arb_poly,fmpq,ctx
from m11_dk_continuation import Continuation,zero_jet
from m11_dk_ode import geom,theta_jet,exact_endpoints


def wide_strip():
    ctx.prec=128;pi=arb.pi();b=2*(pi/2).si()/pi;a=2*((3*pi/2).si()-(pi/2).si())/pi
    scale=128;levels=[16,24,32,40,48,56]
    lower=[arb(9)/5,arb(17)/10,arb(31)/20,arb(7)/5,arb(5)/4,arb(11)/10]
    # Tiling of [-7/16, 1+7/16] + i[-7/16, 7/16]. Assign each tile to
    # the smallest enclosing nested rectangle. Bounds include tile edges.
    count=0
    for i in range(-56,scale+56):
        for j in range(-56,56):
            d=max(0,-i,i+1-scale,-j,j+1)
            m=next(k for k,L in enumerate(levels) if d<=L)
            t=pi*acb(arb((arb(i)+arb(1)/2)/scale,arb(1)/(2*scale)),arb((arb(j)+arb(1)/2)/scale,arb(1)/(2*scale)))
            z=-t*t/16;f=z.hypgeom_0f1(arb(5)/2)
            E=(z.hypgeom_0f1(arb(3)/2),-t*f/12,-f/12+t*t*z.hypgeom_0f1(arb(7)/2)/240)
            L=(b+a*t.cos(),-a*t.sin(),-a*t.cos())
            for r,p,q in (E,L):
                F=r*r+p*p;assert F.real>0,(i,j)
                v=F.sqrt(analytic=True);H=pi*v;K=(r*r+2*p*p-r*q)/(F*v)
                assert H.real>lower[m] and H.abs_upper()<4,(i,j,m)
                assert K.abs_upper()<12,(i,j)
                count+=1
    radial=sum((arb(L-(levels[m-1] if m else 0))/scale*lower[m] for m,L in enumerate(levels)),arb(0))
    assert radial/3>arb(7)/32 and pi*(1+arb(7)/16)<5
    print('Wide inverse strip',count,'boxes; radial lower bound',radial.str(12),'R=7/32: PASS',flush=True)


class TwoSided(Continuation):
    def __init__(self,bits,order,panels,adaptive):
        super().__init__(bits,order,panels,adaptive=adaptive)
        wide_strip();ctx.prec=bits;ctx.cap=order+5
        self.R=arb(7)/32

    def half(self,direction):
        p,n=self.order,self.panels;h=arb(1)/(2*n);step=2*h
        assert n%2==0 and step<self.R
        ratio=h/self.R;advance_ratio=step/self.R
        rem=2*h*576*ratio**p/((p+1)*(1-ratio))
        angle_rem=5*advance_ratio**p/(1-advance_ratio)
        first_rem=5*ratio**p/(1-ratio)
        ctx.cap=p+5
        theta={};phase={}
        for k in ('E','L'):
            ell=self.charts[k]['length'];assert 0<ell<3
            if direction==1:y=zero_jet(k,h*ell,self.a,self.b,p)
            else:y=theta_jet(k,self.pi,-h*ell,self.a,self.b,p)
            ball=sum((y[i] for i in range(p)),arb(0))+arb(0,first_rem.upper())
            assert 0<ball<self.pi
            theta[k]=ball.mid();phase[k]=(4*ball.rad()/(self.pi*ell)).upper()
        total=arb(0)
        for j in range(n//2):
            u=(arb(j)+arb(1)/2)/n
            if direction==-1:u=1-u
            assert all(0<=v<h/2 for v in phase.values())
            s=max(step,min(self.R/2,u/2));assert step<=s<self.R
            budget=None;rate=0
            if self.adaptive and (direction==-1 or j>=2):
                rate=math.log2(float(s/step));budget=math.ceil(p*math.log2(float(self.R/step)))+256
            Y={k:theta_jet(k,theta[k],s*self.charts[k]['length'],self.a,self.b,p,budget,rate) for k in theta}
            curv={}
            for k,y in Y.items():
                r,rp,rpp,V,v=geom(k,y,self.a,self.b);curv[k]=(r*r+2*rp*rp-r*rpp)/(V*v)
            f=(curv['E']-curv['L'])**2;w=h/s
            val=sum((f[k]*2*h*w**k/(k+1) for k in range(0,p,2)),arb(0))
            # |K|<12, so |K'|<=24/R on the half-disk; both curvature
            # differences have modulus <24. Phase shifts are independent.
            trans=2*h*48*24/self.R*sum(phase.values(),arb(0))
            total+=val+arb(0,(rem+trans).upper())
            if j+1<n//2:
                for k,y in Y.items():
                    ball=arb_poly([y[i] for i in range(p)])(direction*step/s)+arb(0,angle_rem.upper())
                    assert 0<ball<self.pi
                    theta[k]=ball.mid()
                    # The exact normalized-arclength displacement caused by
                    # recentering is at most 4*radius/(pi*ell). Autonomous
                    # flow preserves the previous displacement exactly.
                    phase[k]=(phase[k]+4*ball.rad()/(self.pi*self.charts[k]['length'])).upper()
            if (j+1)%4==0 or j+1==n//2:
                print('Half',direction,'panels',j+1,'/',n//2,'radius',total.rad().str(8),flush=True)
        assert total>0
        return total


def work(args,direction):
    t=time.monotonic();c=TwoSided(args.bits,args.order,args.panels,args.adaptive)
    E=c.build_chart('E');L=c.build_chart('L');v=c.half(direction)
    return {'direction':direction,'integral':exact_endpoints(v),'Eulerian_half_length':exact_endpoints(E),'limacon_half_length':exact_endpoints(L),'elapsed_seconds':time.monotonic()-t,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def from_endpoints(e):
    lo,hi=(fmpq(int(e[k]['numerator']),int(e[k]['denominator'])) for k in ('lower','upper'))
    assert lo<=hi
    ball=arb((lo+hi)/2,arb((hi-lo)/2).upper())
    assert ball.lower().fmpq()<=lo and ball.upper().fmpq()>=hi
    return ball


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,default=4096);p.add_argument('--order',type=int,default=512);p.add_argument('--panels',type=int,default=32);p.add_argument('--minimum-bits',type=int,default=1000);p.add_argument('--adaptive',action='store_true');p.add_argument('--parallel',action='store_true');p.add_argument('--output',default='m11-dk-twosided.json');args=p.parse_args();t=time.monotonic()
    if args.parallel:
        with ProcessPoolExecutor(max_workers=2) as ex:
            fut=[ex.submit(work,args,d) for d in (1,-1)];halves=[f.result() for f in fut]
    else:halves=[work(args,d) for d in (1,-1)]
    ctx.prec=args.bits;d=sum((from_endpoints(x['integral']) for x in halves),arb(0)).sqrt()
    assert arb('0.2037837595360494438260805')<d<arb('0.2037837595360494438260815')
    assert d.rel_accuracy_bits()>=args.minimum_bits,(d.rel_accuracy_bits(),args.minimum_bits)
    dt=time.monotonic()-t
    print('D_kappa two-sided',d.str(65),'relative bits',d.rel_accuracy_bits(),'elapsed',dt,'worker peak RSS KiB',max(x['peak_rss_kib'] for x in halves),flush=True)
    Path(args.output).write_text(json.dumps({'quantity':'D_kappa, Eq. (50)','method':'two-sided phase continuation, wider inverse disks','parameters':vars(args),'halves':halves,'discrepancy':exact_endpoints(d),'elapsed_seconds':dt},indent=2)+'\n')
