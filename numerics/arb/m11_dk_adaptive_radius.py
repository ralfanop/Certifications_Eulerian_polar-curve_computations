"""Validated panel-local inverse radii and variable Taylor orders for M11.

The two-sided phase transport of #399 is retained. Each angular chart uses
an exact dyadic audit of its own neighbourhood, rather than the worst global
inverse radius. Choose the order by an outward Cauchy tail check.
"""
import argparse,json,math,resource,time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from flint import acb,arb,arb_poly,ctx
from m11_dk_twosided import TwoSided,from_endpoints
from m11_dk_continuation import zero_jet
from m11_dk_ode import geom,theta_jet,exact_endpoints
from m11_euler_cauchy import evaluate as length_evaluate


def local_radii():
    ctx.prec=128;pi=arb.pi();b=2*(pi/2).si()/pi;a=2*((3*pi/2).si()-(pi/2).si())/pi
    scale=128;bands=8;levels=[16,24,32,40,48,56]
    mins={k:[[arb(10) for _ in levels] for _ in range(bands)] for k in ('E','L')}
    count=0
    for i in range(-56,scale+56):
        for j in range(-56,56):
            shells=[]
            for band in range(bands):
                d=max(0,16*band-i,i+1-16*(band+1),-j,j+1)
                if d<=56:shells.append((band,next(m for m,L in enumerate(levels) if d<=L)))
            if not shells:continue
            t=pi*acb(arb((arb(i)+arb(1)/2)/scale,arb(1)/(2*scale)),arb((arb(j)+arb(1)/2)/scale,arb(1)/(2*scale)))
            z=-t*t/16;f=z.hypgeom_0f1(arb(5)/2)
            E=(z.hypgeom_0f1(arb(3)/2),-t*f/12,-f/12+t*t*z.hypgeom_0f1(arb(7)/2)/240)
            L=(b+a*t.cos(),-a*t.sin(),-a*t.cos())
            for kind,(r,p,q) in [('E',E),('L',L)]:
                F=r*r+p*p;assert F.real>0,(kind,i,j)
                v=F.sqrt(analytic=True);H=pi*v;K=(r*r+2*p*p-r*q)/(F*v)
                assert H.real>0 and H.abs_upper()<4 and K.abs_upper()<12,(kind,i,j)
                lo=H.real.lower()
                for band,m in shells:mins[kind][band][m]=min(mins[kind][band][m],lo)
                count+=1
    radii={}
    for kind in ('E','L'):
        radii[kind]=[]
        for row in mins[kind]:
            low=arb(10);radial=arb(0)
            for m,L in enumerate(levels):
                low=min(low,row[m]);assert low>0
                radial+=arb(L-(levels[m-1] if m else 0))/scale*low
            # ell<3. Rounding down to a dyadic is only a candidate; the
            # following exact interval comparison is the actual proof.
            R=arb(int(float(radial/3)*256)-1)/256
            assert 0<R<radial/3 and R>=arb(7)/32
            radii[kind].append(R)
    assert pi*(1+arb(7)/16)<5
    print('Local inverse radii',count,'boxes: PASS', {k:[str(x) for x in row] for k,row in radii.items()},flush=True)
    return radii


class Local(TwoSided):
    def __init__(self,bits,target,panels):
        self.target=target;self.radii=local_radii()
        # The inherited uniform radius is used for the translation bound.
        step=arb(1)/panels;R=min(x for row in self.radii.values() for x in row)
        maxorder=self.order_for(R,step)
        super().__init__(bits,maxorder,panels,True)
        self.maxorder=maxorder
        assert bits>=target+maxorder+1024

    def order_for(self,R,step):
        assert 0<step<R
        e=arb(2)**(-self.target-512)
        p=max(4,2*math.ceil((self.target+524)/(2*math.log2(float(R/step)))))
        while not 5*(step/R)**p/(1-step/R)<e:p+=2
        return p

    def build_chart(self,kind):
        if kind=='L':return super().build_chart(kind)
        target=self.target+self.maxorder+768
        assert target<self.bits-128
        length=length_evaluate(self.bits,target)/2
        assert 0<length<3
        self.charts[kind]={'length':length}
        return length

    def radius(self,kind,theta):
        x=theta/self.pi;assert 0<=x<=1 or theta==self.pi
        # Include every band possibly containing the centre, even if the
        # high-precision interval straddles a band edge.
        candidates=[R for j,R in enumerate(self.radii[kind]) if x.lower()<=arb(j+1)/8 and x.upper()>=arb(j)/8]
        assert candidates
        return min(candidates)

    def half(self,direction):
        n=self.panels;h=arb(1)/(2*n);step=2*h
        theta={};phase={};orders=[]
        for k in ('E','L'):
            ell=self.charts[k]['length'];R=self.radii[k][0 if direction==1 else -1];p=self.order_for(R,h)
            ctx.cap=p+5
            if direction==1:y=zero_jet(k,h*ell,self.a,self.b,p)
            else:y=theta_jet(k,self.pi,-h*ell,self.a,self.b,p)
            rem=5*(h/R)**p/(1-h/R)
            ball=sum((y[i] for i in range(p)),arb(0))+arb(0,rem.upper())
            assert 0<ball<self.pi
            theta[k]=ball.mid();phase[k]=(4*ball.rad()/(self.pi*ell)).upper()
        total=arb(0)
        for j in range(n//2):
            u=(arb(j)+arb(1)/2)/n
            if direction==-1:u=1-u
            assert all(0<=v<h/2 for v in phase.values())
            R=min(self.radius(k,theta[k]) for k in theta);p=self.order_for(R,step);orders.append(p);ctx.cap=p+5
            ratio=h/R;advance_ratio=step/R
            rem=2*h*576*ratio**p/((p+1)*(1-ratio));angle_rem=5*advance_ratio**p/(1-advance_ratio)
            s=max(step,min(R/2,u/2));assert step<=s<R
            budget=None;rate=0
            nearzero=direction==1 and j<2
            if not nearzero:
                budget=self.target+1024;rate=math.log2(float(s/step))
            Y={k:theta_jet(k,theta[k],s*self.charts[k]['length'],self.a,self.b,p,budget,rate) for k in theta}
            try:
                if not nearzero:ctx.prec=min(self.bits,self.target+2048)
                curv={}
                for k,y in Y.items():
                    r,rp,rpp,V,v=geom(k,y,self.a,self.b);curv[k]=(r*r+2*rp*rp-r*rpp)/(V*v)
                f=(curv['E']-curv['L'])**2;w=h/s
                val=sum((f[k]*2*h*w**k/(k+1) for k in range(0,p,2)),arb(0))
            finally:ctx.prec=self.bits
            # Use the uniform certified radius for comparisons with the
            # unshifted argument; local radii bound the shifted jets only.
            trans=2*h*48*24/self.R*sum(phase.values(),arb(0))
            total+=val+arb(0,(rem+trans).upper())
            if j+1<n//2:
                for k,y in Y.items():
                    ball=arb_poly([y[i] for i in range(p)])(direction*step/s)+arb(0,angle_rem.upper())
                    assert 0<ball<self.pi
                    theta[k]=ball.mid();phase[k]=(phase[k]+4*ball.rad()/(self.pi*self.charts[k]['length'])).upper()
            print('Local half',direction,'panel',j+1,'/',n//2,'R',R.str(8),'order',p,'radius',total.rad().str(8),flush=True)
        assert total>0
        return total,orders


def work(args,direction):
    t=time.monotonic();c=Local(args.bits,args.target,args.panels)
    E=c.build_chart('E');L=c.build_chart('L');v,orders=c.half(direction)
    return {'direction':direction,'orders':orders,'integral':exact_endpoints(v),'Eulerian_half_length':exact_endpoints(E),'limacon_half_length':exact_endpoints(L),'elapsed_seconds':time.monotonic()-t,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,default=4096);p.add_argument('--target',type=int,default=1000);p.add_argument('--panels',type=int,default=32);p.add_argument('--output',default='m11-dk-local.json')
    mode=p.add_mutually_exclusive_group();mode.add_argument('--parallel',action='store_true');mode.add_argument('--direction',type=int,choices=(-1,1));mode.add_argument('--combine',nargs=2)
    args=p.parse_args();t=time.monotonic();params={k:getattr(args,k) for k in ('bits','target','panels')}
    if args.direction is not None:
        half=work(args,args.direction)
        Path(args.output).write_text(json.dumps({'parameters':params,'half':half},indent=2)+'\n')
        print('Half',args.direction,'completed',half['elapsed_seconds'],'peak RSS KiB',half['peak_rss_kib'],flush=True)
        raise SystemExit(0)
    if args.combine:
        inputs=[json.loads(Path(path).read_text()) for path in args.combine]
        assert all(x['parameters']==params for x in inputs)
        halves=[x['half'] for x in inputs]
    elif args.parallel:
        with ProcessPoolExecutor(max_workers=2) as ex:
            fut=[ex.submit(work,args,d) for d in (1,-1)];halves=[f.result() for f in fut]
    else:halves=[work(args,d) for d in (1,-1)]
    assert sorted(x['direction'] for x in halves)==[-1,1]
    assert all(len(x['orders'])==args.panels//2 for x in halves)
    ctx.prec=args.bits
    for name in ('Eulerian_half_length','limacon_half_length'):
        assert from_endpoints(halves[0][name]).overlaps(from_endpoints(halves[1][name]))
    integrals=[from_endpoints(x['integral']) for x in halves]
    assert all(v>0 for v in integrals)
    d=sum(integrals,arb(0)).sqrt()
    assert arb('0.2037837595360494438260805')<d<arb('0.2037837595360494438260815')
    assert d.rel_accuracy_bits()>=args.target,(d.rel_accuracy_bits(),args.target)
    dt=time.monotonic()-t
    print('D_kappa local radii',d.str(65),'relative bits',d.rel_accuracy_bits(),'elapsed',dt,'worker peak RSS KiB',max(x['peak_rss_kib'] for x in halves),flush=True)
    Path(args.output).write_text(json.dumps({'quantity':'D_kappa, Eq. (50)','method':'panel-local inverse radius, additive phase continuation','parameters':params,'halves':halves,'discrepancy':exact_endpoints(d),'elapsed_seconds':dt},indent=2)+'\n')
