"""Validated panel-local inverse radii and variable Taylor orders for M11.

The two-sided phase transport of #399 is retained. Each angular chart uses
an exact dyadic audit of its own neighbourhood, rather than the worst global
inverse radius. Choose the order by an outward Cauchy tail check.
"""
import argparse,hashlib,json,math,resource,time,sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from flint import acb,arb,arb_poly,ctx
from m11_dk_twosided import TwoSided,from_endpoints
from m11_dk_continuation import zero_jet
from m11_dk_ode import geom,theta_jet,exact_endpoints
from m11_euler_cauchy import evaluate as length_evaluate

# Exact rational Arb endpoints exceed Python 3.11+'s default 4300-digit
# integer-string limit at the required 20,000-decimal output precision.
# This only lifts a serialization guard; interval rigor is unchanged.
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


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
    def __init__(self,bits,target,panels,certified_length_manifest=None):
        self.target=target
        self.certified_length_manifest=certified_length_manifest
        self.historical_euler_source=None
        self.radii=local_radii()
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
        if self.certified_length_manifest is None:
            length=length_evaluate(self.bits,target)/2
        else:
            # Source: full Eulerian length, CI 44359739062 (32 panels).
            # Its exact 20,000-decimal cell was separately re-audited by
            # workflow m11-20000-length-reaudit.yml. Never relabel the
            # historical CI as a new-HEAD numerical computation.
            raw=Path(self.certified_length_manifest).read_bytes()
            digest=hashlib.sha256(raw).hexdigest()
            expected="a606d305f7d4c773695cee61cf56268022ec9cc5525f689f301e8822f22fe7b5"
            if digest!=expected:
                raise ValueError("historical full Eulerian length manifest SHA256 mismatch")
            manifest=json.loads(raw)
            if (manifest.get("working_bits"),manifest.get("threshold_bits"),
                    manifest.get("panels"),manifest.get("index"))!=(110000,100000,32,None):
                raise ValueError("historical complete length manifest parameters mismatch")
            length=from_endpoints(manifest["enclosure"])/2
            if length.rel_accuracy_bits()<target:
                raise ValueError("historical full length interval not accurate enough for inverse-ODE Cauchy tail")
            self.historical_euler_source={
                "source_ci":44359739062,
                "source_head_sha":"6ddb354a85832bf5b35538996d7d619c63ac9a16",
                "manifest_sha256":digest,
                "reported_original_relative_bits":manifest["enclosure"].get("relative_bits"),
            }
            print("Reused exact historical 100k full Eulerian length interval",
                  "needed inverse-ODE chart bits",target,flush=True)
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

    def half(self,direction,resume=None,stop_after=None):
        n=self.panels;h=arb(1)/(2*n);step=2*h
        end=n//2 if stop_after is None else stop_after
        assert 0<end<=n//2 and direction in (-1,1)
        self.checkpoint_state=None
        if resume is None:
            start=0;theta={};phase={};orders=[]
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
        else:
            start=resume['next_panel']
            assert isinstance(start,int) and 0<start<end
            assert (resume['bits'],resume['target'],resume['panels'],resume['direction'])==(self.bits,self.target,n,direction)
            assert resume.get('historical_euler_source')==self.historical_euler_source
            orders=resume['orders'][:]
            assert len(orders)==start and all(isinstance(o,int) and o>0 for o in orders)
            # Each saved state is an outward exact-rational enclosure.
            # Restore the angle as its exact midpoint and phase as an upper bound.
            # Conservatively re-enclose the accumulated integral.
            theta={k:from_endpoints(resume['theta'][k]) for k in ('E','L')}
            assert all(x.is_exact() for x in theta.values())
            phase={k:from_endpoints(resume['phase'][k]).upper() for k in ('E','L')}
            total=from_endpoints(resume['partial_integral'])
            assert all(0<theta[k]<self.pi and 0<=phase[k]<h/2 for k in ('E','L'))
            for k,key in (('E','Eulerian_half_length'),('L','limacon_half_length')):
                assert self.charts[k]['length'].overlaps(from_endpoints(resume[key]))
            print('Resuming certified curvature',direction,'from panel',start,
                  'checkpoint interval radius',total.rad().str(8),flush=True)
        for j in range(start,end):
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
        if end<n//2:
            self.checkpoint_state={
                'bits':self.bits,'target':self.target,'panels':n,'direction':direction,
                'next_panel':end,'orders':orders,
                'theta':{k:exact_endpoints(theta[k]) for k in ('E','L')},
                'phase':{k:exact_endpoints(phase[k]) for k in ('E','L')},
                'partial_integral':exact_endpoints(total),
                'Eulerian_half_length':exact_endpoints(self.charts['E']['length']),
                'limacon_half_length':exact_endpoints(self.charts['L']['length']),
                'historical_euler_source':self.historical_euler_source,
            }
            print('Exact outward-rational checkpoint at',end,'/',n//2,
                  'for curvature direction',direction,flush=True)
        return total,orders


def work(args,direction):
    t=time.monotonic();c=Local(args.bits,args.target,args.panels,args.certified_length_manifest)
    E=c.build_chart('E');L=c.build_chart('L')
    resume=None;source_digest=None
    if getattr(args,'resume',None) is not None:
        raw=Path(args.resume).read_bytes()
        source_digest=hashlib.sha256(raw).hexdigest()
        source=json.loads(raw)
        if source['parameters'] != {k:getattr(args,k) for k in ('bits','target','panels')}:
            raise ValueError('checkpoint numerical parameter mismatch')
        resume=source['checkpoint']
    v,orders=c.half(direction,resume,getattr(args,'stop_after',None))
    result={'direction':direction,'orders':orders,'integral':exact_endpoints(v),'Eulerian_half_length':exact_endpoints(E),'limacon_half_length':exact_endpoints(L),'elapsed_seconds':time.monotonic()-t,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    if c.checkpoint_state is not None:
        result['checkpoint']=c.checkpoint_state
        result['checkpoint_parent_sha256']=source_digest
    if c.historical_euler_source is not None:
        result['historical_euler_source']=c.historical_euler_source
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,default=4096);p.add_argument('--target',type=int,default=1000);p.add_argument('--panels',type=int,default=32);p.add_argument('--output',default='m11-dk-local.json')
    p.add_argument('--certified-length-manifest',default=None,help='Historical successful complete 32-panel Eulerian length manifest; SHA256 pinned')
    p.add_argument('--resume',default=None,help='Prior exact interval checkpoint, same parameters and direction')
    p.add_argument('--stop-after',type=int,default=None,help='Stop after this absolute half-panel number and emit exact checkpoint')
    mode=p.add_mutually_exclusive_group();mode.add_argument('--parallel',action='store_true');mode.add_argument('--direction',type=int,choices=(-1,1));mode.add_argument('--combine',nargs=2)
    args=p.parse_args();t=time.monotonic();params={k:getattr(args,k) for k in ('bits','target','panels')}
    if args.direction is not None:
        half=work(args,args.direction)
        if 'checkpoint' in half:
            payload={'parameters':params,'checkpoint':half.pop('checkpoint'),
                     'checkpoint_parent_sha256':half.pop('checkpoint_parent_sha256'),
                     'elapsed_seconds':half['elapsed_seconds'],
                     'peak_rss_kib':half['peak_rss_kib']}
            print('Half',args.direction,'safely checkpointed',payload['checkpoint']['next_panel'],
                  'of',args.panels//2,'panels',flush=True)
        else:
            payload={'parameters':params,'half':half}
            print('Half',args.direction,'completed',half['elapsed_seconds'],
                  'peak RSS KiB',half['peak_rss_kib'],flush=True)
        Path(args.output).write_text(json.dumps(payload,indent=2)+'\n')
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
    source_tags=[x.get('historical_euler_source') for x in halves]
    if any(tag is not None for tag in source_tags):
        assert source_tags[0] is not None and source_tags[0]==source_tags[1], "historical Euler length origins must agree"
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
