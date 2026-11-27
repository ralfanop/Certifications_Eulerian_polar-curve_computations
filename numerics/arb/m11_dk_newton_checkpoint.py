"""M11 only: exact dyadic Newton checkpoints for the two initial angle jets.

Each stage runs in a separate job; coefficient enclosures, not midpoints,
are persisted. The original Cauchy tail and final decimal gate are unchanged.
"""
import argparse,gzip,hashlib,json,os,sys,time,resource
from pathlib import Path
from flint import arb,fmpq,ctx
from m11_dk_adaptive_radius import Local,from_endpoints,exact_endpoints
from m11_dk_ode import theta_jet
from m11_dk_continuation import zero_jet

if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def digest(path):
    with open(path,'rb') as f:
        return hashlib.file_digest(f,'sha256').hexdigest()

def pack(x):
    assert x.is_finite()
    def dyadic(y):
        q=y.fmpq(); den=int(q.q)
        assert den>0 and den&(den-1)==0
        return [hex(int(q.p)),den.bit_length()-1]
    return [dyadic(x.lower()),dyadic(x.upper())]

def unpack(row):
    def rational(v):
        return fmpq(int(v[0],16),1<<v[1])
    lo,hi=map(rational,row)
    assert lo<=hi
    x=arb((lo+hi)/2,arb((hi-lo)/2).upper())
    assert x.lower().fmpq()<=lo and x.upper().fmpq()>=hi
    return x

def write_coeffs(path,meta,coeffs):
    temp=Path(str(path)+'.tmp')
    with gzip.open(temp,'wt',compresslevel=1) as f:
        f.write(json.dumps(meta)+'\n')
        for x in coeffs:
            f.write(json.dumps(pack(x),separators=(',',':'))+'\n')
    os.replace(temp,path)

def read_coeffs(path,identity):
    with gzip.open(path,'rt') as f:
        meta=json.loads(next(f))
        assert meta['identity']==identity
        coeffs=[unpack(json.loads(line)) for line in f]
    assert len(coeffs)==meta['degree']
    return meta,coeffs

def config(args):
    c=Local(args.bits,args.target,args.panels,args.length)
    E=c.build_chart('E'); L=c.build_chart('L')
    print('Length inputs',E.rel_accuracy_bits(),L.rel_accuracy_bits(),flush=True)
    return c

def identity(args,c,kind):
    h=arb(1)/(2*c.panels)
    R=c.radii[kind][0 if args.direction==1 else -1]
    p=c.order_for(R,h)
    return dict(bits=args.bits,target=args.target,panels=args.panels,
                direction=args.direction,kind=kind,order=p,
                source=c.historical_euler_source,
                head=os.environ.get('M11_PRODUCER_HEAD','local-test'))

def produce(args):
    c=config(args)
    meta=identity(args,c,args.kind)
    p=meta['order']; h=arb(1)/(2*c.panels)
    ell=c.charts[args.kind]['length']
    R=c.radii[args.kind][0 if args.direction==1 else -1]
    degree=p if args.degree=='full' else min(p,int(args.degree))
    ctx.cap=p+5
    coeffs=None; parent=None
    if args.resume:
        previous,coeffs=read_coeffs(args.resume,meta)
        assert 2<=len(coeffs)<=degree
        parent=digest(args.resume)
    started=time.monotonic()
    print('Newton stage',args.direction,args.kind,'from',len(coeffs or []),'to',degree,'of',p,flush=True)
    if args.direction==1:
        y=zero_jet(args.kind,h*ell,c.a,c.b,degree,initial_coeffs=coeffs)
    else:
        y=theta_jet(args.kind,c.pi,-h*ell,c.a,c.b,degree,initial_coeffs=coeffs)
    del coeffs
    print('Newton stage done seconds',time.monotonic()-started,
          'RSS KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
    if args.degree!='full':
        write_coeffs(args.output,dict(identity=meta,degree=degree,parent_sha256=parent),
                     (y[i] for i in range(degree)))
    else:
        assert degree==p
        rem=5*(h/R)**p/(1-h/R)
        ball=sum((y[i] for i in range(p)),arb(0))+arb(0,rem.upper())
        assert 0<ball<c.pi
        phase=(4*ball.rad()/(c.pi*ell)).upper()
        assert 0<=phase<h/2
        Path(args.output).write_text(json.dumps(dict(identity=meta,
            degree=p,parent_sha256=parent,theta=exact_endpoints(ball.mid()),
            phase=exact_endpoints(phase)),indent=2)+'\n')

def combine(args):
    c=config(args)
    theta={};phase={};parents={}
    for kind,path in [('E',args.euler),('L',args.limacon)]:
        x=json.loads(Path(path).read_text())
        meta=identity(args,c,kind)
        assert x['identity']==meta and x['degree']==meta['order']
        t=from_endpoints(x['theta']); q=from_endpoints(x['phase']).upper()
        assert t.is_exact() and 0<t<c.pi and 0<=q<arb(1)/(4*c.panels)
        theta[kind]=exact_endpoints(t);phase[kind]=exact_endpoints(q)
        parents[kind]=digest(path)
    params=dict(bits=args.bits,target=args.target,panels=args.panels)
    checkpoint=dict(**params,direction=args.direction,next_panel=0,orders=[],
        theta=theta,phase=phase,partial_integral=exact_endpoints(arb(0)),
        Eulerian_half_length=exact_endpoints(c.charts['E']['length']),
        limacon_half_length=exact_endpoints(c.charts['L']['length']),
        historical_euler_source=c.historical_euler_source)
    Path(args.output).write_text(json.dumps(dict(parameters=params,
        checkpoint=checkpoint,starter_sha256=parents),indent=2)+'\n')
    print('M11 validated starter checkpoint',args.direction,flush=True)

def smoke():
    ctx.prec=256;ctx.cap=40
    a,b=arb(1)/10,arb(1);scale=arb(1)/256
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        for direction in (1,-1):
            for kind in ('E','L'):
                def calc(n,prev=None):
                    if direction==1:return zero_jet(kind,scale,a,b,n,initial_coeffs=prev)
                    return theta_jet(kind,arb.pi(),-scale,a,b,n,initial_coeffs=prev)
                x=calc(8); path=Path(td)/'test.gz';meta={'kind':kind,'direction':direction}
                write_coeffs(path,dict(identity=meta,degree=8),(x[i] for i in range(8)))
                _,coeffs=read_coeffs(path,meta)
                y=calc(16,coeffs); z=calc(16)
                assert all(y[i].overlaps(z[i]) for i in range(16))
    print('M11 Newton exact-endpoint restart smoke PASS',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--smoke',action='store_true')
    p.add_argument('--bits',type=int,default=150000)
    p.add_argument('--target',type=int,default=100100)
    p.add_argument('--panels',type=int,default=128)
    p.add_argument('--length')
    p.add_argument('--direction',type=int,choices=[1,-1])
    p.add_argument('--kind',choices=['E','L'])
    p.add_argument('--degree',default='full')
    p.add_argument('--resume')
    p.add_argument('--euler')
    p.add_argument('--limacon')
    p.add_argument('--output')
    args=p.parse_args()
    if args.smoke:smoke()
    elif args.euler and args.limacon:combine(args)
    else:produce(args)
