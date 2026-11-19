"""Bounded-memory direct Taylor panels for M11.

Each coefficient block is independently enclosed at a chosen Arb
precision. A larger local coordinate scale makes the integration weight
geometrically small, permitting reduced precision for later blocks.
Precision allocation is a heuristic ONLY: outward ball propagation and
the final relative-bit assertion determine success. No coefficient is
discarded except via the independently audited analytic Cauchy tail.
"""
import argparse, json, math, resource, time
from pathlib import Path
from flint import arb, arb_series, ctx
from m11_euler_cauchy import analytic_disk, exact_endpoints


def origin_series(s,n):
    # Exact coefficients in y=(theta/s)^2, from the audited identity.
    a=arb(1)/24; cs=[]
    for k in range(n):
        m=2*k+4
        cs.append(a*((3*m*(m-1))//2+2*m-2))
        a=-s*s*a/((m+1)*(m+2))
    return arb_series(cs,prec=n).sqrt()


def local_series(c,s,n):
    # Division at a nonzero midpoint is legitimate at every finite order.
    # Use s<=c/2 to suppress the propagation of interval errors.
    t=arb_series([c,s],prec=n)
    sn,co=t.sin_cos(); t2=t*t
    num=(5*t2-3*t2*co)/2-2*t*sn+2*(1-co)
    del sn,co,t
    v=num/(t2*t2)
    del num,t2
    assert v[0]>0
    return v.sqrt()


def blocked_panel(bits,target,panels,index,blocks):
    assert bits>target+256 and 0<=index<panels and blocks>=2
    analytic_disk(); ctx.prec=bits
    pi=arb.pi(); h=pi/(2*panels); a=2*index*h; b=2*(index+1)*h; c=a+h
    origin=b<1
    if origin:
        # On the first panels use the even series at zero, avoiding an
        # artificial near-zero denominator and allowing a fixed large scale.
        s=arb(5)/2; u=a/s; v=b/s
        rho=(b/5)**2; weight=(b/s)**2
    else:
        s=c/2 if c<arb(5)/2 else (5-c)/2
        assert 0<s<c
        w=h/s;rho=h/(5-c);weight=w
    assert 0<rho<1 and 0<weight<1
    n=max(4,2*math.ceil((target+128)/(-2*math.log2(float(rho)))))
    # Cauchy: |sqrt F|<4 on |theta|<=5, exact remainder after n terms.
    while 16*h*rho**n/(1-rho)>=arb(2)**(-target-64):n+=2
    decay=math.log2(float(1/weight));total=arb(0)
    print('BLOCKED',index,'order',n,'origin',origin,'weight',weight.str(12),flush=True)
    for block in range(blocks):
        lo=n*block//blocks; hi=n*(block+1)//blocks
        if lo==hi:continue
        p=max(256,bits-int(lo*decay))
        try:
            ctx.prec=p;ctx.cap=hi
            S=origin_series(s,hi) if origin else local_series(c,s,hi)
            assert S.prec==hi and S[0]>0
            part=arb(0)
            if origin:
                up=v**(2*lo+1);down=u**(2*lo+1);u2=u*u;v2=v*v
                for k in range(lo,hi):
                    part+=S[k]*(up-down)/(2*k+1)
                    up*=v2;down*=u2
                part*=2*s
            else:
                k=lo+(lo%2);z=w**k;w2=w*w
                while k<hi:
                    part+=S[k]*z/(k+1);z*=w2;k+=2
                part*=4*h
            del S
        finally:ctx.prec=bits
        total+=part
        print('block',block+1,'/',blocks,'order',hi,'precision',p,'radius',total.rad().str(8),'peak RSS KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
    tail=16*h*rho**n/(1-rho)
    val=total+arb(0,tail.upper())
    assert val>0 and val.rel_accuracy_bits()>=target,(index,val.rel_accuracy_bits(),target)
    return val


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,required=True)
    p.add_argument('--target',type=int,required=True);p.add_argument('--panels',type=int,required=True)
    p.add_argument('--index',type=int,required=True);p.add_argument('--blocks',type=int,default=16)
    p.add_argument('--compare',action='store_true');p.add_argument('--output',required=True)
    a=p.parse_args();start=time.monotonic();val=blocked_panel(a.bits,a.target,a.panels,a.index,a.blocks)
    dt=time.monotonic()-start;peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if a.compare:
        from m11_euler_direct_panel import direct_panel
        ref=direct_panel(a.bits,a.target,a.panels,a.index)
        assert ref.overlaps(val)
        print('Independent direct-panel overlap PASS',flush=True)
    print('BLOCKED PANEL PASS',a.index,'relative bits',val.rel_accuracy_bits(),'seconds',dt,'peak RSS KiB',peak,flush=True)
    Path(a.output).write_text(json.dumps({'quantity':'doubled independent Eulerian arclength panel',
        'working_bits':a.bits,'threshold_bits':a.target,'panels':a.panels,'index':a.index,
        'enclosure':exact_endpoints(val),'elapsed_seconds':dt,'peak_rss_kib':peak},indent=2)+'\n')
