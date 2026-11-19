"""M11 direct local speed-square Taylor panels, independent scaling pilot.

The source-locked identity from #383 is
  t^4 F(t) = (5/2)t^2 - (3/2)t^2 cos(t) - 2t sin(t) + 2(1-cos(t)).
At each nonzero panel midpoint c, formal division by t^4 is legitimate;
the apparent singularity at t=0 is removable in the entire F. In contrast
with #410 no global high-degree polynomial or affine composition is required.
The audited zero-free disk |t|<=5 and |sqrt(F)|<4 give the exact Cauchy tail.
"""
import argparse, json, math, resource, time
from pathlib import Path
from flint import arb, arb_series, ctx
from m11_euler_cauchy import analytic_disk, exact_endpoints


def direct_panel(bits, target, panels, index):
    assert bits > target+128 and 0<=index<panels
    analytic_disk()
    ctx.prec=bits
    pi=arb.pi(); h=pi/(2*panels); c=(2*index+1)*h
    rho=h/(5-c)
    assert 0<rho<1 and c>0
    n=max(4,2*math.ceil((target+128)/(-2*math.log2(float(rho)))))
    while 4*rho**n/(1-rho)>=arb(2)**(-target-64): n+=2
    ctx.cap=n
    print('Direct panel',index,'/',panels,'order',n,'rho',rho.str(12),flush=True)
    t=arb_series([c,h],prec=n)
    sn,cs=t.sin_cos()
    t2=t*t
    numerator=(5*t2-3*t2*cs)/2-2*t*sn+2*(1-cs)
    del sn,cs,t
    v=numerator/(t2*t2)
    del numerator,t2
    assert v[0]>0
    s=v.sqrt()
    del v
    assert s.prec==n and s[0]>0
    # Integrate the exact local Taylor coefficients over [-1,1]; the
    # factor 4h accounts for reflection of the original theta interval.
    z=sum((s[j]/(j+1) for j in range(0,n,2)),arb(0))
    tail=16*h*rho**n/(1-rho)
    val=4*h*z+arb(0,tail.upper())
    assert val>0 and val.rel_accuracy_bits()>=target, (index,val.rel_accuracy_bits(),target)
    return val


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,required=True)
    p.add_argument('--target',type=int,required=True);p.add_argument('--panels',type=int,required=True)
    p.add_argument('--index',type=int,required=True);p.add_argument('--compare',action='store_true')
    p.add_argument('--output',required=True);a=p.parse_args();start=time.monotonic()
    val=direct_panel(a.bits,a.target,a.panels,a.index)
    dt=time.monotonic()-start;peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if a.compare:
        from m11_euler_panel import panel
        other=panel(a.bits,a.target,a.panels,a.index)
        assert val.overlaps(other)
        print('Independent original polynomial-panel overlap PASS',flush=True)
    print('DIRECT PANEL PASS',a.index,'relative bits',val.rel_accuracy_bits(),'seconds',dt,'peak RSS KiB',peak,flush=True)
    Path(a.output).write_text(json.dumps({'quantity':'doubled independent Eulerian arclength panel',
        'working_bits':a.bits,'threshold_bits':a.target,'panels':a.panels,'index':a.index,
        'enclosure':exact_endpoints(val),'elapsed_seconds':dt,'peak_rss_kib':peak},indent=2)+'\n')
