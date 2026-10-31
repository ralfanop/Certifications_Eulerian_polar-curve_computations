from pathlib import Path
import json,time
import mpmath as mp
mp.mp.dps=60
pi=mp.pi;b=2/pi*mp.si(pi/2);a=2/pi*(mp.si(3*pi/2)-mp.si(pi/2))
def geom(t,kind):
    if kind=="E":
        if abs(t)<mp.mpf("0.1"):
            z=-t*t/16
            r=mp.hyp0f1(mp.mpf(3)/2,z)
            rp=-t/12*mp.hyp0f1(mp.mpf(5)/2,z)
            rpp=-mp.hyp0f1(mp.mpf(5)/2,z)/12+t*t*mp.hyp0f1(mp.mpf(7)/2,z)/240
        else:
            s=mp.sin(t/2);c=mp.cos(t/2)
            r=2*s/t;rp=c/t-2*s/t**2;rpp=-s/(2*t)-2*c/t**2+4*s/t**3
    else:r=b+a*mp.cos(t);rp=-a*mp.sin(t);rpp=-a*mp.cos(t)
    v=mp.sqrt(r*r+rp*rp)
    return v,(r*r+2*rp*rp-r*rpp)/v**3
def arc(t,k):
    return mp.quadgl(lambda z:geom(z,k)[0],[0,t],maxdegree=7)
ell={k:arc(pi,k) for k in ["E","L"]}
print("Lengths",ell,flush=True)
def inverse(u,k):
    t=pi*u
    for _ in range(12):
        res=arc(t,k)-u*ell[k]
        delta=res/geom(t,k)[0]
        t-=delta
        if abs(delta)<mp.mpf("1e-52"):return t
    raise RuntimeError("Newton did not converge")
results=[];start=time.time()
for N in [32,48,64]:
    nodes,weights=mp.gauss_quadrature(N,"legendre")
    total=mp.mpf(0)
    for j in range(N):
        u=(nodes[j]+1)/2
        te=inverse(u,"E");tl=inverse(u,"L")
        total+=weights[j]/2*(geom(te,"E")[1]-geom(tl,"L")[1])**2
        if (j+1)%16==0:print("Reference",N,j+1,flush=True)
    d=mp.sqrt(total)
    row={"gauss_order":N,"D":str(d),"D_squared":str(total)}
    results.append(row);print(row,flush=True)
data={"qualification":"Independent high-precision quadrature corroboration only; not an interval certificate.",
      "method":"Direct Gauss-Legendre quadrature with Newton inversion of independently integrated arclength",
      "dps":mp.mp.dps,"half_lengths":{k:str(v) for k,v in ell.items()},
      "results":results,"seconds":time.time()-start}
Path("DIRECT_REFERENCE_CHECK.json").write_text(json.dumps(data,indent=2)+"\n")
