"""Memory-bounded block convolution for rigorous Eulerian arclength.

If P is the rigorously truncated speed-square polynomial (P(0)=1),
S=sqrt(P) solves 2 P S'=P' S. Scaled t_n=S_n q^n then satisfy an exact
finite-width linear recurrence. Block convolutions need only the last
deg(P) values, never the entire square-root Taylor series.
"""
import argparse,time,json,math,resource
from pathlib import Path
from flint import arb,arb_poly,ctx
from m11_euler_cauchy import analytic_disk,exact_endpoints

def scaled_speed_polynomial(target):
    pi=arb.pi();q=pi*pi/25;eta=arb(2)**(-target-40)
    assert 0<q<arb('0.4') and eta<arb(1)/128 and 4/pi**2-eta>arb(1)/4
    p=[arb(1)];a=-25*arb(1)/(24*5*6);qk=q;k=1
    while True:
        m=2*k+4;term=a*((3*m*(m-1))//2+2*m-2)
        if k>=5 and 2*term.abs_upper()<eta:break
        p.append(term*qk);a=-25*a/((m+1)*(m+2));qk*=q;k+=1
    return pi,q,eta,p

def middle_products(a,hist,size,chunk):
    # Only size coefficients of the convolution are needed. Partition the
    # kernel and the compatible history window, so no full-width product
    # is ever materialized. All arithmetic stays in Arb balls.
    n=len(hist);K=len(a)-1;C=[arb(0)]*size;D=[arb(0)]*size
    for j0 in range(1,K+1,chunk):
        j1=min(K+1,j0+chunk)
        l=max(0,n-(j1-1));r=min(n,n+size-j0)
        if l>=r:continue
        H=arb_poly(hist[l:r]);P=arb_poly(a[j0:j1])
        J=arb_poly([j*a[j] for j in range(j0,j1)])
        c=P*H;d=J*H
        for k in range(size):
            idx=n+k-j0-l
            if idx>=0:
                C[k]+=c[idx];D[k]+=d[idx]
    return C,D

def evaluate(bits,target,block,adaptive=False,kernel_chunk=0):
    analytic_disk();ctx.prec=bits
    pi,q,eta,a=scaled_speed_polynomial(target)
    N=(target+20)*25//33+2
    assert 8*pi*q**N/(1-q)<arb(2)**(-target-4)
    K=len(a)-1;assert K>=1 and block>=1
    # Two fixed kernels. P0 omitted because the recurrence isolates t_n.
    if not kernel_chunk:
        P=arb_poly([arb(0)]+a[1:]);J=arb_poly([arb(0)]+[j*a[j] for j in range(1,K+1)])
    hist=[arb(1)];result=arb(1);start=1
    print('Required terms',N,'recurrence width',K,'block',block,flush=True)
    while start<N:
        size=min(block,N-start)
        # Relative precision of later scaled coefficients may decrease;
        # the final sum still uses full precision. No accuracy is presumed.
        if adaptive:ctx.prec=max(256,bits-int(0.8*start*math.log2(float(1/q))))
        try:
            if kernel_chunk:
                C,D=middle_products(a,hist,size,kernel_chunk)
                offset=0
            else:
                H=arb_poly(hist);C=P*H;D=J*H
                offset=len(hist)
            fresh=[];partial=arb(0)
            for k in range(size):
                n=start+k;idx=offset+k
                v=3*D[idx]-2*n*C[idx]
                for j in range(1,min(k,K)+1):
                    v+=(3*j-2*n)*a[j]*fresh[k-j]
                t=v/(2*n)
                fresh.append(t);partial+=t/(2*n+1)
        finally:ctx.prec=bits
        result+=partial
        hist=(hist+fresh)[-K:]
        start+=size
        if start%max(block*16,1)==1 or start==N:
            print('block terms',start,'/',N,'sum radius',result.rad().str(8),flush=True)
    tail=8*pi*q**N/(1-q)+2*pi*eta
    value=2*pi*result+arb(0,tail.upper())
    assert arb('5.5510')<value<arb('5.5511')
    assert value.rel_accuracy_bits()>=target,(value.rel_accuracy_bits(),target)
    print('Eulerian arclength block',value.str(40),'relative bits',value.rel_accuracy_bits(),flush=True)
    return value

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,default=4096);p.add_argument('--target',type=int,default=3000);p.add_argument('--block',type=int,default=64)
    p.add_argument('--adaptive',action='store_true')
    p.add_argument('--kernel-chunk',type=int,default=0)
    p.add_argument('--output',default='m11-euler-block.json');args=p.parse_args();t=time.monotonic()
    value=evaluate(args.bits,args.target,args.block,args.adaptive,args.kernel_chunk);dt=time.monotonic()-t
    peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    Path(args.output).write_text(json.dumps({'quantity':'full Eulerian arclength','parameters':vars(args),'elapsed_seconds':dt,'peak_rss_kib':peak,'enclosure':exact_endpoints(value)},indent=2)+'\n')
    print('Elapsed seconds',dt,'peak RSS KiB',peak,flush=True)
