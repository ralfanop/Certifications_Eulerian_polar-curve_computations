"""Finite-memory arclength recurrence with divide-and-conquer block solving.

The inner recurrence is solved by recursive truncated convolutions rather
than a quadratic Python coefficient loop.  Kernel chunks can also be
multiplied at reduced precision; the outward Arb bounds remain rigorous.
"""
import argparse,json,math,resource,time
from pathlib import Path
from flint import arb,arb_poly,ctx
from m11_euler_block import scaled_speed_polynomial
from m11_euler_cauchy import analytic_disk,exact_endpoints


def solve_block(a,C,D,start,leaf):
    K=len(a)-1;B=len(C);t=[arb(0)]*B;J=[j*a[j] for j in range(min(B,K+1))]
    def solve(l,r):
        if r-l<=leaf:
            for k in range(l,r):
                n=start+k;v=3*D[k]-2*n*C[k]
                for j in range(1,min(k-l,K)+1):
                    v+=(3*j-2*n)*a[j]*t[k-j]
                t[k]=v/(2*n)
            return
        m=(l+r)//2;solve(l,m)
        H=arb_poly(t[l:m]);P=arb_poly([arb(0)]+a[1:r-l]);W=arb_poly(J[:r-l])
        c=P*H;d=W*H
        for k in range(m,r):
            C[k]+=c[k-l];D[k]+=d[k-l]
        solve(m,r)
    solve(0,B)
    return t


def middle(a,hist,B,chunk,discount,discounts):
    n=len(hist);K=len(a)-1;C=[arb(0)]*B;D=[arb(0)]*B;prec=ctx.prec
    for j0 in range(1,K+1,chunk):
        j1=min(K+1,j0+chunk);l=max(0,n-j1+1);r=min(n,n+B-j0)
        if l>=r:continue
        try:
            if discount:ctx.prec=max(256,prec-discounts[j0])
            H=arb_poly(hist[l:r]);P=arb_poly(a[j0:j1]);J=arb_poly([j*a[j] for j in range(j0,j1)])
            c=P*H;d=J*H
        finally:ctx.prec=prec
        for k in range(B):
            idx=n+k-j0-l
            if idx>=0:C[k]+=c[idx];D[k]+=d[idx]
    return C,D


def evaluate(bits,target,block,chunk,leaf,discount):
    analytic_disk();ctx.prec=bits
    pi,q,eta,a=scaled_speed_polynomial(target)
    N=(target+20)*25//33+2;K=len(a)-1
    assert 8*pi*q**N/(1-q)<arb(2)**(-target-4)
    # Approximate precision allocation only: all ball operations are enclosing.
    rate=math.log2(float(1/q));discounts={}
    if discount:
        for j in range(1,K+1,chunk):
            # scaled kernel decay beyond geometric decay of the history
            discounts[j]=max(0,int(.75*(-float(a[j].abs_upper().log()/arb(2).log())-rate*j)))
    hist=[arb(1)];total=arb(1);start=1
    print('Terms',N,'width',K,'block',block,'chunk',chunk,'leaf',leaf,flush=True)
    while start<N:
        B=min(block,N-start);ctx.prec=max(256,bits-int(.8*start*rate))
        try:
            C,D=middle(a,hist,B,chunk,discount,discounts)
            fresh=solve_block(a,C,D,start,leaf)
            part=sum((x/(2*(start+k)+1) for k,x in enumerate(fresh)),arb(0))
        finally:ctx.prec=bits
        total+=part;hist=(hist+fresh)[-K:];start+=B
        if start%max(block*8,1)==1 or start==N:
            print('Terms',start,'/',N,'sum radius',total.rad().str(8),flush=True)
    tail=8*pi*q**N/(1-q)+2*pi*eta
    value=2*pi*total+arb(0,tail.upper())
    assert arb('5.5510')<value<arb('5.5511')
    assert value.rel_accuracy_bits()>=target,(value.rel_accuracy_bits(),target)
    return value


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,default=28000);p.add_argument('--target',type=int,default=20000);p.add_argument('--block',type=int,default=256);p.add_argument('--chunk',type=int,default=256);p.add_argument('--leaf',type=int,default=16);p.add_argument('--discount',action='store_true');p.add_argument('--output',default='m11-euler-cdq.json')
    args=p.parse_args();t=time.monotonic();value=evaluate(args.bits,args.target,args.block,args.chunk,args.leaf,args.discount);dt=time.monotonic()-t
    peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print('Eulerian arclength CDQ',value.str(40),'relative bits',value.rel_accuracy_bits(),'elapsed',dt,'peak RSS KiB',peak,flush=True)
    Path(args.output).write_text(json.dumps({'quantity':'full Eulerian arclength','method':'finite-memory divide-and-conquer block recurrence','parameters':vars(args),'elapsed_seconds':dt,'peak_rss_kib':peak,'enclosure':exact_endpoints(value)},indent=2)+'\n')
