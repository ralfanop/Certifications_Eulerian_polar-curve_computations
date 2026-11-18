"""Independent rigorous Eulerian arclength: Cauchy-bound even Taylor series.

For r(theta)=sinc(theta/2), F=r²+(r')² is entire and even.
An Arb rectangle cover excludes zeros of both r±i r' on |theta|<=5.
The analytic square root with value +1 at zero therefore exists there.
The full arclength follows by termwise integration and a geometric Cauchy tail.
"""
import argparse,time,json
from pathlib import Path
from flint import acb,arb,arb_series,ctx

def analytic_disk():
    ctx.prec=128
    R=5; scale=8; count=0
    I=acb(0,1)
    for i in range(-R*scale,R*scale):
        for j in range(-R*scale,R*scale):
            # Nearest point of the exact dyadic rectangle to the origin.
            if min(abs(i),abs(i+1))**2+min(abs(j),abs(j+1))**2>(R*scale)**2:
                continue
            t=acb(arb((arb(i)+arb(1)/2)/scale,arb(1)/(2*scale)),
                  arb((arb(j)+arb(1)/2)/scale,arb(1)/(2*scale)))
            z=-t*t/16
            r=z.hypgeom_0f1(arb(3)/2)
            rp=-t/12*z.hypgeom_0f1(arb(5)/2)
            assert not (r+I*rp).contains(0) and not (r-I*rp).contains(0), (i,j)
            count+=1
    # Absolute Taylor majorants on the full complex disk.
    a=arb(R)/2
    rmax=a.sinh()/a
    rpmax=(a*a.cosh()-a.sinh())/(2*a*a)
    assert rmax<3 and rpmax<2 and (rmax*rmax+rpmax*rpmax).sqrt()<4
    print('Analytic disk radius 5, zero-free rectangles',count,'and |sqrt(F)|<4: PASS',flush=True)

def evaluate(bits,target):
    analytic_disk()
    ctx.prec=bits
    pi=arb.pi(); q=pi*pi/25
    assert 0<q<arb('0.4')
    # 2*pi*4/(1-q)< 44.  0.4 < 2^(-1.32), so take a safe integer N.
    n=(target+20)*25//33+2
    assert 8*pi*q**n/(1-q)<arb(2)**(-target-4)
    ctx.cap=n
    # Derived coefficient of theta^(2k):
    # (-1)^k * [3(2k+4)(2k+3)/2 + 2(2k+4)-2] / (2k+4)!.
    # The variable u=theta²/25 means that coefficients carry 25^k.
    a=arb(1)/24; coeff=[]
    for k in range(n):
        m=2*k+4
        coeff.append(a*((3*m*(m-1))//2+2*m-2))
        a=-25*a/((m+1)*(m+2))
    assert coeff[0].contains(1) and coeff[1].overlaps(-arb(275)/144)
    print('Taylor coefficient count',n,flush=True)
    S=arb_series(coeff,prec=n).sqrt()
    assert S[0]>0 and S.prec==n
    # Evaluate integrated Taylor polynomial in u at q using Horner.
    result=arb(0)
    for k in range(n-1,-1,-1):
        result=result*q+S[k]/(2*k+1)
    tail=8*pi*q**n/(1-q)
    length=2*pi*result+arb(0,tail.upper())
    assert arb('5.5510')<length<arb('5.5511')
    assert length.rel_accuracy_bits()>=target,(length.rel_accuracy_bits(),target)
    print('Eulerian full length',length.str(40), 'relative bits',length.rel_accuracy_bits(),flush=True)
    return length

def exact_endpoints(x):
    lo,hi=x.lower().fmpq(),x.upper().fmpq()
    return {'relative_bits':x.rel_accuracy_bits(),
            'lower':{'numerator':str(lo.p),'denominator':str(lo.q)},
            'upper':{'numerator':str(hi.p),'denominator':str(hi.q)}}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bits',type=int,default=4096);p.add_argument('--target',type=int,default=3000)
    p.add_argument('--output',default='m11-euler-cauchy.json')
    args=p.parse_args(); start=time.monotonic();x=evaluate(args.bits,args.target)
    elapsed=time.monotonic()-start
    Path(args.output).write_text(json.dumps({'quantity':'full Eulerian arclength','working_bits':args.bits,
        'threshold_bits':args.target,'elapsed_seconds':elapsed,'enclosure':exact_endpoints(x)},indent=2)+'\n')
    print('Elapsed seconds',elapsed,flush=True)
