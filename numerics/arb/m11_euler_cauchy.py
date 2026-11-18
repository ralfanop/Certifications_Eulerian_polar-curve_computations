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
            assert (r+I*rp).abs_lower()>arb(1)/8 and (r-I*rp).abs_lower()>arb(1)/8, (i,j)
            count+=1
    # Absolute Taylor majorants on the full complex disk.
    a=arb(R)/2
    rmax=a.sinh()/a
    rpmax=(a*a.cosh()-a.sinh())/(2*a*a)
    assert rmax<3 and rpmax<2 and rmax*rmax+rpmax*rpmax<13
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
    a=arb(1)/24; coeff=[]; eta=arb(2)**(-bits-20)
    for k in range(n):
        m=2*k+4
        term=a*((3*m*(m-1))//2+2*m-2)
        # For k>=5 the absolute coefficient ratio is <1/2:
        # coefficient ratio = 25/(m+1)(m+2) * P(m+2)/P(m),
        # P(m)=(3m²+m-4)/2=(m-1)(3m+4)/2.
        # It is < 100/((m+1)(m+2)) for m>=12; for m>=14
        # this is <1/2. Therefore the uniform omitted tail is <=2|term|.
        if k>=5 and 2*term.abs_upper()<eta:
            break
        coeff.append(term)
        a=-25*a/((m+1)*(m+2))
    assert coeff[0].contains(1) and coeff[1].overlaps(-arb(275)/144)
    # P differs from F by <=eta on |theta|<=5 if the loop was truncated
    # before n. If it reached n, we must bound the entire omitted tail too.
    if len(coeff)==n:
        m=2*n+4
        assert n>=5 and 2*(a*((3*m*(m-1))//2+2*m-2)).abs_upper()<eta
    # |F|>1/64 on the disk; P is zero-free there by uniform approximation.
    # P(0)=1 and |P|<14, so its analytic positive square root is bounded by 4.
    # On the real interval F>=4/pi², both square roots >1/2, giving
    # |sqrt(F)-sqrt(P)| <= eta. This is separate from truncating sqrt(P).
    assert eta<arb(1)/128 and 4/pi**2-eta>arb(1)/4
    print('Taylor coefficient count',n,'nonzero speed-square coefficients',len(coeff),flush=True)
    S=arb_series(coeff,prec=n).sqrt()
    assert S[0]>0 and S.prec==n
    # Evaluate integrated Taylor polynomial in u at q using Horner.
    result=arb(0)
    for k in range(n-1,-1,-1):
        result=result*q+S[k]/(2*k+1)
    tail=8*pi*q**n/(1-q)+2*pi*eta
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
