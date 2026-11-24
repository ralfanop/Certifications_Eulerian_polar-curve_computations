"""Rigorous interval checks for the finite-data localization criterion.
This tests the scalar budget only, not the analytic interpolation/Rouche theorem
or any actual unknown operator's sample errors.
"""
import argparse
from math import factorial
from flint import arb, ctx

def chebyshev(n, x):
    a, b = arb(1), x
    if n == 0:
        return a
    for _ in range(1, n):
        a, b = b, 2*x*b-a
    return b

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--bits",type=int,default=10000)
    args=p.parse_args()
    ctx.prec=args.bits
    assert ctx.prec == args.bits
    N, M = 32, 2
    h, S, delta = arb(1), arb(1)/5, arb(1)/100
    eta = arb(1)/arb(10)**74
    pi=arb.pi()
    rho=M*pi+delta
    Q=rho**2
    assert Q > h
    amplification=chebyshev(N,1+2*Q/h)
    data=eta*amplification
    remainder=2*(S*Q).exp()*(S*(Q+h))**(N+1)/factorial(N+1)
    budget=data+remainder
    threshold=delta.sin()/rho
    assert data > 0 and remainder > 0
    assert budget < threshold
    assert Q < 40 and rho < arb(63)/10 and arb(8).exp() < 3000
    rational_bound=arb(162)**32/arb(10)**74+6000*(arb(41)/5)**33/factorial(33)
    assert rational_bound < arb(3)/2000
    assert arb(3)/2000 < (delta-delta**3/6)/(arb(63)/10)
    assert (delta-delta**3/6)/(arb(63)/10) < threshold
    print("working_bits",ctx.prec)
    for name,v in [("amplification",amplification),("data",data),("remainder",remainder),("budget",budget),("threshold",threshold),("margin",threshold-budget),("rational_bound",rational_bound)]:
        print(name,v.str(50), "relative_bits",v.rel_accuracy_bits())
    for n in range(1,M+1):
        lo=1/(n*pi+delta)**2
        hi=1/(n*pi-delta)**2
        ref=1/(n*pi)**2
        assert lo < ref and ref < hi
        print("interval",n,lo.str(50),hi.str(50))
    print("PASS strict interval inequalities; conditional finite-data certificate")

if __name__=="__main__":
    main()
