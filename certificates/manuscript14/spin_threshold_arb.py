"""Strict root rounding by monotonicity and Arb endpoint signs.
Newton is used only to propose the decimal cell; it is not the proof.
"""
import argparse,gzip,json,math,sys
from flint import arb,ctx,fmpq,fmpz,__version__
p=argparse.ArgumentParser()
p.add_argument('--case',required=True)
p.add_argument('--bits',type=int,default=3600000)
p.add_argument('--digits',type=int,default=1000001)
a=p.parse_args()
assert __version__=='0.9.0'
if hasattr(sys,'set_int_max_str_digits'): sys.set_int_max_str_digits(0)
def target():
    if a.case=='printed': return arb(4637)/6600
    n=int(a.case) # twice spin
    assert n>0
    return (arb(n)/(n+2)).sqrt()
def f(h):
    e=(-h).exp()
    return 1-2/h+2*e/(1-e)-target()
def fp(h):
    e=(-h).exp()
    return 2/(h*h)-2*e/((1-e)**2)
# Seed at 128 bits, verified sign bracket, then increase precision.
ctx.prec=128
lo=arb(1); hi=arb(16) if a.case=='printed' else arb(4*int(a.case)+16)
assert f(lo)<0 and f(hi)>0
for _ in range(90):
    mid=((lo+hi)/2).mid()
    fm=f(mid)
    if fm<0: lo=mid
    elif fm>0: hi=mid
    else: break
x=((lo+hi)/2).mid().fmpq()
bits=128
while bits<a.bits:
    bits=min(a.bits,bits*2)
    ctx.prec=bits
    for _ in range(3):
        h=arb(x)
        x=(h-f(h)/fp(h)).mid().fmpq()
ctx.prec=a.bits
scale=fmpz(10)**a.digits
num=x.p*scale
m=(2*num+x.q)//(2*x.q)
left=fmpq(2*m-1,2*scale); right=fmpq(2*m+1,2*scale)
fl=f(arb(left)); fr=f(arb(right))
assert fl<0 and fr>0, 'root not strictly inside rounding cell'
s=str(m).zfill(a.digits+1)
rounded=s[:-a.digits]+'.'+s[-a.digits:]
print('CERTIFIED',a.case,'prefix',rounded[:30],'working bits',ctx.prec,
      'fractional digits',a.digits,'strict endpoint signs PASS',flush=True)
with gzip.open('threshold.json.gz','wt',compresslevel=1) as out:
    json.dump(dict(case=a.case,working_bits=ctx.prec,fractional_digits=a.digits,
       rounded=rounded,lower_exact=str(left),upper_exact=str(right),
       lower_residual=fl.str(40,radius=True),upper_residual=fr.str(40,radius=True),
       python_flint=__version__),out)
