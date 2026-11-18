"""Derived scalars and complete elliptic integral for Manuscript 11.

Input is the outward-rounded Arb ball emitted by m11_hstar.py in the same
workflow. The original ball is independently certified by the contraction
and global distance argument in that script. Record each new rounding cell.
"""
import gzip
import json
import sys
from flint import acb
from million_decimal_common import arb, ctx, WORK, MIN, record, finish

def get_hstar(path):
    with gzip.open(path,'rt',encoding='utf-8') as stream:
        for line in stream:
            obj=json.loads(line)
            if obj['name']=='Theorem 3.13 Eq (70) h_star':
                x=arb(obj['arb_ball'])
                assert x.rel_accuracy_bits() >= MIN
                return x
    raise ValueError('missing h_star enclosure')

def radial(pi):
    m=arb(1)/2-1/pi
    def f(t):
        return (2*(t/2).sin()-t*(t/2).cos())/(t*t*t.sin())-m
    def df(t):
        n=2*(t/2).sin()-t*(t/2).cos(); d=t*t*t.sin()
        return (t/2)*(t/2).sin()/d-n*(2*t*t.sin()+t*t*t.cos())/d**2
    t=arb('2.1'); p=128
    while True:
        ctx.prec=min(p,WORK)
        # Recompute pi and its coefficient at each precision.
        m=arb(1)/2-1/arb.pi()
        for _ in range(5 if p==128 else 2): t=(t-f(t)/df(t)).mid()
        if ctx.prec==WORK: break
        p*=2
    rho=arb(2)**(-3480000)
    lo,hi=t-rho,t+rho
    assert arb(2)<lo<hi<arb('2.2') and f(lo)<0<f(hi)
    t=arb(t,2*rho)
    assert t.lower()<=lo.lower() and hi.upper()<=t.upper()
    return (2*(t/2).sin()/t-arb(1)/2-1/pi-m*t.cos())/2

def main():
    h=get_hstar(sys.argv[1]); pi=arb.pi(); c=arb(1)/2+1/pi; m=arb(1)/2-1/pi
    record('Eq (69) a_H = m',m)
    assert c+h>2*m>0
    eps=radial(pi)
    assert 0<h<eps
    gain=100*(1-h/eps)
    assert arb('0.935')<gain<arb('0.945')
    record('Hausdorff vs radial gain percent',gain)
    s1,s3=(pi/2).si(),(3*pi/2).si()
    b,a=2*s1/pi,2*(s3-s1)/pi
    err=b-a-2/pi
    gain=100*(1-h/err)
    assert arb('41.5')<gain<arb('42.5')
    record('Hausdorff vs projection gain percent',gain)
    # |gamma_L'|=sqrt((b+a)^2-4ab*sin(theta/2)^2).
    # Fourfold symmetry of the elliptic integral: total length 4(b+a) E(k²).
    k2=4*a*b/(a+b)**2
    assert 0<k2<1
    val=acb(k2).elliptic_e()
    assert val.imag.contains(0)
    length=4*(b+a)*val.real
    assert arb('5.5243')<length<arb('5.5244')
    record('After Eq (50) full limacon length',length)
    C=(2*pi).si()/pi
    record('Eq (48b) normalized central energy C',C)
    record('Eq (48c) normalized tail energy S',arb(1)/2-C)
    finish('m11hstar-derived')

if __name__=='__main__': main()
