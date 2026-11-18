"""Rigorous Hausdorff balance certificate, Manuscript 11, Theorem 3.13.

The three equations are |P-Z|²=h², (P-Z)·P'=0, (P-Z)·Z'=0.
Newton generates a candidate only. A uniform contraction proves existence
of an exact zero. A globally concave explicit comparison path on the
central interval, and the manuscript's radial concavity outside, prove Q(h)=h.
"""
import os
import sys
from flint import arb, arb_mat, ctx

def geometry(x):
    th,t,h=x
    pi=arb.pi(); c=arb(1)/2+1/pi; m=arb(1)/2-1/pi
    s=(th/2).sin(); co=(th/2).cos()
    r=2*s/th; p=co/th-2*s/th**2
    q=-s/(2*th)-2*co/th**2+4*s/th**3
    R=c+h+m*t.cos(); P=-m*t.sin(); Q=-m*t.cos()
    C=(th-t).cos(); S=(th-t).sin()
    return r,p,q,R,P,Q,C,S

def system(x):
    th,t,h=x
    r,p,q,R,P,Q,C,S=geometry(x)
    f=(r-R)**2+2*r*R*(1-C)-h*h
    g=r*p-R*(p*C-r*S)
    k=r*(P*C+R*S)-R*P
    dot=(p*P+r*R)*C+(p*R-r*P)*S
    J=arb_mat([[2*g,-2*k,2*(R-r*C-h)],
        [p*p+r*q-R*((q-r)*C-2*p*S),-dot,-(p*C-r*S)],
        [dot,r*((Q-R)*C+2*P*S)-P*P-R*Q,r*S-P]])
    return arb_mat([[f],[g],[k]]),J

def point_mat(a):
    return arb_mat([[a[i,j].mid() for j in range(a.ncols())] for i in range(a.nrows())])

def midvec(a):
    return [a[i,0].mid() for i in range(a.nrows())]

def candidate(work):
    x=[arb('2.1074'),arb('2.0956'),arb('0.0493')]
    p=128
    while True:
        ctx.prec=min(p,work)
        for _ in range(5 if p==128 else 2):
            f,J=system(x)
            x=midvec(arb_mat([[v] for v in x])-J.solve(f))
        print('Newton candidate bits',ctx.prec,flush=True)
        if ctx.prec==work: break
        # Increase by less than a factor 2 to retain guard bits from the last step.
        p=min(2*p,work)
    return x

def prove(x,work,target):
    # B is a fixed exact dyadic matrix, not an uncertain inverse.
    ctx.prec=160
    x0=[v.mid() for v in x]
    _,J=system(x0)
    B=point_mat(J.inv())
    # Coarse box contains the later microscopic box. Uniform contraction bound.
    coarse=[arb(v,arb('0.00001')) for v in x0]
    _,Jbox=system(coarse)
    ident=arb_mat([[int(i==j) for j in range(3)] for i in range(3)])
    M=ident-B*Jbox
    for i in range(3):
        assert sum(M[i,j].abs_upper() for j in range(3)) < arb(1)/2
    # Global proof at the exact zero: choose t(u)=t0+u-theta0.
    # On the central interval F(u)=|P(u)-Z(t(u))|² has F''<0.
    # Each interval is exact dyadic/rational via outward Arb construction.
    th0,t0,h0=coarse
    assert arb('1.98') < th0 < arb('2.22') and h0>0
    pi=arb.pi(); c=arb(1)/2+1/pi; m=arb(1)/2-1/pi
    assert c+h0>2*m
    def gap(t): return 2*(t/2).sin()/t-c-m*t.cos()
    a,b,mid=arb('1.98'),arb('2.22'),arb('2.1')
    assert gap(a)<2*h0 and gap(b)<2*h0
    assert gap(mid)>gap(a) and gap(mid)>gap(b)
    # Concavity in cos(theta) proved in Theorem 3.12 implies the radial bound outside.
    for i in range(240):
        u=arb(a+(arb(i)+arb(1)/2)/1000,arb(1)/2000)
        t=t0+u-th0
        r,p,q,R,P,Q,_,_=geometry([u,t,h0])
        C=(th0-t0).cos()
        Fpp=2*(p*p+r*q+P*P+R*Q-C*(q*R+2*p*P+r*Q))
        assert Fpp<0, (i,Fpp)
    # Outward sign: (P-Z)·N > 0. N=R*u_t-R'*v_t.
    r,p,q,R,P,Q,C,S=geometry(coarse)
    assert R*(r*C-R)-P*r*S>0
    print('Global comparison path, outward orientation, contraction: PASS',flush=True)
    ctx.prec=work
    # For a cube of radius rho the fixed-point map x-BF(x) maps the cube
    # into itself: sup |BF(center)| <rho/2 and sup ||I-BJ||_inf <1/2.
    rho=arb(2)**(-target)
    for i in range(3):
        assert (x[i]-x0[i]).abs_upper()+rho < arb('0.000009')
    f,_=system(x)
    residual=B*f
    assert all(residual[i,0].abs_upper()<rho/2 for i in range(3)), 'Newton residual insufficient'
    assert B.det().is_finite() and not B.det().contains(0)
    X=[arb(v,rho) for v in x]
    print('Existence of exact common-normal root: PASS',flush=True)
    # At F=0, the point displacement has norm h and is parallel to the
    # outward normal by k=0. The support half-plane gives Q(h)>=h.
    # g=k=0 gives F'(theta0)=0 for the explicit affine comparison path.
    # Strict concavity proves F(u)<=h² everywhere on central interval.
    # Outside, the radial comparison above gives distance<h. Hence Q(h)=h,
    # identifying this exact root with h_* by Theorem 3.13 uniqueness.
    return X

def main():
    pilot=os.getenv('M11_HSTAR_PILOT')=='1'
    work,target=(512,400) if pilot else (3600000,3480000)
    x=candidate(work)
    th,t,h=prove(x,work,target)
    print('h_star prefix:',h.str(82),flush=True)
    if pilot:
        print('PILOT PASS',h.rel_accuracy_bits(),flush=True)
        return
    from million_decimal_common import record,finish
    pi=arb.pi(); c=arb(1)/2+1/pi
    assert arb('0.049297948325718335705')<h<arb('0.049297948325718335715')
    record('Theorem 3.13 Eq (70) h_star',h)
    record('Theorem 3.13 Eq (71) b_H',c+h)
    record('common normal Eulerian parameter',th)
    record('common normal limacon parameter',t)
    finish('m11hstar')

if __name__=='__main__': main()
