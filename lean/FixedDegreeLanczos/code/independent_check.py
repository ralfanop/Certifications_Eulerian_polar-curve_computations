#!/usr/bin/env python3
"""Independent QQ(M) Stieltjes reconstruction. No supplied JS is imported.

Moments use falling factorial occupancy counts, not the supplied recurrence.
Orthogonal polynomials use norm ratios, not Hankel determinants.
Only the optional final parity comparison computes determinant blocks.
"""
from pathlib import Path
from math import factorial, gcd, lcm
from fractions import Fraction
import json, time
from flint import fmpq_poly as Poly, fmpq

ROOT = Path(__file__).resolve().parents[1]
DATA = json.loads((ROOT/'inputs/V033_Lanczos_beta5_beta16_exact.json').read_text())
START = time.monotonic()
X = Poly([0, 1])

class RF:
    def __init__(self, n=0, d=1):
        if isinstance(n, RF): self.n, self.d = n.n, n.d; return
        n = n if isinstance(n, Poly) else Poly([n])
        d = d if isinstance(d, Poly) else Poly([d])
        assert d
        if not n: self.n,self.d=Poly([]),Poly([1]); return
        g=n.gcd(d); n,d=n//g,d//g
        a=d[d.degree()]
        self.n,self.d=n/a,d/a
    def __add__(self,other):
        other=RF(other); return RF(self.n*other.d+other.n*self.d,self.d*other.d)
    __radd__=__add__
    def __neg__(self): return RF(-self.n,self.d)
    def __sub__(self,other): return self+-RF(other)
    def __mul__(self,other):
        other=RF(other); return RF(self.n*other.n,self.d*other.d)
    __rmul__=__mul__
    def __truediv__(self,other):
        other=RF(other); return RF(self.n*other.d,self.d*other.n)
    def __eq__(self,other):
        other=RF(other); return self.n*other.d==other.n*self.d
    def at(self,m): return self.n(m)/self.d(m)

def arr(p): return [str(c) for c in p]
def rf_data(p): return {'n':arr(p.n),'d':arr(p.d)}
def moments_occupancy(rmax=16):
    """[t^(2r)] (1+B(t))^M = sum_k (M)_k/k! [t^(2r)]B(t)^k."""
    b=Poly([0]+[fmpq(1,4**r*factorial(2*r+1)) for r in range(1,rmax+1)])
    powers=[Poly([1])]
    falling=[Poly([1])]
    for k in range(1,rmax+1):
        powers.append((powers[-1]*b).truncate(rmax+1))
        falling.append(falling[-1]*(X-(k-1)))
    return [sum((falling[k]*(powers[k][r]/factorial(k)) for k in range(r+1)),Poly([]))*factorial(2*r) for r in range(rmax+1)]

MU=moments_occupancy()
def inner_monomial(p,k):
    return sum((c*RF(MU[(i+k)//2]) for i,c in enumerate(p) if (i+k)%2==0),RF())

polys=[[RF(1)],[RF(0),RF(1)]]
norms=[RF(1)]
betas={}; records=[]
for n in range(1,17):
    p=polys[n]
    # Independently check the defining orthogonality, including all lower monomials.
    assert p[-1]==1
    for k in range(n): assert inner_monomial(p,k)==0, (n,k)
    hn=inner_monomial(p,n)
    bn=hn/norms[-1]
    norms.append(hn);betas[n]=bn
    if n<16:
        nxt=[RF(0)]+p
        for k,c in enumerate(polys[n-1]): nxt[k]=nxt[k]-bn*c
        polys.append(nxt)
    rec={'j':n,'numerator_degree':bn.n.degree(),'denominator_degree':bn.d.degree()}
    if n>=5:
        supplied=DATA['beta'][str(n)]
        N=Poly([int(x) for x in supplied['numerator']])
        D=Poly([int(x) for x in supplied['denominator']])
        assert bn.n*D==bn.d*N, ('rational mismatch',n)
        rec['symbolic_identity']=True
        rec['common_polynomial_factor_degree']=N.gcd(D).degree()
        rec['legendre']=str(bn.at(1))
        assert bn.at(1)==fmpq(n*n,4*(4*n*n-1))
        rec['specializations']={str(m):str(bn.at(m)) for m in [1,2,3,4,5,10,335]}
    records.append(rec)
    print(f'Stieltjes j={n}: exact orthogonality and ratio PASS; {time.monotonic()-START:.2f}s',flush=True)

# Second, genuinely independent numerical-specialization construction:
# repeated convolution of moments + full classical Gram-Schmidt on monomials.
def exact_specialization(M):
    one=[Fraction(0) if k%2 else Fraction(1,2**k*(k+1)) for k in range(33)]
    from math import comb
    mu=[Fraction(1)]+[Fraction(0)]*32
    for _ in range(M):
        mu=[sum((comb(k,r)*mu[r]*one[k-r] for r in range(k+1)),Fraction(0)) for k in range(33)]
    for r in range(17): assert str(mu[2*r])==str(MU[r](M))
    def ip(p,q):
        return sum((a*b*mu[i+j] for i,a in enumerate(p) for j,b in enumerate(q)),Fraction(0))
    ps=[];hs=[]
    for n in range(17):
        p=[Fraction(0)]*n+[Fraction(1)]
        for q,h in zip(ps,hs):
            t=ip(p,q)/h
            for k,a in enumerate(q): p[k]-=t*a
        h=ip(p,p); assert h>0
        if n: assert str(h/hs[-1])==str(betas[n].at(M)),(M,n)
        ps.append(p);hs.append(h)
    print(f'Full Fraction Gram-Schmidt M={M}: all j<=16 PASS',flush=True)
for M in [1,2,3,4,5,10]: exact_specialization(M)

# Compare all supplied primitive parity polynomials; Gaussian elimination here,
# on our independently derived moments, also returns normalization constants.
def determinant(matrix):
    a=[[RF(c) for c in row] for row in matrix]; ans=RF(1)
    for k in range(len(a)):
        assert a[k][k]!=0
        pivot=a[k][k]; ans=ans*pivot
        for i in range(k+1,len(a)):
            t=a[i][k]/pivot
            for j in range(k+1,len(a)): a[i][j]=a[i][j]-t*a[k][j]
    assert ans.d.degree()==0
    return ans.n/ans.d[0]

parity={}; determinants={}
for typ,maxr,shift in [('A',9,0),('B',8,1)]:
    for r in range(maxr+1):
        p=determinant([[MU[i+j+shift] for j in range(r)] for i in range(r)])
        valuation=next(i for i,c in enumerate(p) if c)
        den=lcm(*(int(c.q) for c in p))
        ints=[int(c*den) for c in list(p)[valuation:]]
        content=gcd(*ints)
        if ints[-1]<0: content=-content
        primitive=[i//content for i in ints]
        assert primitive==[int(c) for c in DATA['primitive_parity_polynomials'][typ][typ+str(r)]]
        parity[typ+str(r)]={'valuation_at_zero':valuation,'rational_content':str(Fraction(content,den)),'degree':len(primitive)-1,'verified':True}
        determinants[typ+str(r)]=p
        print(f'Parity {typ}{r}: primitive and normalization PASS',flush=True)

for j in range(5,17):
    r=j//2
    f=DATA['beta'][str(j)]
    def primitive_p(key): return Poly([int(x) for x in DATA['primitive_parity_polynomials'][key[0]][key]])
    nf=f['numerator_factors'];df=f['denominator_factors']
    factored=RF(primitive_p(nf[0])*primitive_p(nf[1]),primitive_p(df[0])*primitive_p(df[1]))
    scalar=betas[j]/factored
    assert scalar.n.degree()==0 and scalar.d.degree()==0
    assert str(scalar.at(1))==str(Fraction(f['scalar']))
    if j%2:
        parity_ratio=RF(determinants[f'B{r+1}']*determinants[f'A{r}'],determinants[f'A{r+1}']*determinants[f'B{r}'])
    else:
        parity_ratio=RF(determinants[f'A{r+1}']*determinants[f'B{r-1}'],determinants[f'A{r}']*determinants[f'B{r}'])
    assert parity_ratio==betas[j]

common=lcm(*(int(c.q) for p in MU for c in p))
assert str(common)==DATA['moment_common_denominator']
out={'method':'falling factorial moments; Stieltjes; exact orthogonality; independent Fraction Gram-Schmidt',
     'moment_common_denominator':str(common),'moments':[arr(p) for p in MU],
     'recurrence_coefficients':{str(j):rf_data(b) for j,b in betas.items()},
     'monic_polynomials':[[rf_data(c) for c in p] for p in polys],
     'norms':[rf_data(h) for h in norms],'checks':records,'parity':parity,
     'elapsed_seconds':time.monotonic()-START}
(ROOT/'results/independent_exact.json').write_text(json.dumps(out,indent=2)+'\n')
print('ALL EXACT CHECKS PASSED',flush=True)
