"""M14.119 final 17-Nov-2026 source: cross-check all displayed scalar decimal
values from sections 2, 4, 6, 7, 8, 9 and 10, and the eleven zeta terms.
Physical table values are conditional calculations from the printed inputs.
No measurement is certified beyond its source's precision.
"""
from fractions import Fraction as Q
from math import factorial
from flint import arb, ctx
from million_decimal_common import record, finish, exact, WORK, MIN

assert ctx.prec == WORK == 3600000 and MIN == 3400000

def rounded(name, value, printed):
    n = len(printed.partition('.')[2])
    center = Q(printed)
    half = Q(1, 2 * 10**n)
    assert exact(center-half) < value < exact(center+half), (name, printed)
    record(name, value)

def profile(x):
    return x.sinh()/x

def scalars(x, label, displayed):
    u = (-2*x).exp()
    L = x.cosh()/x.sinh() - 1/x
    assert L.overlaps((1+u)/(1-u)-1/x)
    V = 1/x**2-1/x.sinh()**2
    assert V.overlaps(1/x**2-4*u/(1-u)**2)
    tr = L/(2*x)
    hs = (2*tr-V)/(4*x*x)
    for name, val, dec in zip(('profile', 'Langevin', 'variance', 'trace', 'HS squared'),
                              (profile(x), L, V, tr, hs), displayed):
        rounded(label+' '+name,val,dec)
    return L,V,tr,hs

a = 1/arb(8).sqrt()
b = 1/arb(2).sqrt()
La,Va,Ta,Ha = scalars(a,'a',(
    '1.0209639298650195104786646351804211019462043266699',
    '0.11688058470393301970853181386179164401493872379933',
    '0.32516249665366914396163376385083845935142050373689',
    '0.16529410806639939866550278088492457407260894951106',
    '0.010851438958259306738743595838021377587594790570479'))
Lb,Vb,Tb,Hb = scalars(b,'b',(
    '1.0854416412726070018696230810771799943362362464373',
    '0.22820184167862343547106085276503992978675557681550',
    '0.30247164053363031351513391306894250708230381630266',
    '0.1613630697302135425959636855281220737173049616172233',
    '0.010127249463398385838396728993650820176153053465894'))
ca=a.cosh(); tha=a.sinh()/ca; seca=1/ca**2
rounded('cosh(a)',ca,'1.0631537604037705983260079789718467840680879072616')
rounded('tanh(a)',tha,'0.33952309865331385123358989166828821555857242983167')
rounded('sech^2(a)',seca,'0.88472406548085211009890188842493156897779476147375')
tdn=tha/(2*a)
rounded('DN trace(a)',tdn,'0.48015817085445477171835196122756372079661089695783')
assert profile(b).overlaps(profile(a)*ca)
assert (2*Lb).overlaps(La+tha)
assert (4*Vb).overlaps(Va+seca)
assert (4*Tb).overlaps(Ta+tdn)

for x, label, dec in ((b,'Montgomery-Taylor z0','0.67250070367941164573437979080329518859340302862626'),
                      (2*b,'Montgomery-Taylor z1','1.27673082474804740671137717691544684163532597865042')):
    val=exact(Q(3,2))-x*x.cos()/x.sin()
    rounded(label,val,dec)
K=(1+arb(2).sqrt()).log()/2
rounded('K_sd',K,'0.44068679350977151261630466248989615451408016413082')
assert (2*K).sinh().contains(1)
mu=(2+arb(2).sqrt()).sqrt(); root=mu/arb(8).sqrt()
rounded('quartic largest root',root,'0.65328148243818826392832158671359357679188059417463')
assert root.overlaps((1+b).sqrt()/2)
assert (root**4-root**2/2+exact(Q(1,32))).contains(0)

# Bernoulli input independently reconstructed using Akiyama–Tanigawa.
B=[]; u=[Q(0)]*23
for m in range(23):
    u[m]=Q(1,m+1)
    for j in range(m,0,-1): u[j-1]=j*(u[j-1]-u[j])
    B.append(u[0])
printed=list(map(Q, ('1/48','-1/11520','1/1451520','-1/154828800',
    '1/15328051200','-691/1004293914624000','1/133905855283200',
    '-3617/43706871164436480000','43867/47085412305447419904000',
    '-174611/16442524932061003776000000','77683/635339163374837185904640000')))
pi=arb.pi()
for j, ref in enumerate(printed,1):
    assert B[2*j]/(2**(j+1)*j*factorial(2*j)) == ref
    zterm=(-1)**(j+1)*arb(2*j).zeta()/(j*(8*pi*pi)**j)
    assert exact(ref).overlaps(zterm)
    record(f'zeta term {j}',zterm)

def F(n,t): return t**(n-1)*(t-1)-1

def parry_root(n,initial):
    # Newton is only a proposal mechanism. The final interval is proved
    # by strict opposite endpoint signs and uniqueness on (1,2).
    x=exact(Q(initial)).mid()
    for _ in range(28):
        d=x**(n-2)*(n*x-(n-1))
        x=(x-F(n,x)/d).mid()
    radius=4*abs(F(n,x)).upper()+arb(2)**(-WORK+30)
    result=arb(x,radius)
    lo,hi=result.lower(),result.upper()
    assert 1<lo and hi<2 and F(n,lo)<0 and 0<F(n,hi), n
    record(f'beta_{n}',result)
    return result

b31=parry_root(31,'1.1'); b32=parry_root(32,'1.1')
b187=parry_root(187,'1.03'); b188=parry_root(188,'1.03')
be=profile(b); bz=profile(a)
assert b32<be<b31 and b188<bz<b187
hE=(be-b32)/(b31-b32)
rounded('Figure 3 h_E',hE,'0.9961')
defect=1-be**30*(be-1)
assert exact(Q(313240,10**9))<defect<exact(Q(313241,10**9))
record('Parry defect',defect)

# Table 1: conditional algebra using the source's rounded physical inputs.
kB=exact(Q('1.380649e-23')); muB=exact(Q('9.274e-24'))
for x, label, xprint, lp, mp, op, cp in (
    (a,'H0','0.3536','0.1169','0.4416','54.2','0.00526'),
    (b,'H1','0.7071','0.2282','0.3859','108','0.0105'),
    (arb(1),'H=-2','1','0.3130','0.3435','153','0.0149'),
    (exact(Q(13,4)),'H=-6.5','3.25','0.6953','0.1523','498','0.0484')):
    L=x.cosh()/x.sinh()-1/x
    rounded(label+' |x|',x,xprint)
    rounded(label+' |L|',L,lp)
    rounded(label+' m(-2x)',(1-L)/2,mp)
    rounded(label+' O2 conditional B',x*kB*293/exact(Q('2.64e-23')),op)
    rounded(label+' Co conditional B',x*kB*300/(30000*muB),cp)

finish('m14displayed')
