#!/usr/bin/env python3
"""Validated enclosure of the manuscript's smooth-arc curvature discrepancy.

Requires python-flint. All certificate arithmetic uses Arb balls.
The Taylor remainder is explicit; no sampled-error estimate is used.
"""
from pathlib import Path
from math import factorial
from fractions import Fraction
import argparse,json,time,sys,hashlib
import flint
from flint import arb,arb_poly,arb_series,ctx

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def exact(q):
    return arb(str(q.numerator))/q.denominator

class Certification:
    def __init__(self,bits=256,order=32,panels=64,terms=80):
        require(order >= 4 and order % 2 == 0 and (panels >= 4), 'Certification condition failed: order >= 4 and order % 2 == 0 and (panels >= 4)')
        require(panels & panels - 1 == 0, 'Use a power of two for exact dyadic panel endpoints.')
        self.bits,self.order,self.panels,self.terms=bits,order,panels,terms
        ctx.prec=bits;ctx.cap=order+5
        self.pi=arb.pi()
        self.b=2/self.pi*(self.pi/2).si()
        self.a=2/self.pi*((3*self.pi/2).si()-(self.pi/2).si())
        require(self.pi * (self.b - self.a) > 2, 'Certification condition failed: self.pi * (self.b - self.a) > 2')
        # r_E(theta) = sum (-1)^k theta^(2k)/(2^(2k)(2k+1)!).
        coefficients=[arb(0)]*(2*terms+1)
        for k in range(terms+1):
            coefficients[2*k]=exact(Fraction((-1)**k,2**(2*k)*factorial(2*k+1)))
        self.radial=arb_poly(coefficients)
        self.tail=[]
        n=2*(terms+1)
        for j in range(order+3):
            # Derivative-j Taylor coefficient tail on |theta| <= 4.
            require(j <= n, 'Certification condition failed: j <= n')
            first=Fraction(4**(n-j),2**n*(n+1)*factorial(n-j)*factorial(j))
            ratio=Fraction(4,(n+2-j)*(n+1-j))
            require(0 < ratio < 1, 'Certification condition failed: 0 < ratio < 1')
            self.tail.append(exact(first/(1-ratio)).upper())
        require(self.b>2*self.a>0, 'Strict convexity condition for the limacon failed')
        self.charts={}

    def geometry(self,kind,x,order=None):
        """Jets in x-offset of H=pi*speed and curvature at x=theta/pi."""
        p=self.order if order is None else order
        theta=self.pi*x
        require(theta.abs_upper() < 4, 'Certification condition failed: theta.abs_upper() < 4')
        if kind=="E":
            shifted=self.radial(arb_poly([theta,arb(1)]))
            jet=[shifted[j]+arb(0,self.tail[j]) for j in range(p+3)]
            r=arb_series(jet[:p+1],prec=p+1)
            rp=arb_series([(j+1)*jet[j+1] for j in range(p+1)],prec=p+1)
            rpp=arb_series([(j+1)*(j+2)*jet[j+2] for j in range(p+1)],prec=p+1)
        else:
            theta_jet=arb_series([theta,1],prec=p+1)
            sn,cs=theta_jet.sin_cos()
            r=self.b+self.a*cs;rp=-self.a*sn;rpp=-self.a*cs
        v2=r*r+rp*rp
        require(v2[0] > 0, ('nonpositive speed enclosure', kind, x, v2[0]))
        v=v2.sqrt()
        k=(r*r+2*rp*rp-r*rpp)/(v2*v)
        powers=[self.pi**j for j in range(p+1)]
        H=arb_series([self.pi*v[j]*powers[j] for j in range(p+1)],prec=p+1)
        K=arb_series([k[j]*powers[j] for j in range(p+1)],prec=p+1)
        return H,K

    def build_chart(self,kind):
        """Taylor integration of speed over x in [0,1], with Lagrange bounds."""
        p=self.order;n=self.panels;h=arb(1)/n
        cells=[];total=arb(0)
        for j in range(n):
            lo=arb(j)/n
            X=arb((arb(j)+arb(1)/2)/n,h/2)
            point,_=self.geometry(kind,lo)
            domain,_=self.geometry(kind,X)
            B=domain[p].abs_upper()
            coeff=[arb(0)]+[point[k]/(k+1) for k in range(p)]
            integral=arb_poly(coeff)
            error=B*h**(p+1)/(p+1)
            cells.append({"left":lo,"cumulative":total,"integral":integral,"B":B})
            total=total+integral(h)+arb(0,error.upper())
        require(total > 0, 'Certification condition failed: total > 0')
        self.charts[kind]={"cells":cells,"length":total}
        return total

    def arclength(self,kind,x):
        """Rigorous A_i(x)=int_0^x H_i(t) dt for an exact point x in [0,1]."""
        require(x.is_exact() and x >= 0 and (x <= 1), 'Certification condition failed: x.is_exact() and x >= 0 and (x <= 1)')
        if x==0:return arb(0)
        if x==1:return self.charts[kind]["length"]
        # Float selects a cell; exact comparisons validate/repair the selection.
        j=min(self.panels-1,max(0,int(float(x)*self.panels)))
        while x<arb(j)/self.panels:j-=1
        while x>arb(j+1)/self.panels:j+=1
        cell=self.charts[kind]["cells"][j]
        d=x-cell["left"]
        require(d >= 0 and d <= arb(1) / self.panels, 'Certification condition failed: d >= 0 and d <= arb(1) / self.panels')
        value=cell["cumulative"]+cell["integral"](d)
        error=cell["B"]*d**(self.order+1)/(self.order+1)
        return value+arb(0,error.upper())

    def inverse(self,kind,u):
        """Enclose x_i(u). H_i>=2, so residual/2 rigorously bounds root error."""
        ell=self.charts[kind]["length"]
        require(0 <= u <= 1, 'Certification condition failed: 0 <= u <= 1')
        if u==0:return arb(0)
        if u==1:return arb(1)
        x=u.mid()
        for _ in range(8):
            residual=self.arclength(kind,x)-u*ell
            H,_=self.geometry(kind,x,order=0)
            nxt=(x-residual/H[0]).mid()
            if not (0<=nxt<=1):
                raise ArithmeticError("Newton guess left the proved real domain")
            if nxt==x:break
            x=nxt
        residual=self.arclength(kind,x)-u*ell
        return arb(x,(residual.abs_upper()/2).upper())

    def inverse_curvature_jet(self,kind,X):
        """Jet of k_i(x_i(u)) for any base root x_i(u) in the real ball X."""
        H,K=self.geometry(kind,X)
        ell=self.charts[kind]["length"]
        forward=(H/ell).integral()
        require(forward[0] == 0 and forward[1] > 0, 'Certification condition failed: forward[0] == 0 and forward[1] > 0')
        inverse=forward.reversion()
        result=K(inverse)
        require(result.prec >= self.order + 1, 'Certification condition failed: result.prec >= self.order + 1')
        return result

    def integrate_discrepancy(self):
        p=self.order;n=self.panels;h=arb(1)/(2*n)
        total=arb(0);largest_root_radius=arb(0);remainder_sum=arb(0)
        for j in range(n):
            u=(arb(j)+arb(1)/2)/n
            roots={k:self.inverse(k,u) for k in ["E","L"]}
            jets={k:self.inverse_curvature_jet(k,roots[k]) for k in ["E","L"]}
            f=(jets["E"]-jets["L"])**2
            value=sum((f[k]*(2*h**(k+1)/(k+1)) for k in range(0,p,2)),arb(0))
            # dx/du = ell/H <= ell/2 on the true [0,1] domain.
            domains={k:roots[k]+arb(0,(self.charts[k]["length"]*h/2).upper()) for k in ["E","L"]}
            wide={k:self.inverse_curvature_jet(k,domains[k]) for k in ["E","L"]}
            wide_f=(wide["E"]-wide["L"])**2
            B=wide_f[p].abs_upper()
            error=B*2*h**(p+1)/(p+1)
            require(error.is_finite(), ('nonfinite remainder', j))
            total+=value+arb(0,error.upper())
            remainder_sum+=error
            for X in roots.values():
                if X.rad()>largest_root_radius:largest_root_radius=X.rad()
            if (j+1)%16==0:
                print("Outer panels",j+1,"/",n,"radius",total.rad().str(6),flush=True)
        return total,largest_root_radius,remainder_sum

def rational_bounds(ball,digits=60):
    """Round endpoints outward using exact fractions, independent of formatting."""
    scale=10**digits
    lo=ball.lower().fmpq();hi=ball.upper().fmpq()
    lf=Fraction(int(lo.p),int(lo.q));hf=Fraction(int(hi.p),int(hi.q))
    low=lf.numerator*scale//lf.denominator
    high=-((-hf.numerator*scale)//hf.denominator)
    def fmt(n):
        sign="-" if n<0 else "";n=abs(n)
        return f"{sign}{n//scale}.{n%scale:0{digits}d}"
    return {"lower":fmt(low),"upper":fmt(high)}

def rounded_certification(ball,places):
    q=ball.mid().fmpq()
    mid=Fraction(int(q.p),int(q.q))
    scale=10**places
    val=(2*mid.numerator*scale+mid.denominator)//(2*mid.denominator)
    low=Fraction(2*val-1,2*scale);high=Fraction(2*val+1,2*scale)
    passed=ball>exact(low) and ball<exact(high)
    return {"places":places,"rounded":f"{val//scale}.{val%scale:0{places}d}","certified":bool(passed)}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--bits",type=int,default=256)
    ap.add_argument("--order",type=int,default=32)
    ap.add_argument("--panels",type=int,default=64)
    ap.add_argument("--terms",type=int,default=80)
    ap.add_argument("--output",default="D_K_CERTIFICATE.json")
    args=ap.parse_args()
    t=time.time();c=Certification(args.bits,args.order,args.panels,args.terms)
    print("Parameters",vars(args),flush=True)
    lengths={}
    for k in ["E","L"]:
        ell=c.build_chart(k);lengths[k]=ell
        print(k,"half-length",ell.str(55),flush=True)
    sq,rooterror,remainder=c.integrate_discrepancy()
    require(sq > 0, 'Certification condition failed: sq > 0')
    result=sq.sqrt()
    print("D^2",sq.str(60),flush=True)
    print("D",result.str(60),flush=True)
    tests=[rounded_certification(result,d) for d in [6,12,18,24,30,36]]
    old="0.203783759536049443826081"
    oldq=Fraction(old);ulp=Fraction(1,2*10**24)
    oldpass=result>exact(oldq-ulp) and result<exact(oldq+ulp)
    report={
      "quantity":"D_kappa: separate normalised arclength, smooth arcs only",
      "definition":"D^2 = int_0^1 (k_E(theta_E(v))-k_L(theta_L(v)))^2 dv; theta_i(0)=0, theta_i(1)=pi",
      "parameters":vars(args),"python_version":sys.version,"python_flint_version":flint.__version__,
      "normalisation":"Both full arcs start at theta=-pi and follow increasing theta; evenness reduces the integral to the centre-to-join half-arc variable v.",
      "half_lengths":{k:rational_bounds(v) for k,v in lengths.items()},
      "D_squared":rational_bounds(sq),"D":rational_bounds(result),
      "largest_inverse_x_radius_upper":str(rooterror),
      "outer_Taylor_remainder_bound_sum":str(remainder),
      "rounding_checks":tests,"published_24_place_value":old,
      "published_24_place_rounding_cell_contains_enclosure":bool(oldpass),
      "elapsed_seconds":time.time()-t,
      "method":"Real ball arithmetic, explicit polynomial-tail bounds, rigorous Taylor quadrature, residual/positive-speed inverse enclosure, inverse-series derivative enclosures.",
      "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    }
    Path(args.output).write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"rounding":tests,"published_value_certified":bool(oldpass),"seconds":time.time()-t},indent=2))
    if not oldpass:
        raise SystemExit("The enclosure does not certify the requested 24-place value; increase order or panels.")

if __name__=="__main__":main()
