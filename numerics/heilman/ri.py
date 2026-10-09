"""Exact rational interval arithmetic for the Heilman Appendix A certification.

Transcendental constants (pi, sqrt 2, log(1+sqrt 2)) are enclosed by integer fixed-point series at
scale 10^S with directed rounding of every term and an explicit tail bound; all subsequent
arithmetic is exact (Python Fractions).  No floating point is used in any decision."""
from fractions import Fraction as Fr
from math import isqrt

S = 800
U = 10**S

class RI:
    __slots__ = ("lo", "hi")
    def __init__(s, lo, hi=None):
        lo = Fr(lo); hi = lo if hi is None else Fr(hi)
        assert lo <= hi
        s.lo, s.hi = lo, hi
    def __add__(s, o): o = c(o); return RI(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__
    def __neg__(s): return RI(-s.hi, -s.lo)
    def __sub__(s, o): o = c(o); return RI(s.lo - o.hi, s.hi - o.lo)
    def __rsub__(s, o): return c(o) - s
    def __mul__(s, o):
        o = c(o); ps = (s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi); return RI(min(ps), max(ps))
    __rmul__ = __mul__
    def inv(s):
        assert s.lo > 0 or s.hi < 0
        return RI(1/s.hi, 1/s.lo)
    def __truediv__(s, o): return s * c(o).inv()
    def __rtruediv__(s, o): return c(o) * s.inv()
    def __pow__(s, k):
        r = RI(1)
        for _ in range(k): r = r * s
        return r
    def ge(s, x): return s.lo >= Fr(x)
    def le(s, x): return s.hi <= Fr(x)
    def gt(s, x): return s.lo > Fr(x)
    def lt(s, x): return s.hi < Fr(x)
    def width(s): return s.hi - s.lo

def c(x): return x if isinstance(x, RI) else RI(x)

def dec(s):  # exact rational from a decimal string such as "1.2843271408e17"
    return Fr(s)

def sqrt_int(n):
    a = isqrt(n * U * U)
    return RI(Fr(a, U), Fr(a + 1, U))

def _atan_inv(m):
    """arctan(1/m), m >= 2: alternating series; each term floored/ceiled at scale U."""
    lo = hi = 0; k = 0
    while True:
        den = (2*k + 1) * m**(2*k + 1)
        if U < den: break
        tl, th = U // den, -((-U) // den)
        if k % 2 == 0: lo += tl; hi += th
        else: lo -= th; hi -= tl
        k += 1
    # remaining alternating tail has absolute value < first omitted term < 1/U
    return RI(Fr(lo - 1, U), Fr(hi + 1, U))

def _atanh_fixed(xlo, xhi):
    """artanh(x) for x in [xlo, xhi] subset (0, 1/2), xlo, xhi integers at scale U (x = X/U).
    Positive series sum x^(2k+1)/(2k+1); lower sum uses xlo with floors, upper uses xhi with ceilings,
    plus the tail bound x^(2K+1)/((2K+1)(1-x^2))."""
    def run(X, up):
        s = 0; p = X; k = 0          # p = x^(2k+1) at scale U
        while p > 0:
            t = p // (2*k + 1) if not up else -((-p) // (2*k + 1))
            s += t
            p = (p * X * X) // (U * U) if not up else -((-p * X * X) // (U * U))
            k += 1
            if p < 1 and not up: break
            if up and p <= 1:
                # tail: x^(2k+1)/(2k+1)/(1-x^2) <= 2 * p (x<1/2), with p <= 1 ulp
                s += 2; break
        return s
    return RI(Fr(run(xlo, False), U), Fr(run(xhi, True) + 2, U))

PI = 16 * _atan_inv(5) - 4 * _atan_inv(239)
SQRT2 = sqrt_int(2)
_x = SQRT2 - 1                               # (y-1)/(y+1) with y = 1+sqrt2 equals sqrt2 - 1
_xl = int(_x.lo * U); _xh = -int(-_x.hi * U)
LOG1S2 = 2 * _atanh_fixed(_xl, _xh)          # log(1+sqrt2) = arcsinh(1) = 2 artanh(sqrt2-1)

def selftest():
    assert PI.width() < Fr(1, 10**790) and PI.ge(Fr(314159265358979323846, 10**20))
    assert PI.le(Fr(314159265358979323847, 10**20))
    assert SQRT2.lo**2 <= 2 <= SQRT2.hi**2
    assert LOG1S2.width() < Fr(1, 10**790)
    assert LOG1S2.ge(Fr("0.88137358701954302523")) and LOG1S2.le(Fr("0.88137358701954302524"))
    return True
