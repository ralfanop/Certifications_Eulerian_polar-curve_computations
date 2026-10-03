"""Independent rigorous interval arithmetic on fixed-point dyadic numbers.

Every quantity is an interval [lo, hi] * 2^-P with Python integers lo <= hi.  Only exact integer
operations are used; every rounding is directed outward (floor for lower ends, ceil for upper
ends).  Elementary functions are evaluated from Taylor series with explicit tail bounds, and
pi from Machin's formula with explicit tail bounds.  No floating point and no external library
is involved, so this module is independent of mpmath (used by the primary certificates).
"""
from fractions import Fraction
from math import isqrt

P = 560  # working precision in bits (about 168 decimal digits)

def _fl(num, den):  # floor(num/den), den > 0
    return num // den
def _ce(num, den):  # ceil(num/den), den > 0
    return -((-num) // den)

class FI:
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = lo, hi

    # ---- construction ----
    @staticmethod
    def frac(x):
        x = Fraction(x)
        n, d = x.numerator << P, x.denominator
        return FI(_fl(n, d), _ce(n, d))
    @staticmethod
    def hull(a, b):
        return FI(min(a.lo, b.lo), max(a.hi, b.hi))

    # ---- arithmetic ----
    def __add__(self, o):
        o = _c(o); return FI(self.lo + o.lo, self.hi + o.hi)
    __radd__ = __add__
    def __neg__(self):
        return FI(-self.hi, -self.lo)
    def __sub__(self, o):
        o = _c(o); return FI(self.lo - o.hi, self.hi - o.lo)
    def __rsub__(self, o):
        return _c(o) - self
    def __mul__(self, o):
        o = _c(o)
        ps = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return FI(min(ps) >> P, -((-max(ps)) >> P))
    __rmul__ = __mul__
    def __truediv__(self, o):
        o = _c(o)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError("interval division by an interval containing 0")
        nums = (self.lo << P, self.hi << P)
        lo = min(_fl(n, d) if d > 0 else _fl(-n, -d) for n in nums for d in (o.lo, o.hi))
        hi = max(_ce(n, d) if d > 0 else _ce(-n, -d) for n in nums for d in (o.lo, o.hi))
        return FI(lo, hi)
    def __rtruediv__(self, o):
        return _c(o) / self
    def __pow__(self, k):
        assert isinstance(k, int) and k >= 0
        r = FI(1 << P)
        for _ in range(k):
            r = r * self
        if k % 2 == 0 and self.lo < 0 < self.hi:
            r = FI(0, r.hi)
        return r
    def abs(self):
        if self.lo >= 0: return self
        if self.hi <= 0: return -self
        return FI(0, max(-self.lo, self.hi))
    # ---- predicates (rigorous) ----
    def lt(self, o):  # certainly self < o
        return self.hi < _c(o).lo
    def gt(self, o):
        return self.lo > _c(o).hi
    def contains0(self):
        return self.lo <= 0 <= self.hi
    def mid(self):  # exact dyadic midpoint (rounded down), as thin interval
        return FI((self.lo + self.hi) >> 1)
    def to_fraction_bounds(self):
        return Fraction(self.lo, 1 << P), Fraction(self.hi, 1 << P)
    def __repr__(self):
        a, b = self.to_fraction_bounds()
        return f"FI[{float(a):.17g}, {float(b):.17g}]"

def _c(x):
    return x if isinstance(x, FI) else FI.frac(x)

def sqrt(x):
    assert x.lo >= 0, "sqrt of negative"
    lo = isqrt(x.lo << P)
    s = isqrt(x.hi << P)
    hi = s if s * s == (x.hi << P) else s + 1
    return FI(lo, hi)

ONE = FI(1 << P)

def _sin_cos_thin(m):
    """sin and cos of an exact dyadic m (thin FI) with |m| <= 8, by Taylor series + tail bound."""
    assert m.lo == m.hi
    a = Fraction(abs(m.lo), 1 << P)
    assert a <= 8
    s, c = FI(0), FI(0)
    term = ONE  # m^k / k!
    k = 0
    while True:
        if k % 4 == 0: c = c + term
        elif k % 4 == 1: s = s + term
        elif k % 4 == 2: c = c - term
        else: s = s - term
        k += 1
        term = term * m / k
        # For k >= 2|m|+1 the terms decrease at least geometrically with ratio 1/2, so the
        # tail sum_{j>=k} |m|^j/j! is at most 2*|m|^k/k! (term encloses m^k/k!).
        if k >= 2 * a + 1 and term.abs().hi <= 2:
            bnd = 2 * term.abs().hi + 1
            e = FI(-bnd, bnd)
            return s + e, c + e

def sin(x):
    m = x.mid()
    r = max(x.hi - m.lo, m.lo - x.lo) + 1
    s, _ = _sin_cos_thin(m)
    return s + FI(-r, r)  # |sin x - sin m| <= |x - m|

def cos(x):
    m = x.mid()
    r = max(x.hi - m.lo, m.lo - x.lo) + 1
    _, c = _sin_cos_thin(m)
    return c + FI(-r, r)

def _arctan_inv(n):
    """arctan(1/n) for integer n >= 2, alternating series with tail bound."""
    x = FI.frac(Fraction(1, n))
    x2 = x * x
    s, p, k = FI(0), x, 0
    while True:
        t = p / (2 * k + 1)
        s = s + t if k % 2 == 0 else s - t
        k += 1
        p = p * x2
        if p.hi < 4:
            e = FI(-p.hi - 2, p.hi + 2)
            return s + e

PI = FI.frac(16) * _arctan_inv(5) - FI.frac(4) * _arctan_inv(239)

def selftest():
    lo, hi = PI.to_fraction_bounds()
    assert Fraction(314159265358979323846, 10**20) < lo < hi < Fraction(314159265358979323847, 10**20)
    s, c = _sin_cos_thin(FI.frac(Fraction(1, 2)))
    v = s * s + c * c
    assert v.lo <= (1 << P) <= v.hi
    return True

if __name__ == "__main__":
    print("selftest", selftest(), PI)
