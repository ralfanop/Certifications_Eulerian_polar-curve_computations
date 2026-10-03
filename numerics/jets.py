"""Second-order jets (value, first derivative, second derivative) over an arbitrary interval backend.

A backend object B must provide: B.sin, B.cos, B.sqrt (interval functions), B.const(Fraction),
and interval objects supporting + - * / with each other.
"""
from fractions import Fraction

class Jet:
    __slots__ = ("v", "d", "dd", "B")
    def __init__(self, B, v, d, dd):
        self.B, self.v, self.d, self.dd = B, v, d, dd
    @staticmethod
    def const(B, c):
        z = B.const(Fraction(0))
        return Jet(B, c, z, z)
    def _lift(self, o):
        if isinstance(o, Jet):
            return o
        if isinstance(o, (int, Fraction)):
            o = self.B.const(Fraction(o))
        return Jet.const(self.B, o)
    def __add__(self, o):
        o = self._lift(o); return Jet(self.B, self.v + o.v, self.d + o.d, self.dd + o.dd)
    __radd__ = __add__
    def __sub__(self, o):
        o = self._lift(o); return Jet(self.B, self.v - o.v, self.d - o.d, self.dd - o.dd)
    def __rsub__(self, o):
        return self._lift(o) - self
    def __neg__(self):
        z = self.B.const(Fraction(0))
        return Jet(self.B, z - self.v, z - self.d, z - self.dd)
    def __mul__(self, o):
        o = self._lift(o)
        return Jet(self.B, self.v * o.v, self.d * o.v + self.v * o.d,
                   self.dd * o.v + 2 * (self.d * o.d) + self.v * o.dd)
    __rmul__ = __mul__
    def __truediv__(self, o):
        o = self._lift(o)
        q = self.v / o.v
        q1 = (self.d - q * o.d) / o.v
        q2 = (self.dd - 2 * (q1 * o.d) - q * o.dd) / o.v
        return Jet(self.B, q, q1, q2)
    def __rtruediv__(self, o):
        return self._lift(o) / self

def jsin(u):
    B = u.B
    s, c = B.sin(u.v), B.cos(u.v)
    return Jet(B, s, c * u.d, c * u.dd - s * (u.d * u.d))

def jcos(u):
    B = u.B
    s, c = B.sin(u.v), B.cos(u.v)
    return Jet(B, c, (B.const(Fraction(0)) - s) * u.d, (B.const(Fraction(0)) - c) * (u.d * u.d) - s * u.dd)
