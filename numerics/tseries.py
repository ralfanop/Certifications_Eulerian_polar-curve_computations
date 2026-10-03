"""Truncated Taylor series with interval coefficients over an arbitrary interval backend B.

A series S of order n represents sum_{k=0}^{n} S[k] tau^k (coefficients are backend intervals).
All recurrences are the standard automatic-differentiation ones; with interval coefficients they
enclose the true Taylor coefficients of the composed function at every point of the expansion
interval represented by the order-0 data.
"""
from fractions import Fraction

class TS:
    __slots__ = ("c", "B")
    def __init__(self, B, coeffs):
        self.B, self.c = B, list(coeffs)
    @property
    def n(self):
        return len(self.c) - 1
    @staticmethod
    def const(B, x, n):
        z = B.const(0)
        return TS(B, [x] + [z] * n)
    @staticmethod
    def var(B, x0, n):  # x0 + tau
        z = B.const(0)
        return TS(B, [x0, B.const(1)] + [z] * (n - 1))
    def _lift(self, o):
        if isinstance(o, TS):
            return o
        if isinstance(o, (int, Fraction)):
            o = self.B.const(o)
        return TS.const(self.B, o, self.n)
    def trunc(self, n):
        return TS(self.B, self.c[: n + 1])
    def __add__(self, o):
        o = self._lift(o); n = min(self.n, o.n)
        return TS(self.B, [self.c[k] + o.c[k] for k in range(n + 1)])
    __radd__ = __add__
    def __sub__(self, o):
        o = self._lift(o); n = min(self.n, o.n)
        return TS(self.B, [self.c[k] - o.c[k] for k in range(n + 1)])
    def __rsub__(self, o):
        return self._lift(o) - self
    def __neg__(self):
        z = self.B.const(0)
        return TS(self.B, [z - x for x in self.c])
    def scale(self, s):
        return TS(self.B, [x * s for x in self.c])
    def __mul__(self, o):
        if not isinstance(o, TS):
            o = self.B.const(o) if isinstance(o, (int, Fraction)) else o
            return self.scale(o)
        n = min(self.n, o.n)
        a, b = self.c, o.c
        out = []
        for k in range(n + 1):
            s = a[0] * b[k]
            for j in range(1, k + 1):
                s = s + a[j] * b[k - j]
            out.append(s)
        return TS(self.B, out)
    __rmul__ = __mul__
    def __truediv__(self, o):
        o = self._lift(o); n = min(self.n, o.n)
        a, b = self.c, o.c
        q = []
        for k in range(n + 1):
            s = a[k]
            for j in range(1, k + 1):
                s = s - b[j] * q[k - j]
            q.append(s / b[0])
        return TS(self.B, q)
    def deriv(self):
        return TS(self.B, [self.c[k] * k for k in range(1, self.n + 1)])

def ts_sqrt(a):
    B = a.B
    s = [B.sqrt(a.c[0])]
    two_s0 = s[0] * 2
    for k in range(1, a.n + 1):
        acc = a.c[k]
        for j in range(1, k):
            acc = acc - s[j] * s[k - j]
        s.append(acc / two_s0)
    return TS(B, s)

def ts_sincos(u):
    B = u.B
    s, c = [B.sin(u.c[0])], [B.cos(u.c[0])]
    for k in range(1, u.n + 1):
        ss, cc = B.const(0), B.const(0)
        for j in range(1, k + 1):
            ju = u.c[j] * j
            ss = ss + ju * c[k - j]
            cc = cc + ju * s[k - j]
        s.append(ss / k)
        c.append((B.const(0) - cc) / k)
    return TS(B, s), TS(B, c)
