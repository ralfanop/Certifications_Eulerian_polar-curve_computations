#!/usr/bin/env python3
"""M15 editorial revision 2026-11-13, Section 2.4, Proposition on Eulerian apex.

Rigorously checks at 10000 Arb bits:
* the exact finite Eulerian slope identities s_3=s_5=2, s_7=35/18;
* the N=10 endpoint of the manuscript's UNIFORM bound:
       5/sqrt(2*pi)+40/(9*pi**10) < 2.

This does NOT prove that the analytical Gaussian/tail estimate holds,
that its upper bound decreases for every N>=10, or the stated two-term
asymptotics. These require independent Lean/analytic proofs.

All nonzero computed Arb expressions have individually checked *actual*
certified relative accuracy >= 8182 bits; no binary-float inputs.
"""
from math import comb, factorial
from fractions import Fraction

from flint import arb, ctx
import flint

ctx.prec = 10000
assert ctx.prec == 10000
MIN_BITS = 8182


def eulerian(n: int, k: int) -> int:
    """Exact inclusion-exclusion formula for Eulerian number E(n,k)."""
    assert n >= 1 and 0 <= k < n
    return sum(
        ((-1) ** j) * comb(n + 1, j) * ((k + 1 - j) ** n)
        for j in range(k + 2)
    )


def central_slope(n: int) -> Fraction:
    """Exact rational central ascending slope for odd n>=3."""
    assert n >= 3 and n % 2 == 1
    m = (n - 1) // 2
    return Fraction(n + 1, factorial(n)) * (eulerian(n, m) - eulerian(n, m - 1))


slopes = {n: central_slope(n) for n in (3, 5, 7)}
assert slopes[3] == Fraction(2)
assert slopes[5] == Fraction(2)
assert slopes[7] == Fraction(35, 18)
assert slopes[7] < Fraction(2)
for n, v in slopes.items():
    print(f"s_{n} exact rational: {v}")

# Arb must compute pi internally, not import a binary floating-point approximation.
zero = arb(0)
one = arb(1)
two = arb(2)
pi = arb.pi()
sqrt_2_pi = (two * pi).sqrt()
gaussian_endpoint = arb(5) / sqrt_2_pi
tail_endpoint = arb(40) / (arb(9) * pi ** 10)
uniform_endpoint = gaussian_endpoint + tail_endpoint
strict_gap = two - uniform_endpoint

# A completely independent rearrangement of the n=9 (N=10) bound.
N = arb(10)
endpoint_direct = (
    (arb(216) * N ** 2 / (pi * (N + 2) ** 3)).sqrt()
    + (arb(4) * N / ((N - 1) * pi ** 10))
)
assert endpoint_direct.overlaps(uniform_endpoint), (
    "N=10 endpoint formulations do not overlap"
)

assert gaussian_endpoint > zero
assert tail_endpoint > zero
assert uniform_endpoint > zero
assert strict_gap > zero, "The manuscript strict uniform upper bound is not verified"

values = {
    "pi": pi,
    "sqrt(2*pi)": sqrt_2_pi,
    "s7=35/18": arb(35) / arb(18),
    "N10 Gaussian upper term": gaussian_endpoint,
    "N10 tail upper term": tail_endpoint,
    "N10 total uniform upper": uniform_endpoint,
    "N10 independently evaluated upper": endpoint_direct,
    "strict margin 2 - N10 bound": strict_gap,
}

print("M15 Section 2.4 Eulerian apex — Arb 10000-bit scalar verification")
print("python-flint:", flint.__version__)
print("ctx.prec:", ctx.prec)
min_observed = 10000
for name, ball in values.items():
    bits = ball.rel_accuracy_bits()
    min_observed = min(min_observed, bits)
    assert ball.is_finite(), name
    assert bits >= MIN_BITS, (name, bits)
    print(name, "| certified relative bits:", bits,
          "| interval:", ball.str(55, radius=True, more=True))

print("minimum certified relative bits:", min_observed)
print("SUCCESS: exact finite slopes and N=10 strict Arb uniform apex bound, >=8182 bits")
