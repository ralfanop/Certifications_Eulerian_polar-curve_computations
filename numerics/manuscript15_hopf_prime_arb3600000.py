"""Arb enclosures for Manuscript 15 Appendix B: Hopf-circle/prime scalar.
Analytic inputs: zeta(0)=-1/2, zeta'(0)=-log(2*pi)/2.
This is NOT a numerical summation of the divergent product over primes.
"""
from hashlib import sha256
from flint import arb, ctx, fmpz

WORK_BITS = 3_600_000
MIN_BITS = 3_400_000
DIGITS = 1_000_001
ctx.prec = WORK_BITS


def decimal_power(e):
    if e >= 0:
        return arb(fmpz(10) ** e)
    return arb(1) / arb(fmpz(10) ** (-e))


def certify(name, x):
    assert x.is_finite(), name
    accuracy = x.rel_accuracy_bits()
    assert accuracy >= MIN_BITS, (name, accuracy)
    assert x > 0 or x < 0, name
    sign = "+" if x > 0 else "-"
    y = abs(x)
    e = 0
    while y < decimal_power(e):
        e -= 1
    while y >= decimal_power(e + 1):
        e += 1
    assert y >= decimal_power(e) and y < decimal_power(e + 1), name
    # Scale to DIGITS significant decimal digits. The exact integer scale
    # lies within the working precision for all quantities tested here.
    scale = DIGITS - 1 - e
    assert scale >= 0
    scaled = y * arb(fmpz(10) ** scale)
    # Every floor is an integer; a unique integer in its Arb enclosure
    # certifies the exact truncation. Repeat for rounding (half-up).
    prefix = scaled.floor().unique_fmpz()
    rounded = (scaled + arb(1) / 2).floor().unique_fmpz()
    assert prefix is not None and rounded is not None, name
    p, r = str(prefix), str(rounded)
    assert len(p) == DIGITS, (name, len(p))
    assert len(r) in (DIGITS, DIGITS + 1), (name, len(r))
    print(f"{name}: rel_bits={accuracy} sign={sign} decimal_exponent={e} "
          f"significant_digits={DIGITS} trunc_sha256={sha256(p.encode()).hexdigest()} "
          f"rounded_sha256={sha256(r.encode()).hexdigest()}", flush=True)
    return sign, e, prefix, rounded


def main():
    print(f"working_bits={WORK_BITS} min_relative_bits={MIN_BITS} "
          f"required_significant_digits={DIGITS}", flush=True)
    pi = arb.pi()
    log2pi = (2 * pi).log()
    z0 = -arb(1) / 2
    dz0 = -log2pi / 2
    h0 = dz0 / z0
    g0 = h0 / z0
    prime = (-g0).exp()
    circle = (-4 * dz0).exp()
    direct = 4 * pi ** 2
    for name, x in [("pi", pi), ("log_2pi", log2pi), ("zeta_0", z0),
                    ("zeta_prime_0", dz0), ("log_derivative_0", h0),
                    ("continued_value_0", g0)]:
        certify(name, x)
    a = certify("prime_regularized_scalar", prime)
    b = certify("hopf_circle_determinant", circle)
    c = certify("four_pi_squared", direct)
    assert prime.overlaps(circle) and circle.overlaps(direct)
    assert a == b == c, "million-digit fingerprints disagree"
    # Numerical sample only; the algebraic identity for all M is Lean's job.
    for M in range(1, 18):
        k = M - 1
        lhs = arb(1) / (2 * (2 * pi) ** (2 * k))
        rhs = arb(1) / (2 * circle ** k)
        assert lhs.overlaps(rhs), M
        assert certify(f"b_{M}_{2*M}_direct", lhs) == certify(
            f"b_{M}_{2*M}_hopf", rhs), M
    print("SUCCESS: relative accuracy, unique significant decimal prefixes "
          "and unique rounded magnitudes verified", flush=True)


if __name__ == "__main__":
    main()
