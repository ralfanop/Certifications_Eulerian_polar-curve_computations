"""Manuscript 14.119 (2026-11-17): certify Eq. (201), both special
points, Eq. (95)-(97) new zeta terms, and Eq. (175)-(179).

3,600,000 working bits, >=3,400,000 relative accuracy for nonzero
mathematical quantities. The CODATA central decimal and standard
uncertainty are INPUTS, not experimentally validated to this precision.
"""
from fractions import Fraction
from hashlib import sha256
from math import factorial
from flint import arb, ctx, fmpz

WORK_BITS = 3_600_000
MIN_BITS = 3_400_000
DIGITS = 1_000_001
ctx.prec = WORK_BITS

P = tuple(map(Fraction, ("6", "1/5", "-19/3150", "31/94500", "-14089/654885000", "132731/85135050000", "-19378097/160905244500000", "798055301/82061674695000000", "-8765082658861/10805060707090650000000", "188905177031/2723964884140500000000", "-369024804546778819/61060478561839972215000000000", "326577481196239877/610604785618399722150000000000")))
R = tuple(map(Fraction, ("0", "-3/10", "-27/2800", "9/28000", "-23/1379840", "121483/112112000000", "-106721/1358280000000", "18232603/3001798800000000", "-74462871059417/151774789630464000000000", "4697904816091/114787656023040000000000", "-3000951506527034377/857694513680715110400000000000", "1238782192338196421/4062763485856018944000000000000")))
TERMS = {
    9: Fraction("43867/47085412305447419904000"),
    10: Fraction("-174611/16442524932061003776000000"),
    11: Fraction("77683/635339163374837185904640000"),
}

def rational(q):
    return arb(fmpz(q.numerator)) / arb(fmpz(q.denominator))

def decimal_power(e):
    if e >= 0:
        return arb(fmpz(10)**e)
    return arb(1) / arb(fmpz(10)**(-e))

def certify(name, x):
    assert x.is_finite(), name
    bits = x.rel_accuracy_bits()
    assert bits >= MIN_BITS, (name, bits)
    assert x > 0 or x < 0, name
    y = abs(x)
    exponent = 0
    while y < decimal_power(exponent):
        exponent -= 1
    while y >= decimal_power(exponent + 1):
        exponent += 1
    assert y >= decimal_power(exponent) and y < decimal_power(exponent+1), name
    scale = DIGITS - 1 - exponent
    assert scale >= 0
    scaled = y * arb(fmpz(10) ** scale)
    prefix = scaled.floor().unique_fmpz()
    assert prefix is not None, name
    s = str(prefix)
    assert len(s) == DIGITS, (name, len(s))
    print(f"{name}: relative_bits={bits} sign={'+' if x>0 else '-'} "
          f"decimal_exponent={exponent} digits={DIGITS} "
          f"prefix_first_60={s[:60]} sha256={sha256(s.encode()).hexdigest()}", flush=True)
    return x

def logs(a):
    out = [Fraction(0)] * len(a)
    for j in range(1, len(a)):
        out[j] = a[j] - sum((k*out[k]*a[j-k] for k in range(1,j)), Fraction(0))/j
    return out

def verify_coefficients():
    b = [Fraction(1, factorial(2*k+1)) for k in range(13)]
    a = logs(b)
    c = logs([6*v for v in b[1:]])
    assert len(P) == len(R) == 12
    for n in range(12):
        assert sum(a[k+1]*P[n-k] for k in range(n+1)) == int(n == 0)
        assert R[n] == -sum(P[k]*c[n-k] for k in range(n+1))
    for m, coeff in TERMS.items():
        assert coeff == a[m]/8**m
    print("Exact rational coefficients verified through x^20", flush=True)
    return a

def poly(coefs, t):
    out = arb(0)
    for coef in reversed(coefs):
        out = out*t+rational(coef)
    return out

def parry(a, pi):
    expected = {
        2: ("3000382121419998992644032422930461275391872303378219", 31),
        8: ("18628778927723939629442982735721165694763355622923443", 187),
    }
    for q, (prefix50, n) in expected.items():
        t = arb(1)/q
        x = certify(f"x_q{q}", t.sqrt())
        beta = certify(f"beta_q{q}", x.sinh()/x)
        J = certify(f"J_q{q}", (6/t).log())
        rho = certify(f"rho_q{q}", -(beta-1).log()/beta.log())
        direct = (x/(x.sinh()-x)).log()/beta.log()
        assert rho.overlaps(direct), q
        assert n-1 < rho and rho < n, q
        # Exact 50 digits after the decimal point, as printed in manuscript.
        f = (rho * arb(fmpz(10)**50)).floor().unique_fmpz()
        assert f is not None and str(f) == prefix50, (q, f)
        assert beta**(n-1)*(beta-1) < 1 < beta**n*(beta-1)
        approx = certify(f"rho_truncated_q{q}", (poly(P,t)*J+poly(R,t))/t)
        certify(f"rho_minus_truncated_q{q}", rho-approx)
        if q == 8:
            logbeta = certify("log_beta_q8", beta.log())
            partial = sum((rational(a[m]/8**m) for m in range(1,12)), arb(0))
            tail = certify("log_beta_q8_minus_11_terms", logbeta-partial)
            # Alternating series gives a negative remainder after the odd term.
            assert rational(a[12]/8**12) < tail < 0
    for m, coeff in TERMS.items():
        exact = certify(f"rational_zeta_term_{m}", rational(coeff))
        from_zeta = certify(f"direct_zeta_term_{m}",
            (-1)**(m+1) * arb(2*m).zeta() / (m*(8*pi*pi)**m))
        assert exact.overlaps(from_zeta), m

def permeability(pi):
    sphere = certify("four_pi", 4*pi)
    density = certify("sphere_density", 1/sphere)
    historical = certify("historical_mu0", sphere/10**7)
    central = rational(Fraction("1.25663706127e-6"))
    uncertainty = rational(Fraction("2e-16"))
    ratio = certify("central_to_historical_ratio", central/historical)
    delta = certify("central_relative_discrepancy", ratio-1)
    sigma = certify("relative_standard_uncertainty", uncertainty/historical)
    assert delta < 0 and -delta < sigma
    assert rational(Fraction("-1.32034e-10")) < delta < rational(Fraction("-1.32032e-10"))
    assert rational(Fraction("0.999999999865")) < ratio < rational(Fraction("0.999999999875"))
    assert (central*10**7*density).overlaps(ratio)
    print("CODATA comparison only: empirical standard uncertainty exceeds central discrepancy.", flush=True)

def main():
    print(f"working_bits={WORK_BITS} min_relative_bits={MIN_BITS}", flush=True)
    a = verify_coefficients()
    pi = certify("pi", arb.pi())
    parry(a, pi)
    permeability(pi)
    print("SUCCESS: all mathematical enclosures and exact coefficient checks passed.", flush=True)

if __name__ == "__main__":
    main()

