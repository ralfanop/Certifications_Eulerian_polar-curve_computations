#!/usr/bin/env python3
"""M16 v16.4 §13: Arb enclosures of NEW mixed periodic-wave fourth expressions.

Not the spatial Laplacian expressions certified for v16.1.
The spectral reindexing and Euler's even-zeta formulae are analytic inputs,
not proved by this numerical script. No input is a binary float.
"""
import flint
from flint import arb, ctx

ctx.prec = 10000
MIN_RELATIVE_BITS = 8182
assert ctx.prec == 10000
pi = arb.pi()
z2 = pi**2 / 6
z4 = pi**4 / 90
z8 = pi**8 / 9450

# Two independently evaluated Arb formulas, algebraically equivalent.
wave_zeta_reindex = (4*z2*z4 - 2*z4**2 + z8) / 128
wave_pi_reduced = pi**6 / 17280 - pi**8 / 907200
dirac_fourth = pi**2 - pi**4 / 12
mixed_unperturbed_fourth = dirac_fourth + wave_pi_reduced

# The two enclosures rigorously overlap and differ by much less than 2^-9000.
assert abs(wave_zeta_reindex-wave_pi_reduced) < arb(1)/arb(2**9000)
values = {
    "wave_nonresonant_fourth_zeta": wave_zeta_reindex,
    "wave_nonresonant_fourth_pi": wave_pi_reduced,
    "mixed_W_R_plus_D3_fourth": mixed_unperturbed_fourth,
}
# 12dp exact decimal rounding centres; all are integers / 10**12.
printed = {
    "wave_nonresonant_fourth_zeta": 45176809575,
    "wave_nonresonant_fourth_pi": 45176809575,
    "mixed_W_R_plus_D3_fourth": 1797356957831,
}
half_ulp = arb(1)/arb(2*10**12)

print("Manuscript 16 v16.4 mixed wave-Dirac scalar expressions")
print("FLINT:", flint.__version__, "Arb working bits:", ctx.prec)
for key,val in values.items():
    assert val.is_finite(), (key, "not finite")
    assert val > 0, (key, "not positive")
    bits = val.rel_accuracy_bits()
    assert bits >= MIN_RELATIVE_BITS, (key, bits)
    centre = arb(printed[key])/arb(10**12)
    assert abs(val-centre) < half_ulp, (key, "12dp rounding not enclosed")
    print(key, val.str(48, radius=True, more=True),
          "relative_bits", bits, "12dp_numerator", printed[key])
print("SUCCESS v16.4: 10000-bit Arb closed-expression enclosures, all >=8182 relative bits")
