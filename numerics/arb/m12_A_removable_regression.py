#!/usr/bin/env python3
"""Independent low-precision regression for the removable singularity in M12 A(s).

This is NOT a million-digit certificate.  It checks the analytic branch
against A(s) = 1/2 + 1/expm1(s) - 1/s at positive rational arguments.
"""
from flint import acb, arb, ctx

ctx.prec = 256

def regularized_A(s):
    w = s*s/16
    return (s/12) * w.hypgeom_0f1(arb(5)/2) / w.hypgeom_0f1(arb(3)/2)

def direct_A(s):
    return acb(1)/2 + 1/s.expm1() - 1/s

for denominator in (4, 8, 16, 32, 64, 128):
    s = acb(1)/denominator
    a = regularized_A(s)
    b = direct_A(s)
    assert (a-b).real.contains(0), (denominator, a, b)
    assert a.imag.contains(0) and b.imag.contains(0)
    assert a.real > 0
    # Negative control: an extra factor w changes the simple zero into
    # a cubic zero. Reject this distinct function using rigorous balls.
    w = s*s/16
    wrong = a*w
    assert not (wrong-b).real.contains(0), (
        "spurious cubic branch overlaps", denominator, wrong, b
    )
    print("PASS: A(1/%d), correct enclosures overlap; cubic branch excluded" % denominator)
print("PASS: removable singularity regression + negative controls (256-bit pilot only)")
