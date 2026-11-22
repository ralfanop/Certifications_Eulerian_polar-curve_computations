Manuscript 15 — FLINT/Arb certificate of equation (295)
Date: 2026-11-22

Source archive: M15_QUARTER(1).zip
SHA-256: 415a38a0bc0f777402bd7397aaf59f01abf765d5bcd37000092353ca248cf8f8
15.tex SHA-256: 2f5ced66bfd9248d1ce14937d1e38cd446890d7ac02c843f9ba8a6f8ee77fbb2
Source labels: eq:catenoid-cl-angle, eq:catenoid-cl-angle-degrees

The unique positive root u_* of u*tanh(u) = 1 is enclosed by exact
dyadic endpoints with strictly opposite interval signs. Uniqueness
follows from tanh(u) + u*sech(u)^2 > 0 for u > 0.
The enclosure is propagated through lambda_CL = sqrt(u_*^2-1),
alpha_CL = 2*atan(1/lambda_CL), and degrees = alpha_CL*180/pi.
Equivalent formulas using sinh(u_*) are cross-checked by overlap.

Working precision: 3,600,000 bits.
Relative accuracy threshold: 3,400,000 bits.
Actual relative accuracy of alpha_CL, radians and degrees: 3,599,870 bits.
Equation (296)'s 50 decimal places match both truncation and rounding.

Reproduce with Python and python-flint 0.9.0 (FLINT 3.6.0):
    python certify_M15_eq295.py --certificate M15_eq295_balls.json

M15_eq295_run.txt: actual run log (PASS).
M15_eq295_balls.json: lossless dyadic midpoint/radius data, and root
bracket endpoints and sign-test enclosures. Each exact dyadic is
represented by mantissa_hex * 2**exponent_2. The JSON is intentionally
not rounded to a short decimal display.

The original manuscript is not modified. This is a numerical certificate,
not a new Lean 4 formalisation.
