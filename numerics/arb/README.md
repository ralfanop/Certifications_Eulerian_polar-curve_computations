# Arb certificates for manuscript V001 (Eulerian polar curve)

Every decimal printed in V001 has an Arb (ball arithmetic, FLINT) certificate in this folder,
in addition to the `mpmath.iv` and `ia_fixed` certificates of `numerics/` (README §2).
Library: python-flint 0.9.0. The workflow `.github/workflows/v001-arb.yml` reruns everything
and commits its logs here.

Criterion: a decimal printed as `≈ d` is certified when the Arb enclosure lies strictly inside
its rounding cell (d − ½·10⁻ᵏ, d + ½·10⁻ᵏ). A decimal printed as `d…` is certified when the
enclosure lies in [d, d + 10⁻ᵏ). Every comparison is a certain Arb comparison between balls,
or an exact comparison of rationals.

| Folder / file | V001 values | Method | Logs |
| --- | --- | --- | --- |
| `hstar80/` (26 September 2026) | h_* to 80 places, hence Eq. (70) to 20 places and h_* ≈ 0.0492979 | Q(L) > L from a supporting-line witness, with margin 1.344·10⁻⁸⁰. Q(U) < U from strict concavity outside θ ∈ [1.98, 2.22], plus an adaptive dyadic cover of [1.98, 2.22] by 2589 panels (max depth 133) with Arb mean-value bounds. 768 bits. `verify_hstar_80.py` replays the stored certificate using Arb only | `CERTIFICATION_RUN_OUTPUT.txt` (original run on macOS), `verify_hstar_80_ci.log` |
| `dkappa/` (September 2026, V422–V423) | Eq. (50) D_κ to 24 places; the half-lengths L_E and L_L | Validated Taylor quadrature, inversion of the arclength charts and outer remainder in Arb (see `D_K_CERTIFICATION_NOTE.pdf`). 256 bits | `certify_dk_ci.log` (the rerun reproduces the stored enclosures exactly), `verify_certificate_ci.log` |
| `v001_arb_decimals.py` (31 October 2026) | All other printed decimals: Eqs (6), (27)–(29), (33), (47), (48), Table 1, 0.0847669…, Eqs (59)–(61), Eq. (71) b_H, the 0.94 % and "about 42 %" gains, Eq. (72), the Montgomery–Taylor constants 1.3274992963… and 0.6725007… (§3.11), and Eq. (93) c₆₆₉, c₆₇₁. Also the two curve lengths 5.5510… and 5.5243…, the margin 1.34·10⁻⁸⁰, 333/106 < π < 355/113 and 670 < 216π − 15/2 < 672 | Closed forms with Arb's `Si`, `atan`, `sin`, `cos`. θ_* is bracketed by a certified sign change of S(θ) (Eq. 59), which is strictly increasing by Thm 3.12. b_H and the gains use the h_* certificate; the lengths use the D_κ certificate. c_n is computed exactly from the Eulerian recurrence. 768 bits; 4 negative controls | `v001_arb_decimals.log` |

Reproduce:

```
pip install python-flint==0.9.0 mpmath==1.4.1   # mpmath only for certify_hstar_80.py and reference_direct.py
cd hstar80 && python verify_hstar_80.py
cd ../dkappa && python certify_dk.py --order 32 --panels 64 --output /tmp/dk.json && python verify_certificate.py
cd .. && python v001_arb_decimals.py
```

`hstar80/` and `dkappa/` are deposited unchanged from the author's certified packages V426–V432;
their SHA-256 sums match `dkappa/MANIFEST_SHA256.txt` and the `script_sha256` fields of the
certificates. Their internal numbering is that of V423–V427: Theorems 3.13 and 3.14 cited there are V001's
Theorems 3.12 (strict concavity of f) and 3.13 (Q(h) − h strictly decreasing).
