# Hepner (1962), p. 355: check of the γ-matrix relations

Source: W. A. Hepner, *The inhomogeneous Lorentz group and the conformal group*, Nuovo Cimento **26** (1962) 351–368, DOI 10.1007/BF02787046.

Status: **checked by us** (exact matrix identities in floating point with explicit 4×4 Dirac matrices; 15 Oct 2026). Files: `hepner355_check.py`, `hepner355_check.log`.

We use Euclidean (Pauli-metric) Dirac matrices with γ_kγ_l + γ_lγ_k = 2δ_kl and γ₅ = γ₁γ₂γ₃γ₄. We read the six-dimensional M_μν of (1), p. 354, with the index convention under which the angular-momentum relations (2) hold. Under that convention the following relations hold: (4), (2a), (2b), the first relation of (2c), [γ_i⁽⁺⁾, γ_i⁽⁻⁾] = −2iM₅₆, (2d), and footnote (5).

The second relation of (2c) is printed as

  [γ_i⁽⁺⁾, γ_k⁽⁻⁾] = 4M_ik  (i ≠ k).

It holds with coefficient 2:

  [γ_i⁽⁺⁾, γ_k⁽⁻⁾] = 2M_ik  (i ≠ k).

Directly: γ_i⁽⁺⁾γ_k⁽⁻⁾ = ½(1 + γ₅)γ_iγ_k and γ_k⁽⁻⁾γ_i⁽⁺⁾ = −½(1 − γ₅)γ_iγ_k, so the commutator is γ_iγ_k = 2M_ik.

Not checked:
- whether the normalisation (i/√2)·½(1 ± γ₅)γ_k of Hepner's generators X₁…X₁₅ reproduces the commutation relations of Hill (Phys. Rev. 67, 358, 1945, Table II) once the corrected coefficient is used;
- the reference to Hill itself.

## Reproduce

```
python3 -I hepner355_check.py > hepner355_check.log
```
