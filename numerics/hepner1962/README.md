# Hepner (1962), p. 355: check of the γ-matrix relations

Source: W. A. Hepner, *The inhomogeneous Lorentz group and the conformal group*, Nuovo Cimento **26** (1962) 351–368, DOI 10.1007/BF02787046.

Status: **checked by us** (exact matrix identities in floating point with explicit 4×4 Dirac matrices; 15 Oct 2026). Files: `hepner355_check.py`, `hepner355_check.log`.

We use Euclidean (Pauli-metric) Dirac matrices with γ_kγ_l + γ_lγ_k = 2δ_kl and γ₅ = γ₁γ₂γ₃γ₄. We read the six-dimensional M_μν of (1), p. 354, with the index convention under which the angular-momentum relations (2) hold. Under that convention the following relations hold: (4), (2a), (2b), the first relation of (2c), [γ_i⁽⁺⁾, γ_i⁽⁻⁾] = −2iM₅₆, (2d), and footnote (5).

The second relation of (2c) is printed as

  [γ_i⁽⁺⁾, γ_k⁽⁻⁾] = 4M_ik  (i ≠ k).

It holds with coefficient 2:

  [γ_i⁽⁺⁾, γ_k⁽⁻⁾] = 2M_ik  (i ≠ k).

Directly: γ_i⁽⁺⁾γ_k⁽⁻⁾ = ½(1 + γ₅)γ_iγ_k and γ_k⁽⁻⁾γ_i⁽⁺⁾ = −½(1 − γ₅)γ_iγ_k, so the commutator is γ_iγ_k = 2M_ik.

## Against Hill's Table II (`hill_table_check.py`, `hill_table_check.log`)

Reference: E. L. Hill, *On accelerated coordinate systems in classical and relativistic mechanics*, Phys. Rev. **67** (1945) 358–363, Table II on p. 362. Its rows and columns list [X_a, X_b], as checked on [X₁₅, X₁] = −X₁ with X₁ = −∂_x and X₁₅ = x∂_x + ….

We test the spatial sub-algebra, with c = 1: translations X₁–X₃, rotations X₅–X₇, accelerations X₁₁–X₁₃ and dilatation X₁₅, 46 relations in all. The time components are left out, because Hepner uses x₄ = it while Hill uses t. Hepner's matrices are X_k = t·½(1 + γ₅)γ_k, X₁₀₊ₖ = a·½(1 − γ₅)γ_k, X₅ = −½γ₂γ₃, X₆ = −½γ₃γ₁, X₇ = −½γ₁γ₂ and X₁₅ = −½γ₅.

- With Hepner's choice t = a = z₀ = i/√2, all 46 relations of Table II hold.
- With t = αz₀ and a = z₀/α (α = 2, −3, i, 0.5 + 0.7i), all hold. This confirms Hepner's remark on p. 356 that translations may be rescaled by α and accelerations by 1/α.
- With t = a = 1, or t = a = 1/√2, 9 relations fail.

So Hill's relations fix the product t·a = z₀² = −1/2. With equal factors for translations and accelerations, the factor is ±z₀ = ±i/√2.

## Reproduce

```
python3 -I hepner355_check.py > hepner355_check.log
python3 -I hill_table_check.py > hill_table_check.log
```
