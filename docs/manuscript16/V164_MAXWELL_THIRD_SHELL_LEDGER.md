# M16 v16.4 — necessary side of the nonresonant Maxwell Schatten threshold

Authoritative source: `Manoscritto_16_4_Editorial_Abstract200_Sezioni14-16_20261114(1).zip`, SHA-256 `c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f`, `16.tex` Proposition `prop:mixed-schatten-164`, equations `eq:mixed-maxwell-index-164` and `eq:mixed-lower-series-164`.

This branch adds a **new** scalar estimate for the Maxwell nonresonant temporal mode `m=ell+2`, distinct from the previously certified *Dirac* third-shell bound in PR #305.

For integer `ell>=2`, `ell^2-(ell+2)^2=-4(ell+1)`. With the transverse multiplicity `2(ell^2-1)`, the `p=3` nearest-mode term satisfies

```text
2*(ell^2-1) / (4*(ell+1))^3
  = (ell-1)/(32*(ell+1)^2)
 >= 1/(96*(ell+1)).
```

The last inequality is equivalent to `ell+1 <= 3*(ell-1)`, which follows from `ell>=2`. The shifted harmonic series diverges, hence this proves the **necessary-side scalar comparison** for `p=3`, conditional on the spectral multiplicity and eigenvalue identification in the manuscript. Divergence itself, the full `p<=3` reduction, the upper `p>3` estimate, and the operator Schatten iff remain **analytic formalization obligations**.

Lean: two scalar lemmas; `#print axioms` audit; no `sorryAx` or `Lean.ofReduceBool` permitted. Arb: not applicable to these exact rational identities; do not fabricate a 10000-bit precision claim. Previous v16.4 scalar enclosures are already certified in PR #306 and are not duplicated.

No edits to any manuscript source or Manoscritti 11–15. No merge.
