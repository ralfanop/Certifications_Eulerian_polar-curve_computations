# M12 — Appendix A semantic Lean reconciliation (2026-11-20)

Scope: frozen authoritative `Manoscritto_12_20261118(1).zip`, SHA-256
`7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860`,
member `Manoscritto_12/12.tex`, lines 2485–2548. Neither manuscript nor existing proofs are modified. Equation numbers, labels and PDF pages follow the authoritative #417 index, NOT historical equation numbers embedded in Lean comments.

Evidence: [#438](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/438), source head
`595120564632dee861ded1083013569dccc1f90d`,
[exact-head audit run 44495702589 / job 135462195243](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44495702589/job/135462195243),
artifact 14516780117. The actual log reports `M12_BRIDGE_COUNT 821 BAD 0`.
For each of the 25 named public declarations below, the log contains its declaration type and standard-only transitive axioms (propext, Classical.choice, Quot.sound). Source types were checked in the three modules at that exact commit:
- `lean/EulerianGrothendieck/Bridge/AppendixA.lean`
- `lean/EulerianGrothendieck/Bridge/AppendixAGd.lean`
- `lean/EulerianGrothendieck/Bridge/AppendixAMoments.lean`

All names in the table are under `EulerianBridge.AppendixA`. "Direct" means the displayed equation or full chain is present in its type, modulo usual notation; "definition + theorem" and "corollary" explicitly distinguish the required interpretation. This is a source/type reconciliation of existing checked proofs, not a new build or a claim that every surrounding prose assertion is formalized.

| Current eq. | Source label | Mathematical target | Lean declaration(s) | Match and domain |
|---|---|---|---|---|
| 279 | eq:A058962-ogf | OGF (1+4x)/(1−4x)^2 | `a_ogf` | Direct HasSum for real x with abs(x)<1/4; no complex-domain extension claimed. |
| 280 | eq:A058962-egf | EGF exp(4x)(1+8x) | `a_egf` | Direct HasSum for all real x. |
| 281 | eq:A058962-rec | a(k)=8a(k−1)−16a(k−2), k≥2 | `a_rec` | Equivalent additive natural-number identity a(k+2)+16a(k)=8a(k+1); reindex and subtract. |
| 282 | eq:moments-log3 | sum of moments = 2 arctanh(1/2) = 2 arccoth(2) = log 3 | `moments_sum`, `integral_inv_one_sub_sq` | Direct chain (HasSum + two equalities), and alternative integral evaluation. |
| 283 | eq:gudermannian | gd(ψ)=integral sech from 0 to ψ, increasing, range (−π/2,π/2) | definition `gd`; `gd_eq`, `gd_strictMono`, `abs_gd_lt`, `range_gd` | Definition and checked theorems for real ψ. |
| 284 | eq:lambertian | inverse gd = integral sec = log tan(π/4+φ/2) = arctanh(sin φ) | definition `gdInv`; `gdInv_gd`, `gd_gdInv`, `gdInv_eq_arctanh_sin`, `gdInv_eq_log_tan` | Definition and checked identities, inverse range hypothesis abs(φ)<π/2 where applicable. |
| 285 | eq:lambertian-45 | gdInv(π/4)=arctanh(1/sqrt 2)=log(1+sqrt 2) | `gdInv_pi_div_four` | Direct conjunction of both equalities. |
| 286 | eq:lambertian-345 | gdInv(arctan(4/3))=arctanh(4/5)=2 arctanh(1/2)=log 3 | `gdInv_arctan_four_thirds` | Direct conjunction, also includes sin(arctan(4/3))=4/5. |
| 287 | eq:moments-semifactorial | m(k)=(2k−1)!!/[4^k(2k+1)!!] | `m_semifactorial` | Direct for natural k, with oddDF(k) and oddDF(k+1); k=0 included via natural double-factorial convention. |
| 288 | eq:central-binomial-semifactorial | binom(2k,k)=2^k(2k−1)!!/k! | `central_binom_semifactorial` | Equivalent cross-multiplied natural identity, k! nonzero; centralBinom is the central binomial coefficient. |
| 289 | eq:catalan-semifactorial | C(k)=binom(2k,k)/(k+1)=2^k(2k−1)!!/(k+1)! | `catalan_semifactorial`, `central_binom_semifactorial` | Cross-multiplied natural identities; factorial nonzero and (k+1)!=(k+1)k! give both division forms. |
| 290 | eq:moments-uniform | (1/4) ∫[-2,2] x^(2k) dx = 4^k/(2k+1)=16^k m(k) | `uniform_moments` | Direct conjunction, k natural. |
| 291 | eq:moments-arcsine | (1/π) ∫[-2,2] x^(2k)/sqrt(4−x²) dx = binom(2k,k) | `arcsine_moment` | Direct real interval-integral identity, k natural. |
| 292 | eq:moments-semicircle | (1/(2π)) ∫[-2,2] x^(2k)sqrt(4−x²) dx = C(k) | `semicircle_moment` | Direct real interval-integral identity, k natural. |
| 293 | eq:moments-gaussian | standard Gaussian even moment = (2k−1)!! | `gaussian_moment` | Direct integral over real line with density exp(−x²/2)/sqrt(2π), k natural. |

Unnumbered assertions: `m_eq` and `m_inv` directly establish the uniform moment and reciprocal sequence; `a_eq_hypercube_edges` verifies the numerical formula (2k+1)·2^(2k) but does not itself prove the combinatorial hypercube edge-count interpretation. The separate cited identity log(1+sqrt 2)=sqrt 2 L_8(1) (prose after eq. 286, Finch 2019 p.98) is not established by `gdInv_pi_div_four`, nor by the inspected Appendix A declarations. Do not infer a formal proof of the Dirichlet L-value from a scalar Arb enclosure or the Lambertian identity. Treat it as a separate reconciliation obligation: locate an exact existing theorem for the primitive real character modulo 8 and its normalization, or prove the series evaluation; retain the external-citation status until verified. Similarly, the combinatorial interpretations and general arctanh generating function in prose are not closed by the numbered equation mapping alone.

Result: 15/15 numbered Appendix A displays have direct, definitional, or algebraic-corollary reconciliations to audited Lean declarations, with the stated real-domain and natural-number conventions; **not** 15 newly compiled theorems. The remaining 278 numbered displays and unnumbered proof obligations need their own semantic mapping unless independently reconciled. No numerical precision claim is changed.

Related evidence: merged #462, audited source head `e936c63c3ed571d34f2448dffe6ccef3fbbf0879`, run 44519258395: 918 EulerianGrothendieck, 162 UniformLanczos, 705 V033 FixedDegreeLanczos public theorem declarations, each namespace BAD 0. These counts alone do not establish semantic coverage of the manuscript. Keep the separate Table 1 quadrature gate open at 3,600,000 working bits and exact fixed/significant decimal rounding.
