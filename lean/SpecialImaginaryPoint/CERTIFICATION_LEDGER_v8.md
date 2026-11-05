# Manuscript 14.10 — Lean 4 / Arb certification register v8

**Audit date:** 4 November 2026  
**Research object:** the unique printed Theorem 11.1 in Manuscript 14.10.  
**Branch:** `manuscript14-section11-parry-cert-20261103`; [PR #30](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/30) remains DRAFT. No merge into V007, V097, PR #16, main, or manuscripts 11–13.

## Decisive new certificate: the missing Hermite–Lindemann instance

[CI #41812297467](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41812297467) is **SUCCESS**. It compiled the complete Lindemann–Weierstrass proof infrastructure, the existing special-point/Fourier–Parry modules, and the integrated Eulerian theorem in the **same Lean kernel**, using:

- Lean `v4.35.0-rc3`;
- the **unchanged** Mathlib pin `0272bbe1c093d038d7257ab15306abd58245f9ff`;
- the local upstream compatibility files `SpecialImaginaryPoint/UpstreamLindemannAlgebraicPart.lean` and `SpecialImaginaryPoint/UpstreamLindemannBasic.lean`;
- `SpecialImaginaryPoint/HermiteEulerianSpecial.lean` for three new genuine, unconditional theorems.

The files are adapted from **Yuyang Zhao's** pre-merge Mathlib Lindemann–Weierstrass formalization in [Mathlib PR #28013](https://github.com/leanprover-community/mathlib4/pull/28013), specifically commit `5a0057ccc26b` (18 September 2026, Lean 4.35 rc2), with the necessary `HasUniqueDiv` API adjustment for pinned rc3 and changed local import path. Original authorship and **Apache 2.0** header are retained. This is an *upstream proof used under license*, not a new mathematical proof of Lindemann–Weierstrass and not an independent discovery.

The audit for all three new declarations lists **only** `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx` and no `Lean.ofReduceBool`. The local-upstream dependency modules are actual Lean source compiled in the workflow, not assumed axioms or binary blobs.

### New statements accepted by the kernel

1. `eulerian_complex_exponent_algebraic_integer` — `IsAlgebraic ℤ ((1/sqrt(2):ℝ):ℂ)`, via the fraction-ring equivalence and the proved algebraicity over Q.
2. `eulerian_exponential_transcendental` — `¬ IsAlgebraic ℚ (Real.exp (1/Real.sqrt 2))`, using the kernel-compiled upstream `transcendental_exp`.
3. `eulerian_parry_section11_unconditional` — a single unconditional theorem combining all main Eulerian-Parry dynamical and numerical conclusions with `¬IsAlgebraic ℚ x_E` and absence of eventual digit periodicity, where `x_E = sqrt(2) sinh(1/sqrt(2))`.

The endpoint digit block for `β₃₁` is a separately certified theorem in `ParryThresholds.lean`; the integrated theorem invokes the already audited root and jump lemmas.

## Certified workstreams and counts

| Kernel-checked component | Last successful CI | Dedicated audited Lean declarations |
| --- | --- | ---: |
| Earlier special-point analytical / formal results | [#41723312459](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723312459) | 25 |
| Section 11 rational thresholds, greedy floor dynamics, roots, analytic enclosure, endpoint jump | [#41806320179](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41806320179) | 28 |
| Algebraic affine-orbit polynomial and eventual rational-digit periodicity lemmas | [#41808330602](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41808330602) | 7 |
| Actual greedy floor recursion, rationality from eventually periodic digits | [#41808771417](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41808771417) | 4 |
| Hyperbolic-to-exponential transcendence reduction | [#41809032863](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809032863) | 3 |
| Real sinh series plus explicit conditional Hermite bridge | [#41809760282](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809760282) | 4 |
| **Unconditional Hermite–Lindemann instance and integrated theorem** | [#41812297467](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41812297467) | **3** |
| **Total** | | **74** |

These 74 are declarations in the project modules, **not** 74 original research theorems, and do not count upstream helper declarations independently.

**Numerical certification:** 37 prior exact/Arb checks + 26 Section 11 checks = **63 distinct PASS**, with all ten v14.10 seven-term Taylor bounds included. See Arb success in [#41809439359](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809439359) and [#41809760282](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809760282). CI failure of #41809439359 was from an independent redundant Lean tactic; Arb itself succeeded and a later Lean run is SUCCESS.

**Final joint verification:** [CI #41812736721](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41812736721) is **SUCCESS for Lean and Arb**. The same Lean kernel compiled and axiom-audited the unconditional theorem and all local dependencies. The Arb job reports **ALL 26 SECTION 11 ARB/RATIONAL CHECKS PASSED**. No Lean errors, `sorryAx` or `Lean.ofReduceBool` appeared in the successful theorem audits.

## Precise scope and remaining maintenance

- Theorem 11.1's **stated mathematical content is now fully certified in Lean**, with the *only previously missing deep theorem* supplied as kernel-compiled, attributed open-source code rather than as an axiom.
- The mathematical novelty of Section 11 continues to concern the specific Eulerian-Parry specialization, not the classical Lindemann–Weierstrass theorem or generic Parry maps.
- **Maintenance note:** Mathlib [PR #28013](https://github.com/leanprover-community/mathlib4/pull/28013) is not merged as of this audit. When it is merged, the local compatibility copies should be retired in favor of its official module with a deliberately reviewed Mathlib/toolchain upgrade; do not silently change the project's current pin.
- No modification was made to the author's manuscript 14.10 TeX/PDF, nor to manuscripts 11–13, V007, V097, PR #16, or main.

