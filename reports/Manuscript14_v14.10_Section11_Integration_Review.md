# Manuscript 14.10 — Section 11 integration and Lean 4 / Arb review

**Reviewed:** 4 November 2026, using the author-supplied `Manuscript_14_v14.10_Research_Section11(1).zip`.  
**Scope:** the author's new 14.10 manuscript, not a rewrite of v14.9.  
**Repository branch:** `manuscript14-section11-parry-cert-20261103` (draft PR #30).  
**Policy:** no merges; no modifications to manuscripts 11–13, V007, V097, or the 14.10 TeX/PDF.

## 1. Scientific scope of version 14.10

Section 11 has been reduced to **one research theorem**, `thm:parry-eulerian`, plus a bibliographic remark. The theorem claims, for `x_E=√2 sinh(1/√2)` and `β_n` the unique root in `(1,2)` of `X^n-X^(n-1)-1`:

- The specialized strict bracketing `β_32 < x_E < β_31`.
- Greedy expansions `d_{β_31}(1)=1 0^29 1` and `d_{x_E}(1)=1 0^30 1 ...`.
- Transcendence of `x_E` and consequent non-eventual periodicity of `d_{x_E}(1)`.
- The exact critical-orbit defect bounds `313240/10^9 < 1-x_E^30(x_E-1) < 313241/10^9`.
- The threshold discontinuity `T_{β_31}^31(1)=0`, with left limit `1`.

The family, standard Parry density, generic transfer operators, and generic Fourier-invariance identities are **background**, not separately numbered novelty claims in 14.10. **Do not keep 'certify the Parry invariant density' on the priority list for this manuscript unless a different, independent project specifically requires it.**

The term *successive* refers only to adjacent indices in the **specified trinomial family**, not to globally consecutive Parry numbers.

## 2. Verified certification baseline; no unearned upgrade

| CI run | Workstream | Lean kernel-audited declarations | Exact/Arb checks | Both jobs |
| --- | --- | ---: | ---: | --- |
| [#41723312459](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723312459) | Special-point analytic/formal material | 25 | 37 | SUCCESS |
| [#41727177204](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41727177204) | Section 11 threshold auxiliary results | 9 | 16 | SUCCESS |
| **Total** | Distinct modules / checks | **34** | **53** | Verified |

The 14.10 editorial revision adds **no new Lean theorem**. Therefore 34/53 remains the verified count until fresh successful runs prove new statements. It is **not** a count of main results of the printed manuscript proved in full.

The nine Section 11 Lean declarations prove polynomial sign comparisons, rational defect inequalities, conditional interval transfers, the two-digit algebraic identity, and conditional first-digit inequalities. **The formal Lean input remains a generic real number satisfying rational bounds**, not the actual function value `x_E=√2 sinh(1/√2)`. The floor recursion and transcendence remain separate.

The provided Python script `SECTION11_EXACT_CERTIFICATE.py` was executed unchanged in the review environment: all **four exact rational check groups** passed. Its output is an additional locally reproduced check, not four new CI-registered Arb tests.

## 3. Revised dependency order for theorem 11.1

1. **Analytic bridge**: within Lean, identify the Fourier/sine-hyperbolic value `x_E` with its convergent positive power series, then derive the exact rational enclosure used in the Parry comparison. Only after this bridge may the existing conditional Lean inequalities be instantiated at the actual `x_E`.
2. **Actual digit recursion**: define `T_β(t)=βt-floor(βt)` with the stated input-1 convention; certify the `β_31` terminating word, the `x_E` prefix, and the critical orbit boundary jump.
3. **Transcendence / nonperiodicity**: connect Lindemann's theorem to the exact `x_E` definition and prove that an eventually periodic greedy expansion of `1` forces algebraicity of its base, with a nonzero polynomial explicitly obtained.
4. **The prior sections remain independent**: continue the analytic ODE, domain-level operator, Fredholm/resolvent and modular exactness tasks only in the appropriate separate workstream. Do not re-formalize generic Parry invariant density or general transfer-operator theory as if it were new Section 11 content.

The complete printed theorem 11.1 is still **PARTIALLY CERTIFIED**, and no complete end-to-end Lean proof has been reported.

## 4. Bibliographic correction needed in the 14.10 source

The bibliography entry `harehichri2026` currently says **“The Parry order of Perron numbers”**. The linked publication [arXiv:2603.19554](https://arxiv.org/abs/2603.19554) is actually titled **“Parry order of Parry numbers”**, by Kevin G. Hare and Hachem Hichri (20 March 2026). Correct the title before final manuscript release. The Cornean–Herbst–Sørensen entry (arXiv:2610.27844, October 2026) matches the linked article's title.

The originality of the *particular Eulerian specialization* remains a qualified research claim; exact priority against all earlier literature is not established. No correction to the author's TeX/PDF is made by this audit.

## 5. Editorial integrity

The provided `REVISION_NOTE.txt` reports a 32-page successful LaTeX compilation and notes that the 14.9 source and the repository's earlier certifications were not changed. This audit independently examined the source text and exact checker, not an independently rerun LaTeX build of the author's file.


---

## 6. Subsequent final certification (4 November 2026)

**This dated addendum supersedes only the provisional certification status and counts in §2–§3 above; it does not erase the historical audit record.** The earlier “PARTIALLY CERTIFIED” assessment and 34/53 counts describe the state *at the time of that initial review*, not the current state of the branch.

- [CI #41812297467](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41812297467): **SUCCESS** for the unconditional Hermite–Lindemann special case, proven in `HermiteEulerianSpecial.lean` using the adapted and kernel-compiled Mathlib PR #28013 modules.
- [CI #41812736721](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41812736721): **SUCCESS** for both the Lean and Arb jobs. Its Lean job log records `eulerian_parry_section11_unconditional` with exactly `propext`, `Classical.choice` and `Quot.sound`; its numerical job reports **ALL 26 SECTION 11 ARB/RATIONAL CHECKS PASSED**.
- [CERTIFICATION_LEDGER_v8.md](../lean/SpecialImaginaryPoint/CERTIFICATION_LEDGER_v8.md) records **74 dedicated audited Lean declarations** and **63 distinct exact/Arb checks** in the project. These are not counts of distinct original results in the published mathematical manuscript.
- The integrated theorem covers the Eulerian strict bracket between the indexed trinomial roots `β₃₂` and `β₃₁`, the actual greedy prefix and defect bound, the threshold orbit jump, transcendence and non-eventual periodicity. Root existence **and uniqueness** are established in the supporting `ParryThresholds.lean` lemmas; the integrated statement invokes the bracket and jump results.
- The third-party Lindemann–Weierstrass code is attributed to Yuyang Zhao and retains its original Apache-2.0 licensing; see [UPSTREAM_LINDEMANN_ATTRIBUTION.md](../lean/SpecialImaginaryPoint/UPSTREAM_LINDEMANN_ATTRIBUTION.md). The Mathlib pin remains unchanged.

**Conclusion:** The printed mathematical content of the unique Theorem 11.1 is **FULLY CERTIFIED in the repository**, subject to the exact meaning and conventions formalized by the imported definitions and lemmas. The repository evidence does not itself certify the bibliographic novelty of the Eulerian specialisation or constitute an independent LaTeX/PDF reproduction check. The author’s manuscript files remain unchanged, as do V007, V097 and manuscripts 11–13; PR #30 must remain **DRAFT, without merge**.

**Editorial follow-up, not a mathematical proof gap:** the Hare–Hichri reference-title correction noted in §4 still requires a separate source edit if it has not been made in a later manuscript version. Do not represent this historical review as an up-to-date inspection of a newer manuscript ZIP.
