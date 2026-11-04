# V007 — Certified real Gegenbauer heat semigroup: closed graph and exact nuclear S1

**Certification date:** 4 November 2026.  
**Repository:** `ralfanop/Certifications_Eulerian_polar-curve_computations`.  
**Pull request:** [#16](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/16), branch `gegenbauer-fock-formalization-20261025` (draft, **DO NOT MERGE**).  
**Proof assistant:** Lean 4, pinned toolchain `leanprover/lean4:v4.35.0-rc3`, repository-pinned Mathlib.

## Final joint certificates — SUCCESS

| Statement | GitHub Actions run | Build | Kernel axiom audit |
| --- | --- | --- | --- |
| `sturmRealHeat_closed_graph_compact_nuclear_joint_certificate` | [#41805185884](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805185884) | SUCCESS; 9,159 jobs | `propext`, `Classical.choice`, `Quot.sound` only |
| `sturmRealHeat_closed_graph_compact_nuclear_exactS1_joint_certificate` | [#41805555379](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805555379) | SUCCESS; 9,168 jobs | `propext`, `Classical.choice`, `Quot.sound` only |

Both completed on 4 November 2026; the jobs explicitly build the corresponding Lean source modules and execute `lake env lean -M16768` with `#print axioms`. Neither certified proof depends on `sorryAx` or `Lean.ofReduceBool`.

- [Final joint Lean source](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleRealHeatGraphNuclearExactS1Certificate.lean)
- [Four-property joint Lean source](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleRealHeatGraphNuclearJointCertificate.lean)

## Exact mathematical scope

Let `lambda > 0`, and let `H = L²(nu_lambda; R)` be the genuine real ultraspherical weighted Hilbert space. Let `A` denote the **canonical closure of the original Gegenbauer Sturm differential operator on polynomials**, not an independently postulated diagonal operator. Let `(e_n)_(n>=0)` denote the certified complete normalized Gegenbauer Hilbert basis.

For every `s > 0`, the certified five-property joint statement asserts:

1. **Strong right continuity in the closed Sturm graph norm:** for each `f in Dom(A)`, the sum `||H_u f-f||_2 + ||H_u Af-Af||_2` tends to zero as `u ↓ 0`. Certified domain invariance/commutation separately identifies the second term as `||A H_u f-Af||_2` for `u >= 0`.
2. **Compactness:** `H_s` is compact on the full genuine real weighted `L²`.
3. **General real nuclear class:** `H_s` has an operator-norm convergent, absolutely summable rank-one representation, meeting the formalized real nuclear-series criterion.
4. **Exact mass of the explicit positive orthogonal expansion:** its sum of rank-one operator norms equals the actual diagonal trace `sum_n <e_n,H_s e_n>`.
5. **Exact universal projective real nuclear S1 norm:** the infimum of nuclear costs over **all** admissible real-Hilbert rank-one decompositions is exactly `sum_n exp(-s n(n+2 lambda))`.

The operator-norm convergent series is

```text
H_s = SUM_{n>=0} exp(-s*n*(n+2*lambda)) * rankOne_R(e_n,e_n).
```

The sharp trace-norm identity is

```text
realNuclearInfimum(H_s)
  = SUM_{n>=0} exp(-s*n*(n+2*lambda)),  lambda>0, s>0.
```

The **universal lower bound** for the nuclear infimum relies on real finite-dimensional trace duality applied to every admissible decomposition; it is not deduced solely from exhibiting one positive decomposition.

## Independently certified dependencies

| Property | Run | Build status |
| --- | --- | --- |
| Strong continuity in graph norm | [#41717375064](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41717375064) | SUCCESS; 9,137 jobs |
| Positive heat nuclear operator series and compactness | [#41804102167](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41804102167) | SUCCESS; 9,131 jobs |
| Positive nuclear mass equals genuine basis trace | [#41804102123](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41804102123) | SUCCESS; 9,132 jobs |
| General real-Hilbert rank-one nuclear class | [#41804101950](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41804101950) | SUCCESS; 9,135 jobs |
| Exact positive-time universal real projective nuclear S1 norm | [#41804412794](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41804412794) | SUCCESS; 9,140 jobs |

The exact-graph generator theorem `sturmRealHeatLimit_generator_graph_set_eq_closedSturm` was independently certified in [#41439924141](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41439924141); this establishes equality of the semigroup generator graph with the actual closed Sturm differential operator graph. **The final five-property theorem does not itself state this generator equality:** it invokes the actual closed operator in its graph-continuity conjunct. Cite both results where both are needed.

## Scope limitations and manuscript wording

- The certified norm is the **real-Hilbert projective rank-one nuclear infimum** `realNuclearInfimum`. This dossier does **not** assert a formal equivalence with a distinct **complex** CFC/Physlib trace-class predicate or norm. Such a bridge needs separate formal hypotheses and certification.
- The full joint certificate is a mathematically useful organization of certified operator-theoretic statements; **formal certification by itself is not a claim of new mathematical priority**.
- Do not claim `H_0` compact or nuclear: the compactness and nuclearity statements are for **strictly positive** time.
- No merge into `main` or V097 is authorized. V007 remains a separate project/manuscript.

## Suggested standalone manuscript proposition

**Proposition (Canonical Gegenbauer heat: closed-graph continuity and exact nuclear trace).** Let `lambda>0`, let `A_lambda` be the closure of the Gegenbauer Sturm differential operator on polynomials in `L²(nu_lambda;R)`, and let `H_s` be its genuine `C_0` heat semigroup. Then the restriction of `H_s` to the closed Sturm domain is strongly continuous at zero in the graph norm. For each `s>0`, `H_s` is a compact real nuclear operator, admits the absolutely operator-norm convergent positive expansion on the normalized Gegenbauer basis, and its optimal real projective nuclear norm equals the sum of its positive eigenvalues `sum_n exp(-s*n*(n+2*lambda))`.

**Proof dependency:** the pinned Lean theorem `sturmRealHeat_closed_graph_compact_nuclear_exactS1_joint_certificate` and its independent kernel-checked dependencies listed above.
