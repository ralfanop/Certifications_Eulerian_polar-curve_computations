# Manuscript 15 — All 7000 Eulerian probability profiles: exact mass and Arb samples

Source basis: Manuscript15_Revision_20261111e, Figure 1.
The source plot includes the profiles of Eulerian distributions for every
n=3 through n=7002 inclusive, i.e. exactly 7000 profiles.

The numerical checker independently constructs the **exact integer**
Eulerian numbers E(n,j) for all these n using the standard triangular recurrence:
`E(n,j)=(j+1)E(n-1,j)+(n-j)E(n-1,j-1)`, with E(1,0)=1.

For each n, it verifies with **exact integer comparisons**:
- `sum_{j=0}^{n-1} E(n,j) = n!`;
- every E(n,j)>0;
- left/right endpoints E(n,0)=E(n,n−1)=1;
- reflection E(n,j)=E(n,n−1−j).

For n in `{3,60,670,671,1000,2000,5000,7002}`, it
additionally encloses the **central peak probability**
`E(n, floor((n−1)/2))/n!` by python-flint Arb,
requiring `ctx.prec=10000` and `rel_accuracy_bits()>=8182`.
These enclosures are for **mathematical probabilities**;
the PDF/TikZ figure uses geometric point coordinates formatted to five
decimal places in pt, and those approximated coordinates cannot be
described as certified to 8182 bits.

**Status: VERIFIED on exact source head.** [GitHub Actions #43091335797](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43091335797) completed SUCCESS on commit `2dcca885ccc5d606e57451dba30d1cc4eaa078d0`. All 7000 individual n cases passed exact integer normalization, positivity and reflection tests. All eight Arb peak enclosures passed with **9998 bits of certified relative accuracy** at 10000 working bits. Log artifact uploaded. The source script itself has not changed.
Successful CI would certify eight specific probability enclosures and
the stated finite exact-integer checks, **not a Lean theorem for all n**
or a proof of the maximal distance of the simplified polylines.

This is intentionally separate from the 14 closed-form Arb constants
certified in PR #179. Previous manuscripts and their data are unchanged.
