# Manuscript 14.1, Section 7 — finite spectral certificate

4 November 2026. Isolated research branch: `manuscript14-dirichlet-finite-20261104`.
This work does **not** merge with `main`, V007, V097 or the independent Parry Section 11 branch.

## Certifiable claims

For the auxiliary Dirichlet eigenvalues `lambda_n = pi^2 * n^2`, `n >= 1`, and shift `t >= 0`:

- The finite diagonal matrix with entries `1 + t/lambda_n` has determinant equal to the product of those factors.
- The finite product `D_N(t) = product(n=1..N) (1+t/lambda_n)` is positive, starts from one at `t=0`, and is nondecreasing in `N`.
- The finite resolvent trace is `T_N(t) = sum(n=1..N) 1/(lambda_n+t)`, and equals the diagonal matrix trace.
- The finite square-resolvent sum is `Q_N(t) = sum(n=1..N) 1/(lambda_n+t)^2`.

Files:
- [DirichletFiniteDeterminant.lean](../lean/SpecialImaginaryPoint/DirichletFiniteDeterminant.lean)
- [DirichletFiniteTrace.lean](../lean/SpecialImaginaryPoint/DirichletFiniteTrace.lean)
- [Arb and exact rational checks](../numerics/arb/manuscript14_dirichlet_finite_arb.py)
- [isolated CI](../.github/workflows/manuscript14-dirichlet-finite.yml)

## Verified checkpoints

Initial finite-determinant Lean+Arb certificate at `3f8046c5c3b09ddd889b9a4325ec72a797877bdf`:
[CI 41824926567](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41824926567) **SUCCESS for Lean and Arb**.
Seven explicitly audited Lean declarations; `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`; nine exact rational/Arb tests passed.

Extended trace modules and script at `1948522cb4b43dd36731f52d8656ededc4585c0f`:
[CI 41825497267](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41825497267).
**SUCCESS for Lean and Arb**, verified from the completed workflow jobs and Lean log.
Fourteen project Lean declarations (seven determinant and seven trace) were explicitly audited by `#print axioms` and list only `propext`, `Classical.choice`, and `Quot.sound` without `sorryAx` or `Lean.ofReduceBool`.
All **13/13 Arb/exact rational checks PASS**, at 256 bits with pinned python-flint 0.9.0.

At both `t=1/8` and `t=1/2`, numerical ball checks compare the first 500 factors and resolvent terms with their hyperbolic closed forms. The tail estimates used in the analytical comparison are:
```
0 < D_inf/D_N - 1 < exp(t / (pi^2 * N)) - 1,
0 < T_inf - T_N < 1 / (pi^2 * N),
0 < Q_inf - Q_N < 1 / (3 * pi^4 * N^3)
```
for `N >= 1`, `t > 0`, *assuming the classical Euler-product and trace identities*.
The CI checks their specific numerical inclusions, but does not formalize the universal
tail inequalities or prove the input infinite product identity in Lean.

## Outstanding formal obligations

1. Identify the actual unbounded Dirichlet Laplacian and its spectral decomposition, not just finite diagonal matrices.
2. Prove the trace-class and Hilbert–Schmidt summability theorems for its resolvent and the operator-valued finite-rank limit.
3. Prove Euler's `sinh(sqrt(t))/sqrt(t)` infinite product and connect it to the Fredholm determinant of `I+t A^-1`.
4. Establish the zeta-regularized determinant ratio, with correct operator domains, and differentiate the limit with locally uniform convergence to certify the Langevin trace formulas.
5. Audit numerical enclosures and printed precision independently of claims of originality.

This ledger reports verified checkpoints only and makes no claim of an infinite-dimensional determinant certification.
