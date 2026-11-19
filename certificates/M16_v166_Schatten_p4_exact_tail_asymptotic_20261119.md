# M16.6 §13 — exact scalar tail representation and asymptotic coefficient (2026-11-19)

**Scope and provenance.** Derived from the scalar model in `certificates/M16_v166_Schatten_p4_scalar_closed_form_20261119.md` at PR #411 HEAD `f88863ff600070b3f3c3c0a481ae74ab85d1249d`. This is an analytic note, not Lean/Arb certification and not an operator result. Frozen manuscripts unchanged.

Let `A(L)=sum_{k in Z\{0,-L}} [4|k||k+L|]^{-4}`, `L>=2`, and `T_4(N)=sum_{L>N} 2(L^2-1) A(L)`, `N>=2`. Let `H_s(N)=sum_{L=N+1}^infinity L^{-s}=zeta(s,N+1)` for `s>1`.

The already-proved partial-fraction formula for `A(L)` implies the **exact convergent tail identity**
```
T_4(N) = (zeta(4)/32) [H_2(N)-H_4(N)]
       + (5 zeta(2)/16) [H_4(N)-H_6(N)]
       - (35/64) [H_6(N)-H_8(N)].
```
All terms are absolutely summable; this is a scalar identity. The signed last term means interval evaluation must retain directed enclosures and account for cancellation.

For `s>1`, the integral test yields
```
 (N+1)^(1-s)/(s-1) <= H_s(N) <= N^(1-s)/(s-1).
```
Thus `N H_2(N) -> 1` and `N H_s(N) -> 0` for `s>=4`, proving the **exact leading coefficient**
```
 lim_{N->infinity} N T_4(N) = zeta(4)/32 = pi^4/2880.
```
This strengthens the prior Theta(1/N) statement by determining the coefficient; it is not a new numerical certificate.

**Certification pathway:** (1) reconcile the frozen §13 index set and multiplicity with this scalar model; (2) formalize the partial fractions, absolute convergence, integral comparison, and limit in Lean 4; (3) check `#print axioms` and CI on exact HEAD; (4) use FLINT/Arb `ctx.prec=3600000`, assert each nonzero result has `rel_accuracy_bits()>=3400000`, and prove strict single-cell rounding at 1,000,001 significant decimal digits using exact endpoints. Neither this note nor a finite benchmark satisfies (3)–(4).

**Open operator obligations:** identify Maxwell–Dirac singular values with the scalar spectral model, graph-domain conditions, Schatten membership and the general regularized Fredholm determinant det4.
