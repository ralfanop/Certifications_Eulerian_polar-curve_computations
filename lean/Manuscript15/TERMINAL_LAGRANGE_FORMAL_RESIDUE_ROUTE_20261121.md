# M15 §6.2 — independent formal-residue route to Lagrange–Bürmann (21 November 2026)

Status: mathematical proof plan, **not a Lean certification**. No numerical Arb claims. This file does not modify the frozen manuscript. It is independent of the `Composition.single` lemma in PR #491 (which has subsequently passed exact-HEAD CI).

## Algebraic setting and hypotheses

Let K be a commutative Q-algebra, F(u)=u A(u) in K[[u]], with A(0) a unit, and H(w) the unique compositional inverse of F. Let G(u) in K[[u]]. All negative powers below are formed in K((u)), where F(u) is invertible. Define Res_u as the coefficient of u^(-1).

For every n>=1,

    [w^n] G(H(w)) = (1/n) [u^(n-1)] G'(u) (u/F(u))^n.

The factor 1/n requires characteristic zero (or n invertible); this is why the Q-algebra hypothesis is explicit.

## Three independent algebraic lemmas

1. **Derivative residue**: Res_u (D Q(u)) = 0 for every Laurent series Q(u). Proof: the u^(-1) coefficient of D Q is 0 times the u^0 coefficient of Q. This does not require convergence.

2. **Formal substitution of residues**: for B(w) in K((w)) and F(u)=u A(u), A(0) invertible,

    Res_w B(w) = Res_u B(F(u)) F'(u).

First prove for monomials B(w)=w^k. For k != -1, F^k F' = D(F^(k+1))/(k+1), so the residue vanishes by (1). For k=-1, F'/F = 1/u + A'/A and has residue 1. Extend to Laurent series coefficientwise: at each fixed coefficient, only finitely many terms contribute, since ord(F)=1. A proof avoiding division by k+1 for arbitrary rings can instead use the formal logarithmic derivative and integer coefficient comparison; over a Q-algebra the displayed proof suffices.

3. **Integration by parts**: since Res D(G F^(-n))=0,

    Res G F' F^(-n-1) = (1/n) Res G' F^(-n).

This is the product rule applied to D(G F^(-n)) = G' F^(-n) - n G F' F^(-n-1).

## Main proof

    [w^n] G(H(w))
      = Res_w G(H(w)) w^(-n-1)
      = Res_u G(u) F'(u) F(u)^(-n-1)
      = (1/n) Res_u G'(u) F(u)^(-n)
      = (1/n) [u^(n-1)] G'(u) (u/F(u))^n.

The second equality uses the formal substitution lemma and H(F(u))=u. The final equality is multiplication by u^(-n).

## Specialisation to the frozen terminal graph

Set t0=2*pi, F(u)=X(t0+u)-X(t0), G(u)=Y(t0+u), H=F^(-1). The already established local analytic inverse supplies F'(0)=a != 0. The real Taylor series therefore define elements of R[[u]], and their formal compositional inverse is the Taylor series of the analytic inverse by uniqueness. For the actual graph Y(X^(-1)(X(t0)+w)), the coefficient identity above applies to all n>=1.

The n=0 constant term is G(0) and must be handled separately. For a terminal contact claim, the leading nonzero coefficient and determinant/ratio identities require additional identification with the actual derivatives of X and Y, not merely this abstract coefficient theorem.

## Lean implementation checkpoints (not yet proved)

- Inspect the repository's pinned Mathlib v4.35.0-rc3 for LaurentSeries, PowerSeries, formal derivative, coefficient, composition/reversion, and change-of-variable lemmas; do not assume current Mathlib APIs match the pin.
- Establish derivative-residue and integration-by-parts first as standalone Lean theorems with `#print axioms`.
- Establish residue substitution for an order-one series with invertible leading coefficient; audit infinite sums/formal substitution.
- Prove the coefficient theorem, then connect it to the existing `HasFPowerSeriesAt` construction from PR #491.
- Run a dedicated exact-HEAD pinned workflow before marking any declaration certified.

This route is independent of the dependent-index product rewriting that previously blocked `single_term`. No `sorry`, new axioms, numerical shortcuts, or manuscript changes are proposed.
