import Manuscript16.V165ResolventMultiplier

/-!
M16 v16.5 §14.1: sharp scalar graph-norm multiplier.
Authoritative ZIP SHA-256:
4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e

This proves a pointwise least-upper-bound identity on the scalar half-line.
It does NOT construct the Fourier multiplier on L², identify a Sobolev
operator domain, or prove a full resolvent theorem.
-/

namespace Manuscript16.V165GraphScalar

open Manuscript16.V165Resolvent

theorem graph_sq_least_bound (b M : ℝ) (hb : 0 < b)
    (hM : ∀ t : ℝ, 0 ≤ t →
      1 + (1 / (b + t))^2 ≤ M) :
    1 + (1 / b)^2 ≤ M := by
  simpa using hM 0 (le_refl 0)

theorem graph_sq_sharp (b : ℝ) (hb : 0 < b) :
    (∀ t : ℝ, 0 ≤ t →
      1 + (1 / (b + t))^2 ≤ 1 + (1 / b)^2) ∧
    (∀ M : ℝ, (∀ t : ℝ, 0 ≤ t →
      1 + (1 / (b + t))^2 ≤ M) →
      1 + (1 / b)^2 ≤ M) := by
  constructor
  · intro t ht
    exact graph_sq_bound b t hb ht
  · intro M hM
    exact graph_sq_least_bound b M hb hM

#print axioms Manuscript16.V165GraphScalar.graph_sq_least_bound
#print axioms Manuscript16.V165GraphScalar.graph_sq_sharp

end Manuscript16.V165GraphScalar
