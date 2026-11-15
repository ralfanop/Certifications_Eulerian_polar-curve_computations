import Mathlib

/-!
Manuscript 16 v16.4, Section 13: the *scalar inequality* used for the
graph-norm estimate. This does not construct the graph-domain inverse,
prove closedness, or certify Fredholmness/det4.
-/

namespace Manuscript16

/-- If the X-norm of an inverse image is at most r times the input norm,
and its L₀-image is bounded by the input norm plus e times its X-norm,
then the sum graph norm has the asserted bound. -/
theorem graph_norm_scalar_bound
    (a b y e r : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r)
    (ha : a ≤ r * y) (hb : b ≤ y + e * a) :
    a + b ≤ (1 + (1 + e) * r) * y := by
  have hfac : 0 ≤ 1 + e := by linarith
  calc
    a + b ≤ a + (y + e * a) := add_le_add_left hb a
    _ = y + (1 + e) * a := by ring
    _ ≤ y + (1 + e) * (r * y) :=
      add_le_add_left (mul_le_mul_of_nonneg_left ha hfac) y
    _ = (1 + (1 + e) * r) * y := by ring

#print axioms Manuscript16.graph_norm_scalar_bound
end Manuscript16
