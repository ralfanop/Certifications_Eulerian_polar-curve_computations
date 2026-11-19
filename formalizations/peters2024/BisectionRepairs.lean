import Peters2024

/-! Sufficient hypotheses for a genuine vector-valued bisection (§6.5).
These are corrected statements, not proofs of the unrestricted printed claim. -/

namespace Peters2024
open Set

/-- A continuous real scalar cumulative integral in a fixed vector direction
can be bisected, including when the direction is zero. In particular the
codomain may be ℂ, considered as a real vector space. -/
theorem line_bisection {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : ℝ → E) (g : ℝ → ℝ) (v : E)
    (hg : Continuous g) (hg0 : g 0 = 0)
    (hline : ∀ t, F t = g t • v) :
    ∃ t ∈ Icc (0 : ℝ) 1, F t = F 1 - F t := by
  obtain ⟨t, ht, he⟩ := real_bisection g hg hg0
  refine ⟨t, ht, ?_⟩
  rw [hline t, hline 1, ← sub_smul, ← he]

/-- A reflection symmetry of cumulative increments forces the midpoint to
bisect an arbitrary additive-group-valued cumulative integral. -/
theorem reflection_bisection {E : Type*} [AddGroup E]
    (F : ℝ → E)
    (hsym : ∀ t ∈ Icc (0 : ℝ) 1, F (1 - t) = F 1 - F t) :
    F (1/2) = F 1 - F (1/2) := by
  have h := hsym (1/2) (by constructor <;> norm_num)
  convert h using 2
  norm_num

/-- A continuous scalar parametrization of an affine line is enough; the
initial value need not be zero until the cumulative function is normalized. -/
theorem affine_line_bisection {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : ℝ → E) (g : ℝ → ℝ) (v w : E)
    (hg : Continuous g) (hg0 : g 0 = 0)
    (hline : ∀ t, F t = w + g t • v) :
    ∃ t ∈ Icc (0 : ℝ) 1, F t - F 0 = F 1 - F t := by
  obtain ⟨t, ht, he⟩ := real_bisection g hg hg0
  refine ⟨t, ht, ?_⟩
  rw [hline t, hline 0, hline 1, hg0, zero_smul, add_zero,
    add_sub_cancel_left, add_sub_add_left_eq_sub, ← sub_smul, ← he]

end Peters2024

#print axioms Peters2024.line_bisection
#print axioms Peters2024.reflection_bisection
#print axioms Peters2024.affine_line_bisection
