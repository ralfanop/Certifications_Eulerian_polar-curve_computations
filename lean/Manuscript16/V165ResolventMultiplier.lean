import Mathlib

/-!
Scalar prerequisites for the free evanescent resolvent, M16 v16.5 §14.1.
Source ZIP SHA256 4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e.
Here b = |κ|²-k² > 0 and t = ξ² ≥ 0. These are scalar bounds and
a sharp scalar upper-bound characterization, not a Fourier or operator theorem.
-/
namespace Manuscript16.V165Resolvent

theorem multiplier_bound (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    0 < 1 / (b + t) ∧ 1 / (b + t) ≤ 1 / b := by
  have hd : 0 < b + t := by linarith
  constructor
  · exact div_pos zero_lt_one hd
  · apply (div_le_div_iff₀ hd hb).2
    linarith

theorem bessel_bound (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    (1 + t) / (b + t) ≤ max 1 (1 / b) := by
  have hd : 0 < b + t := by linarith
  by_cases h : b ≤ 1
  · apply le_trans _ (le_max_right 1 (1 / b))
    apply (div_le_div_iff₀ hd hb).2
    nlinarith [mul_nonneg ht (sub_nonneg.mpr h)]
  · apply le_trans _ (le_max_left 1 (1 / b))
    apply (div_le_iff₀ hd).2
    linarith

/-- Every upper bound on the entire scalar half-line is at least the stated max.
The second endpoint is at infinity, not a claim that the supremum is attained. -/
theorem bessel_least_bound (b M : ℝ) (hb : 0 < b)
    (hM : ∀ t : ℝ, 0 ≤ t → (1 + t) / (b + t) ≤ M) :
    max 1 (1 / b) ≤ M := by
  apply max_le
  · by_contra! hn
    have hc : 0 < 1 - M := by linarith
    let t : ℝ := (b + 1) / (1 - M)
    have ht : 0 ≤ t := (div_pos (by linarith) hc).le
    have hd : 0 < b + t := by linarith
    have he : t * (1 - M) = b + 1 := by
      dsimp [t]
      field_simp [hc.ne']
    have hu := (div_le_iff₀ hd).1 (hM t ht)
    have hm := mul_lt_mul_of_pos_right hn hb
    nlinarith
  · simpa using hM 0 (le_refl 0)

/-- Squared canonical Hilbert graph-norm ratio; unlike Bessel norm, this
is 1 + (b+t)⁻² and reaches its scalar maximum at t=0. -/
theorem graph_sq_bound (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    1 + (1 / (b + t))^2 ≤ 1 + (1 / b)^2 := by
  obtain ⟨hp, hle⟩ := multiplier_bound b t hb ht
  have hq : 0 < 1 / b := div_pos zero_lt_one hb
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (add_nonneg hq.le hp.le)]

#print axioms Manuscript16.V165Resolvent.multiplier_bound
#print axioms Manuscript16.V165Resolvent.bessel_bound
#print axioms Manuscript16.V165Resolvent.bessel_least_bound
#print axioms Manuscript16.V165Resolvent.graph_sq_bound
end Manuscript16.V165Resolvent
