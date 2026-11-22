/-
Manuscript 15, Section 7.9 -- principal-root formulation of Eq. (262).

With Mathlib's principal power `z ^ (1/2 : ℂ) = exp (log z / 2)` (principal branch,
arg ∈ (-π, π]), for every real θ and u = e^{iθ}:
  √(1 - 4 c_Mand(θ)) = 1 - u,
and for -π < θ ≤ π this equals -iθ B(e^{iθ}), Eq. (262).
The prose of Section 7.9 is also formalised: |1 - √(1 - 4c)| = 1 on the curve, and
the fixed point u/2 equals z y(z) at z = c_Mand(θ), where
y(z) = (1 - √(1 - 4z))/(2z) is the closed form of the Catalan generating function.
-/
import M15Cert.Kernel

open Complex

namespace M15

lemma one_sub_four_cMand (θ : ℝ) : 1 - 4 * cMand θ = (1 - Complex.exp (θ * I)) ^ 2 := by
  unfold cMand; ring

lemma re_one_sub_exp_nonneg (θ : ℝ) : 0 ≤ (1 - Complex.exp (θ * I)).re := by
  rw [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  linarith [Real.cos_le_one θ]

/-- The principal square root of 1 - 4 c_Mand(θ) is 1 - e^{iθ}, for every real θ. -/
theorem sqrt_one_sub_four_cMand (θ : ℝ) :
    (1 - 4 * cMand θ) ^ (1 / 2 : ℂ) = 1 - Complex.exp (θ * I) := by
  rw [one_sub_four_cMand]
  set w := 1 - Complex.exp (θ * I) with hw
  by_cases h0 : w = 0
  · rw [h0]; simp [Complex.zero_cpow]
  · have hre : 0 < w.re := by
      rcases (re_one_sub_exp_nonneg θ).lt_or_eq with h | h
      · exact h
      · exfalso
        have hc : Real.cos θ = 1 := by
          have : (1 - Complex.exp (θ * I)).re = 1 - Real.cos θ := by
            rw [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
          rw [← hw] at this; linarith
        have hs : Real.sin θ = 0 := by
          have := Real.sin_sq_add_cos_sq θ
          rw [hc] at this; nlinarith [sq_nonneg (Real.sin θ)]
        apply h0
        rw [hw, Complex.exp_mul_I]
        rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]; simp
    have harg : |w.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    have h1 : -(Real.pi / ((2 : ℕ) : ℝ)) < w.arg := by
      push_cast; linarith [(abs_lt.1 harg).1]
    have h2 : w.arg ≤ Real.pi / ((2 : ℕ) : ℝ) := by
      push_cast; linarith [(abs_lt.1 harg).2]
    have := Complex.pow_cpow_nat_inv (x := w) (n := 2) two_ne_zero h1 h2
    simpa [one_div] using this

/-- Eq. (262): for -π < θ ≤ π, √(1 - 4 c_Mand(θ)) = -iθ B(e^{iθ}) (principal root). -/
theorem cardioid_catalan_root (θ : ℝ) (h1 : -Real.pi < θ) (h2 : θ ≤ Real.pi) :
    (1 - 4 * cMand θ) ^ (1 / 2 : ℂ) = -I * θ * eulerianB (Complex.exp (θ * I)) := by
  rw [sqrt_one_sub_four_cMand]
  unfold eulerianB
  by_cases hθ : θ = 0
  · subst hθ; simp
  · have hu : Complex.exp (θ * I) ≠ 1 := by
      intro h
      rcases Complex.exp_eq_one_iff.1 h with ⟨n, hn⟩
      have him := congrArg Complex.im hn
      simp at him
      -- θ = 2πn with |θ| ≤ π and θ ≠ 0: impossible
      have hpi := Real.pi_pos
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 hn0
        nlinarith
      · subst hn0; simp at him; exact hθ him
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
        nlinarith
    have hlog : Complex.log (Complex.exp (θ * I)) = θ * I := by
      apply Complex.log_exp <;> simp [h1, h2]
    simp only [hu, ↓reduceIte, hlog]
    have hθ' : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
    field_simp
    ring_nf

/-- On the cardioid, |1 - √(1 - 4c)| = 1: the boundary of the region of
Flajolet–Sedgewick, p. 536, Fig. VII.23. -/
theorem norm_one_sub_sqrt_cMand (θ : ℝ) :
    ‖1 - (1 - 4 * cMand θ) ^ (1 / 2 : ℂ)‖ = 1 := by
  rw [sqrt_one_sub_four_cMand]
  simp [Complex.norm_exp_ofReal_mul_I]

/-- The closed form of the Catalan generating function, with the principal root. -/
noncomputable def catalanY (z : ℂ) : ℂ := (1 - (1 - 4 * z) ^ (1 / 2 : ℂ)) / (2 * z)

lemma cMand_ne_zero (θ : ℝ) : cMand θ ≠ 0 := by
  intro h
  have hu : ‖Complex.exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hfac : cMand θ = Complex.exp (θ * I) * (2 - Complex.exp (θ * I)) / 4 := by
    unfold cMand; ring
  rw [hfac] at h
  have h' : Complex.exp (θ * I) * (2 - Complex.exp (θ * I)) = 0 := by
    have := h; field_simp at this; linear_combination this
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact Complex.exp_ne_zero _ h1
  · have : Complex.exp (θ * I) = 2 := by linear_combination -h1
    rw [this] at hu; norm_num at hu

/-- The fixed point u/2 of w ↦ w² + c_Mand(θ) equals z y(z) at z = c_Mand(θ). -/
theorem fixed_point_eq_catalan (θ : ℝ) :
    cMand θ * catalanY (cMand θ) = Complex.exp (θ * I) / 2 := by
  unfold catalanY
  rw [sqrt_one_sub_four_cMand]
  have h := cMand_ne_zero θ
  field_simp
  ring

/-- ... and it is indeed a fixed point, with multiplier u. -/
theorem fixed_point_cMand (θ : ℝ) :
    (Complex.exp (θ * I) / 2) ^ 2 + cMand θ = Complex.exp (θ * I) / 2 ∧
      2 * (Complex.exp (θ * I) / 2) = Complex.exp (θ * I) := by
  constructor
  · unfold cMand; ring
  · ring

end M15
