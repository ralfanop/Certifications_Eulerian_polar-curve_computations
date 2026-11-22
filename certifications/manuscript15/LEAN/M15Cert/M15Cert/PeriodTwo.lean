/-
Manuscript 15, Proposition 7.22 -- the disc of period two, Eqs. (276) and (277).

Equation numbers in this module are those of version 39 of the manuscript.
For f_c(w) = w² + c, the second factor w² + w + c + 1 of Eq. (275) has, for every c,
a root w₊; the other root is w₋ = -1 - w₊, and f_c exchanges the two.  For c ≠ -3/4
they are distinct and neither is fixed by f_c, so they form a cycle of exact period two,
with w₊ w₋ = c + 1.  Its multiplier is (f_c ∘ f_c)'(w₊) = 4 w₊ w₋ = 4(c + 1), Eq. (276);
the cycle is attracting exactly when |c + 1| < 1/4, and the multiplier has modulus one
exactly on the circle |c + 1| = 1/4, Eq. (277).  At c = -3/4 = c_Mand(π) the second factor
is (w + 1/2)², and the circle and the cardioid are tangent there.
-/
import M15Cert.Kernel

open Complex

namespace M15

/-- The second factor of Eq. (275) has a root for every complex c. -/
theorem exists_period_two_root (c : ℂ) : ∃ w : ℂ, w ^ 2 + w + c + 1 = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-3 - 4 * c) (by norm_num : 0 < 2)
  exact ⟨(-1 + s) / 2, by linear_combination hs / 4⟩

/-- The roots of the second factor are exchanged by f_c(w) = w² + c: f_c(w) = -1 - w,
-1 - w is again a root, f_c(-1 - w) = w, and the product of the two roots is c + 1. -/
theorem period_two_swap {c w : ℂ} (hw : w ^ 2 + w + c + 1 = 0) :
    w ^ 2 + c = -1 - w ∧ (-1 - w) ^ 2 + (-1 - w) + c + 1 = 0 ∧ (-1 - w) ^ 2 + c = w ∧
      w * (-1 - w) = c + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hw
  · linear_combination hw
  · linear_combination hw
  · linear_combination (-1 : ℂ) * hw

/-- For c ≠ -3/4 the two roots are distinct and neither is a fixed point of f_c. -/
theorem period_two_distinct {c w : ℂ} (hc : c ≠ -3 / 4) (hw : w ^ 2 + w + c + 1 = 0) :
    w ≠ -1 - w ∧ w ^ 2 + c ≠ w := by
  have hne : w ≠ -1 - w := by
    intro h
    have h2 : w = -1 / 2 := by linear_combination h / 2
    apply hc
    rw [h2] at hw
    linear_combination hw
  refine ⟨hne, ?_⟩
  intro h
  apply hne
  linear_combination (-1 : ℂ) * h + hw

/-- For c ≠ -3/4 the second factor of Eq. (275) has two distinct roots w₊ and w₋, exchanged
by f_c and not fixed by it: a cycle of exact period two of f_c, with w₊ w₋ = c + 1. -/
theorem period_two_cycle {c : ℂ} (hc : c ≠ -3 / 4) :
    ∃ wp wm : ℂ, wp ^ 2 + wp + c + 1 = 0 ∧ wm ^ 2 + wm + c + 1 = 0 ∧ wp ≠ wm ∧
      wp ^ 2 + c = wm ∧ wm ^ 2 + c = wp ∧ wp ^ 2 + c ≠ wp ∧ wp * wm = c + 1 := by
  obtain ⟨w, hw⟩ := exists_period_two_root c
  obtain ⟨h1, h2, h3, h4⟩ := period_two_swap hw
  obtain ⟨h5, h6⟩ := period_two_distinct hc hw
  exact ⟨w, -1 - w, hw, h2, h5, h1, h3, h6, h4⟩

/-- Eq. (276): the multiplier of the cycle, (f_c ∘ f_c)'(w₊) = 4 w₊ w₋ = 4(c + 1),
with w₋ = -1 - w₊. -/
theorem period_two_multiplier {c w : ℂ} (hw : w ^ 2 + w + c + 1 = 0) :
    HasDerivAt (fun z : ℂ => (z ^ 2 + c) ^ 2 + c) (4 * (w * (-1 - w))) w ∧
      4 * (w * (-1 - w)) = 4 * (c + 1) := by
  have h1 : ∀ z : ℂ, HasDerivAt (fun x : ℂ => x ^ 2 + c) (2 * z) z := by
    intro z
    have h := (hasDerivAt_pow 2 z).add_const c
    convert h using 1
    norm_num
  have h2 := (h1 (w ^ 2 + c)).comp w (h1 w)
  have h3 : HasDerivAt (fun z : ℂ => (z ^ 2 + c) ^ 2 + c) (2 * (w ^ 2 + c) * (2 * w)) w := h2
  have hfw : w ^ 2 + c = -1 - w := by linear_combination hw
  constructor
  · exact h3.congr_deriv (by rw [hfw]; ring)
  · linear_combination (-4 : ℂ) * hw

/-- Eq. (277): the cycle is attracting, with multiplier of modulus less than one, exactly when
|c + 1| < 1/4, and the multiplier has modulus one exactly on the circle |c + 1| = 1/4. -/
theorem period_two_attracting_iff (c : ℂ) :
    (‖4 * (c + 1)‖ < 1 ↔ ‖c + 1‖ < 1 / 4) ∧ (‖4 * (c + 1)‖ = 1 ↔ ‖c + 1‖ = 1 / 4) := by
  have h4 : ‖4 * (c + 1)‖ = 4 * ‖c + 1‖ := by simp
  rw [h4]
  constructor
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-- At c = -3/4 the second factor of Eq. (275) is (w + 1/2)²: the cycle of period two merges
with the fixed point -1/2 (period-doubling bifurcation). -/
theorem period_two_merge (w : ℂ) : w ^ 2 + w + (-3 / 4 : ℂ) + 1 = (w + 1 / 2) ^ 2 := by ring

/-- The circle |c + 1| = 1/4 of Eq. (277), parametrised by φ ↦ -1 + e^{iφ}/4. -/
noncomputable def circTwo (φ : ℝ) : ℂ := -1 + Complex.exp (φ * I) / 4

lemma hasDerivAt_exp_mul_I (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * I)) (Complex.exp (θ * I) * I) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
  exact h1.cexp

/-- The derivative of the cardioid c_Mand(θ) = u/2 - u²/4, u = e^{iθ}: (i/2) u (1 - u). -/
theorem hasDerivAt_cMand (θ : ℝ) :
    HasDerivAt cMand (I / 2 * Complex.exp (θ * I) * (1 - Complex.exp (θ * I))) θ := by
  have h2 := hasDerivAt_exp_mul_I θ
  have h3 := (h2.div_const 2).sub ((h2.pow 2).div_const 4)
  unfold cMand
  convert h3 using 1
  simp; ring

/-- At θ = π the cardioid reaches c = -3/4, which lies on the circle |c + 1| = 1/4 as its
point φ = 0, and the two curves are tangent there: c_Mand'(π) = -i and the velocity of the
circle at φ = 0 is i/4, a nonzero real multiple of it (both tangents are vertical). -/
theorem cardioid_circle_tangent :
    cMand Real.pi = -3 / 4 ∧ circTwo 0 = -3 / 4 ∧ ‖cMand Real.pi + 1‖ = 1 / 4 ∧
      HasDerivAt cMand (-I) Real.pi ∧ HasDerivAt circTwo (I / 4) 0 ∧
      (-I : ℂ) = ((-4 : ℝ) : ℂ) * (I / 4) := by
  have hpi : cMand Real.pi = -3 / 4 := by
    unfold cMand
    rw [Complex.exp_pi_mul_I]
    norm_num
  refine ⟨hpi, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [circTwo]
  · rw [hpi, show (-3 / 4 : ℂ) + 1 = ((1 / 4 : ℝ) : ℂ) by norm_num,
      Complex.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  · have h := hasDerivAt_cMand Real.pi
    rw [Complex.exp_pi_mul_I] at h
    exact h.congr_deriv (by ring)
  · exact (((hasDerivAt_exp_mul_I 0).div_const 4).const_add (-1 : ℂ)).congr_deriv (by simp)
  · push_cast
    ring

end M15
