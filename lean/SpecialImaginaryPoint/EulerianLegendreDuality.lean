import Mathlib

/-! M14.120, Proposition 4.4: first kernel targets for the Eulerian
Legendre dual. Raw expressions are used away from zero; the continuous
extension is explicit. The global inverse, variance representation and
identification of the supremum are separate outstanding analytic targets. -/
namespace M14.EulerianLegendre
noncomputable section

def profile (x : ℝ) : ℝ := if x = 0 then 1 else Real.sinh x / x
def cumulant (x : ℝ) : ℝ := Real.log (profile x)
def langevinRaw (x : ℝ) : ℝ := Real.cosh x / Real.sinh x - 1 / x
def langevin (x : ℝ) : ℝ := if x = 0 then 0 else langevinRaw x
def stationary (x : ℝ) : ℝ := x * langevin x - cumulant x
def conjugate (m : ℝ) : ℝ := sSup (Set.range (fun x : ℝ => m * x - cumulant x))
def curvatureRaw (x : ℝ) : ℝ := 1 / x^2 - 1 / Real.sinh x ^ 2

theorem profile_zero : profile 0 = 1 := by simp [profile]
theorem stationary_zero : stationary 0 = 0 := by
  simp [stationary, langevin, cumulant, profile]

theorem stationary_formula (x : ℝ) (hx : x ≠ 0) :
    stationary x = x * (Real.cosh x / Real.sinh x) - 1 -
      Real.log (Real.sinh x / x) := by
  simp only [stationary, langevin, profile, cumulant, if_neg hx, langevinRaw]
  field_simp [hx]
  <;> ring

theorem curvature_reciprocal (x : ℝ) (hx : x ≠ 0)
    (hs : Real.sinh x ≠ 0) (hd : Real.sinh x ^ 2 - x^2 ≠ 0) :
    1 / curvatureRaw x =
      x^2 * Real.sinh x ^ 2 / (Real.sinh x ^ 2 - x^2) := by
  unfold curvatureRaw
  field_simp [hx, hs, hd] <;> ring

theorem curvature_positive_of_sinh_sq (x : ℝ)
    (hx : x ≠ 0) (h : x^2 < Real.sinh x ^ 2) :
    0 < curvatureRaw x := by
  have hp : 0 < x^2 := sq_pos_of_ne_zero hx
  have hs : 0 < Real.sinh x ^ 2 := lt_trans hp h
  unfold curvatureRaw
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hp h)

theorem reciprocal_origin (a : ℝ) (ha : a = 1 / 3) : 1 / a = 3 := by
  rw [ha]
  norm_num

-- Exact stationary supremum once the global supporting inequality is proved.
theorem conjugate_eq_of_support (m x : ℝ)
    (h : ∀ y : ℝ, m * y - cumulant y ≤ m * x - cumulant x) :
    conjugate m = m * x - cumulant x := by
  unfold conjugate
  apply le_antisymm
  · apply csSup_le
    · exact ⟨m * x - cumulant x, ⟨x, rfl⟩⟩
    · rintro z ⟨y, rfl⟩
      exact h y
  · apply le_csSup
    · exact ⟨m * x - cumulant x, by rintro z ⟨y, rfl⟩; exact h y⟩
    · exact ⟨x, rfl⟩

-- Envelope differentiation at a stationary point, with actual derivative premises.
theorem envelope_derivative (K inv : ℝ → ℝ) (m d : ℝ)
    (hi : HasDerivAt inv d m) (hk : HasDerivAt K m (inv m)) :
    HasDerivAt (fun t => t * inv t - K (inv t)) (inv m) m := by
  have hh := ((hasDerivAt_id m).mul hi).sub (hk.comp m hi)
  have hh' : HasDerivAt (fun t : ℝ => t * inv t - K (inv t))
      (1 * inv m + m * d - m * d) m := hh
  convert hh' using 1 <;> ring


-- Analytic stage: strict positivity of the actual sinh quotient off the origin.
theorem sinh_pos_of_pos (x : ℝ) (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have he : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  exact div_pos (sub_pos.mpr he) (by norm_num)

theorem sinh_ne_of_ne (x : ℝ) (hx : x ≠ 0) : Real.sinh x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hp := sinh_pos_of_pos (-x) (by linarith)
    rw [Real.sinh_neg] at hp
    exact ne_of_lt (by linarith)
  · exact ne_of_gt (sinh_pos_of_pos x h)

theorem profile_positive (x : ℝ) : 0 < profile x := by
  by_cases hx : x = 0
  · simp [hx, profile]
  · rw [profile, if_neg hx]
    rcases lt_or_gt_of_ne hx with h | h
    · have hp := sinh_pos_of_pos (-x) (by linarith)
      rw [Real.sinh_neg] at hp
      exact div_pos_of_neg_of_neg (by linarith) h
    · exact div_pos (sinh_pos_of_pos x h) h

theorem langevinRaw_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt langevinRaw (curvatureRaw x) x := by
  have hs := sinh_ne_of_ne x hx
  have hdS : HasDerivAt Real.sinh (Real.cosh x) x := by
    first | exact Real.hasDerivAt_sinh x | exact?
  have hdC : HasDerivAt Real.cosh (Real.sinh x) x := by
    first | exact Real.hasDerivAt_cosh x | exact?
  have hh := (hdC.div hdS hs).sub ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx)
  have he : HasDerivAt langevinRaw
      ((Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) / Real.sinh x ^ 2 -
        (0 * x - 1 * 1) / x ^ 2) x := hh
  have hpy := Real.cosh_sq_sub_sinh_sq x
  have hn : Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x = -1 := by
    nlinarith
  rw [hn] at he
  convert he using 1
  unfold curvatureRaw
  ring

theorem langevin_hasDerivAt_of_ne (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt langevin (curvatureRaw x) x := by
  apply (langevinRaw_hasDerivAt x hx).congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds (show x ∈ ({0} : Set ℝ)ᶜ by simpa using hx)] with y hy
  have hy' : y ≠ 0 := by simpa using hy
  simp [langevin, hy']


-- Prove the strict gap using the derivative of sinh x - x on [0,∞).
theorem cosh_gt_one_of_ne (x : ℝ) (hx : x ≠ 0) :
    1 < Real.cosh x := by
  have hs := sinh_ne_of_ne x hx
  have hsq : 0 < Real.sinh x ^ 2 := sq_pos_of_ne_zero hs
  have hc := Real.cosh_pos x
  have hident := Real.cosh_sq_sub_sinh_sq x
  by_contra! h
  have hprod : 0 ≤ (1 - Real.cosh x) * (1 + Real.cosh x) :=
    mul_nonneg (sub_nonneg.mpr h) (by linarith)
  nlinarith

theorem sinh_sub_id_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sinh y - y) (Real.cosh x - 1) x := by
  have hd : HasDerivAt Real.sinh (Real.cosh x) x := by
    first | exact Real.hasDerivAt_sinh x | exact?
  exact hd.sub (hasDerivAt_id x)

theorem sinh_gt_self_pos (x : ℝ) (hx : 0 < x) :
    x < Real.sinh x := by
  have hm : StrictMonoOn (fun y : ℝ => Real.sinh y - y) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    · exact (Real.continuous_sinh.sub continuous_id).continuousOn
    · intro y hy
      rw [interior_Ici] at hy
      have hypos : 0 < y := hy
      rw [(sinh_sub_id_derivative y).deriv]
      exact sub_pos.mpr (cosh_gt_one_of_ne y (ne_of_gt hypos))
  have hzero : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by
    exact (le_rfl : (0 : ℝ) ≤ 0)
  have hmem : x ∈ Set.Ici (0 : ℝ) := hx.le
  have h := hm hzero hmem hx
  simp only [Real.sinh_zero, sub_self] at h
  linarith

theorem sinh_sq_gt_sq (x : ℝ) (hx : x ≠ 0) :
    x^2 < Real.sinh x ^ 2 := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hg := sinh_gt_self_pos (-x) (by linarith)
    rw [Real.sinh_neg] at hg
    have hp : 0 < (x - Real.sinh x) * (-x - Real.sinh x) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · have hg := sinh_gt_self_pos x h
    have hp : 0 < (Real.sinh x - x) * (Real.sinh x + x) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

theorem curvature_positive_of_ne (x : ℝ) (hx : x ≠ 0) :
    0 < curvatureRaw x :=
  curvature_positive_of_sinh_sq x hx (sinh_sq_gt_sq x hx)

theorem langevin_deriv_positive_of_ne (x : ℝ) (hx : x ≠ 0) :
    0 < deriv langevin x := by
  rw [(langevin_hasDerivAt_of_ne x hx).deriv]
  exact curvature_positive_of_ne x hx

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.profile_zero
#print axioms M14.EulerianLegendre.stationary_zero
#print axioms M14.EulerianLegendre.stationary_formula
#print axioms M14.EulerianLegendre.curvature_reciprocal
#print axioms M14.EulerianLegendre.curvature_positive_of_sinh_sq
#print axioms M14.EulerianLegendre.reciprocal_origin
#print axioms M14.EulerianLegendre.conjugate_eq_of_support
#print axioms M14.EulerianLegendre.envelope_derivative

#print axioms M14.EulerianLegendre.sinh_pos_of_pos
#print axioms M14.EulerianLegendre.sinh_ne_of_ne
#print axioms M14.EulerianLegendre.profile_positive
#print axioms M14.EulerianLegendre.langevinRaw_hasDerivAt
#print axioms M14.EulerianLegendre.langevin_hasDerivAt_of_ne

#print axioms M14.EulerianLegendre.cosh_gt_one_of_ne
#print axioms M14.EulerianLegendre.sinh_sub_id_derivative
#print axioms M14.EulerianLegendre.sinh_gt_self_pos
#print axioms M14.EulerianLegendre.sinh_sq_gt_sq
#print axioms M14.EulerianLegendre.curvature_positive_of_ne
#print axioms M14.EulerianLegendre.langevin_deriv_positive_of_ne
