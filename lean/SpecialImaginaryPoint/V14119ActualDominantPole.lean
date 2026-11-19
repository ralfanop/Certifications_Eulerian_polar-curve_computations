import SpecialImaginaryPoint.V14119DominantPoleQuarticE6
import SpecialImaginaryPoint.V14119EulerianMeromorphicPoles

/-! M14, §2.1: identify the actual meromorphic poles with the phase
lattice and prove the sharp global minimum, not merely a minimum of
a proposed modulus formula. Uses the independent #370 and #447 results. -/
noncomputable section
namespace Manuscript14.ActualDominantPole

open Manuscript14.DominantPole

theorem phase_ne_one (θ : ℝ) (hlo : Real.pi / 2 ≤ |θ|)
    (hhi : |θ| < Real.pi) : phase θ ≠ 1 := by
  have hp : 0 < |θ| / 2 := by linarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hp (by linarith [Real.pi_pos] : |θ| / 2 < Real.pi)
  intro he
  have h := chord θ hhi
  rw [he, sub_self, norm_zero] at h
  linarith

theorem phase_ne_zero (θ : ℝ) : phase θ ≠ 0 := Complex.exp_ne_zero _

theorem phase_pole_eq (θ : ℝ) (j : ℤ) :
    Manuscript14.EulerianMeromorphicPoles.pole (phase θ) j = Manuscript14.DominantPole.pole θ (j : ℝ) := by
  unfold Manuscript14.EulerianMeromorphicPoles.pole Manuscript14.DominantPole.pole
  push_cast
  ring

/-- Every actual simple pole on the arc has modulus at least κ,
and equality occurs only at the principal pole at an arc endpoint. -/
theorem actual_pole_modulus (θ : ℝ) (j : ℤ)
    (hlo : Real.pi / 2 ≤ |θ|) (hhi : |θ| < Real.pi) :
    kappa ≤ ‖Manuscript14.EulerianMeromorphicPoles.pole (phase θ) j‖ ∧
      (‖Manuscript14.EulerianMeromorphicPoles.pole (phase θ) j‖ = kappa ↔ j = 0 ∧ |θ| = Real.pi / 2) := by
  rw [phase_pole_eq]
  have hm := complex_pole_minimum θ hlo hhi
  have hpos : 0 < |θ| := by linarith [Real.pi_pos]
  by_cases hj : j = 0
  · subst j
    exact ⟨by simpa using hm, by simpa using complex_pole_minimum_eq_iff θ hlo hhi⟩
  · have hs := complex_unique_pole θ j hhi hpos hj
    have hlt := lt_of_le_of_lt hm hs
    exact ⟨hlt.le, by simp [hj, ne_of_gt hlt]⟩

theorem actual_pole_lower (θ : ℝ) (z : ℂ)
    (hlo : Real.pi / 2 ≤ |θ|) (hhi : |θ| < Real.pi)
    (hz : meromorphicOrderAt (Manuscript14.EulerianMeromorphicPoles.generating (phase θ)) z = (-1 : WithTop ℤ)) :
    kappa ≤ ‖z‖ := by
  obtain ⟨j,rfl⟩ := (Manuscript14.EulerianMeromorphicPoles.generating_simple_pole_iff (phase θ) z
    (phase_ne_zero θ) (phase_ne_one θ hlo hhi)).mp hz
  exact (actual_pole_modulus θ j hlo hhi).1

theorem actual_pole_equality (θ : ℝ) (z : ℂ)
    (hlo : Real.pi / 2 ≤ |θ|) (hhi : |θ| < Real.pi)
    (hz : meromorphicOrderAt (Manuscript14.EulerianMeromorphicPoles.generating (phase θ)) z = (-1 : WithTop ℤ)) :
    ‖z‖ = kappa ↔ z = Manuscript14.EulerianMeromorphicPoles.pole (phase θ) 0 ∧ |θ| = Real.pi / 2 := by
  obtain ⟨j,hj⟩ := (Manuscript14.EulerianMeromorphicPoles.generating_simple_pole_iff (phase θ) z
    (phase_ne_zero θ) (phase_ne_one θ hlo hhi)).mp hz
  constructor
  · intro he
    have hh := (actual_pole_modulus θ j hlo hhi).2.mp (by rwa [hj] at he)
    exact ⟨by rw [hj,hh.1],hh.2⟩
  · rintro ⟨he,ht⟩
    rw [he]
    exact (actual_pole_modulus θ 0 hlo hhi).2.mpr ⟨rfl,ht⟩

theorem actual_arc_poles_isLeast : IsLeast
    {r : ℝ | ∃ θ : ℝ, ∃ z : ℂ,
      Real.pi / 2 ≤ |θ| ∧ |θ| < Real.pi ∧
      meromorphicOrderAt (Manuscript14.EulerianMeromorphicPoles.generating (phase θ)) z = (-1 : WithTop ℤ) ∧ r = ‖z‖}
    kappa := by
  have hθ : |Real.pi / 2| = Real.pi / 2 := abs_of_pos (by positivity)
  have hlo : Real.pi / 2 ≤ |Real.pi / 2| := by rw [hθ]
  have hhi : |Real.pi / 2| < Real.pi := by rw [hθ]; linarith [Real.pi_pos]
  constructor
  · refine ⟨Real.pi / 2, Manuscript14.EulerianMeromorphicPoles.pole (phase (Real.pi/2)) 0, hlo,hhi,?_,?_⟩
    · exact (Manuscript14.EulerianMeromorphicPoles.generating_simple_pole_iff _ _ (phase_ne_zero _) (phase_ne_one _ hlo hhi)).mpr ⟨0,rfl⟩
    · exact ((actual_pole_modulus (Real.pi/2) 0 hlo hhi).2.mpr ⟨rfl,hθ⟩).symm
  · rintro r ⟨θ,z,hlo',hhi',hz,rfl⟩
    exact actual_pole_lower θ z hlo' hhi' hz

theorem phase_positive_endpoint : phase (Real.pi/2) = Complex.I := by
  apply Complex.ext <;> simp [phase, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

theorem phase_negative_endpoint : phase (-Real.pi/2) = -Complex.I := by
  apply Complex.ext <;> simp [phase, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im, neg_div]

theorem endpoint_poles_exact :
    meromorphicOrderAt (Manuscript14.EulerianMeromorphicPoles.generating Complex.I) (Manuscript14.EulerianMeromorphicPoles.pole Complex.I 0) = (-1 : WithTop ℤ) ∧
      ‖Manuscript14.EulerianMeromorphicPoles.pole Complex.I 0‖ = kappa ∧
    meromorphicOrderAt (Manuscript14.EulerianMeromorphicPoles.generating (-Complex.I)) (Manuscript14.EulerianMeromorphicPoles.pole (-Complex.I) 0) = (-1 : WithTop ℤ) ∧
      ‖Manuscript14.EulerianMeromorphicPoles.pole (-Complex.I) 0‖ = kappa := by
  have hp : |Real.pi/2| = Real.pi/2 := abs_of_pos (by positivity)
  have hn : |-Real.pi/2| = Real.pi/2 := by rw [neg_div, abs_neg, hp]
  have hpp : Real.pi/2 ≤ |Real.pi/2| := by rw [hp]
  have hpn : Real.pi/2 ≤ |-Real.pi/2| := by rw [hn]
  have hqp : |Real.pi/2| < Real.pi := by rw [hp]; linarith [Real.pi_pos]
  have hqn : |-Real.pi/2| < Real.pi := by rw [hn]; linarith [Real.pi_pos]
  have hendpoint :
      meromorphicOrderAt (Manuscript14.EulerianMeromorphicPoles.generating (phase (Real.pi/2))) (Manuscript14.EulerianMeromorphicPoles.pole (phase (Real.pi/2)) 0) = (-1 : WithTop ℤ) ∧
        ‖Manuscript14.EulerianMeromorphicPoles.pole (phase (Real.pi/2)) 0‖ = kappa ∧
      meromorphicOrderAt (Manuscript14.EulerianMeromorphicPoles.generating (phase (-Real.pi/2))) (Manuscript14.EulerianMeromorphicPoles.pole (phase (-Real.pi/2)) 0) = (-1 : WithTop ℤ) ∧
        ‖Manuscript14.EulerianMeromorphicPoles.pole (phase (-Real.pi/2)) 0‖ = kappa := by
    exact ⟨(Manuscript14.EulerianMeromorphicPoles.generating_simple_pole_iff _ _ (phase_ne_zero _) (phase_ne_one _ hpp hqp)).mpr ⟨0,rfl⟩,
    (actual_pole_modulus _ 0 hpp hqp).2.mpr ⟨rfl,hp⟩,
    (Manuscript14.EulerianMeromorphicPoles.generating_simple_pole_iff _ _ (phase_ne_zero _) (phase_ne_one _ hpn hqn)).mpr ⟨0,rfl⟩,
    (actual_pole_modulus _ 0 hpn hqn).2.mpr ⟨rfl,hn⟩⟩
  simpa only [phase_positive_endpoint, phase_negative_endpoint] using hendpoint

#print axioms phase_ne_one
#print axioms phase_ne_zero
#print axioms phase_pole_eq
#print axioms actual_pole_modulus
#print axioms actual_pole_lower
#print axioms actual_pole_equality
#print axioms actual_arc_poles_isLeast
#print axioms phase_positive_endpoint
#print axioms phase_negative_endpoint
#print axioms endpoint_poles_exact
end Manuscript14.ActualDominantPole
