import Mathlib

/-! Local control of ordinary gradients by the covariant magnetic energy,
M14 §7.4 (equation 114), consolidated TeX SHA256
5eaa4b4c760b8bf347385ecde00033f9a38ba13ed8b60a9b648eaabb69fee662.
This is an actual pointwise and Bochner-integral estimate for the two
components; the identification of d with weak derivatives and Rellich
compactness of the restricted Sobolev embedding are separate. -/
open MeasureTheory Filter
noncomputable section
namespace Manuscript14.LocalMagneticCoercivity

theorem covariant_pointwise (h a : ℝ) (d u : ℂ) :
    h^2 * ‖d‖^2 ≤ 2 * ‖h • d - a • u‖^2 + 2 * a^2 * ‖u‖^2 := by
  have ht : ‖h • d‖ ≤ ‖h • d - a • u‖ + ‖a • u‖ := by
    calc
      ‖h • d‖ = ‖(h • d - a • u) + a • u‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hm := mul_nonneg (sub_nonneg.mpr ht)
    (add_nonneg (add_nonneg (norm_nonneg (h • d - a • u)) (norm_nonneg (a • u)))
      (norm_nonneg (h • d)))
  have hsq : ‖h • d‖^2 ≤ 2 * ‖h • d - a • u‖^2 + 2 * ‖a • u‖^2 := by
    nlinarith [sq_nonneg (‖h • d - a • u‖ - ‖a • u‖)]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsq
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsq
  nlinarith [hsq]

theorem local_pointwise (h a M : ℝ) (d u : ℂ) (hM : 0 ≤ M)
    (ha : |a| ≤ M) :
    h^2 * ‖d‖^2 ≤ 2 * ‖h • d - a • u‖^2 + 2 * M^2 * ‖u‖^2 := by
  have hs : a^2 ≤ M^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (add_nonneg hM (abs_nonneg a)),
      sq_abs a]
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖u‖)
  linarith [covariant_pointwise h a d u]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem local_integral_control (s : Set X) (h M : ℝ) (A : X → ℝ)
    (d u : X → ℂ) (hM : 0 ≤ M)
    (hA : ∀ᵐ x ∂μ.restrict s, |A x| ≤ M)
    (hd : Integrable (fun x => ‖d x‖^2) (μ.restrict s))
    (hp : Integrable (fun x => ‖h • d x - A x • u x‖^2) (μ.restrict s))
    (hu : Integrable (fun x => ‖u x‖^2) (μ.restrict s)) :
    h^2 * (∫ x in s, ‖d x‖^2 ∂μ) ≤
      2 * (∫ x in s, ‖h • d x - A x • u x‖^2 ∂μ) +
      2 * M^2 * (∫ x in s, ‖u x‖^2 ∂μ) := by
  have hf := hd.const_mul (h^2)
  have hg := (hp.const_mul (2 : ℝ)).add (hu.const_mul (2 * M^2))
  have hae : ∀ᵐ x ∂μ.restrict s,
      h^2 * ‖d x‖^2 ≤ 2 * ‖h • d x - A x • u x‖^2 + 2 * M^2 * ‖u x‖^2 := by
    filter_upwards [hA] with x hx using local_pointwise h (A x) M (d x) (u x) hM hx
  have hi := integral_mono_ae hf hg hae
  rw [integral_add (hp.const_mul (2 : ℝ)) (hu.const_mul (2 * M^2)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  exact hi

/-- Two-coordinate quantitative local energy bound, with no spectral assumption. -/
theorem local_two_coordinates (s : Set X) (h M : ℝ) (A₁ A₂ : X → ℝ)
    (d₁ d₂ u : X → ℂ) (hM : 0 ≤ M)
    (hA₁ : ∀ᵐ x ∂μ.restrict s, |A₁ x| ≤ M)
    (hA₂ : ∀ᵐ x ∂μ.restrict s, |A₂ x| ≤ M)
    (hd₁ : Integrable (fun x => ‖d₁ x‖^2) (μ.restrict s))
    (hd₂ : Integrable (fun x => ‖d₂ x‖^2) (μ.restrict s))
    (hp₁ : Integrable (fun x => ‖h • d₁ x - A₁ x • u x‖^2) (μ.restrict s))
    (hp₂ : Integrable (fun x => ‖h • d₂ x - A₂ x • u x‖^2) (μ.restrict s))
    (hu : Integrable (fun x => ‖u x‖^2) (μ.restrict s)) :
    h^2 * ((∫ x in s, ‖d₁ x‖^2 ∂μ) + (∫ x in s, ‖d₂ x‖^2 ∂μ)) ≤
      2 * ((∫ x in s, ‖h • d₁ x - A₁ x • u x‖^2 ∂μ) +
           (∫ x in s, ‖h • d₂ x - A₂ x • u x‖^2 ∂μ)) +
      4 * M^2 * (∫ x in s, ‖u x‖^2 ∂μ) := by
  have h₁ := local_integral_control s h M A₁ d₁ u hM hA₁ hd₁ hp₁ hu
  have h₂ := local_integral_control s h M A₂ d₂ u hM hA₂ hd₂ hp₂ hu
  nlinarith

#print axioms covariant_pointwise
#print axioms local_pointwise
#print axioms local_integral_control
#print axioms local_two_coordinates

end Manuscript14.LocalMagneticCoercivity
