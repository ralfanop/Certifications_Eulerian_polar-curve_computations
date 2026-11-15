import Manuscript15.Section27PrimalWasserstein

/-! M15, authoritative 15-Nov-2026 revision, §7.4 and §§6.3–6.5.
The real reconstruction inequalities are derived from actual Mathlib
characteristic functions and the primal W₁ of #309. The last three lemmas
are the exact CLOSED SCALAR consequences of the new Hopf sector expressions,
not claims of spectral continuation, analytic Lagrange inversion, or
identification of the Flajolet–Martin constant. -/

open MeasureTheory
noncomputable section

namespace Manuscript15.Revision20261115

open Manuscript15.Section27.Primal

def profile (μ : Measure ℝ) (t : ℝ) : ℝ := (charFun μ t).re

def X (a : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  a * t * (1 - profile μ (2*t))

def Y (a : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  a * t^2 / 2 * (profile μ t) ^ 2

theorem profile_abs_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    |profile μ t| ≤ 1 := by
  exact (Complex.abs_re_le_norm (charFun μ t)).trans (norm_charFun_le_one (μ := μ) t)

theorem profile_transport
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) (t : ℝ) :
    |profile μ t - profile ν t| ≤ |t| * wasserstein1 μ ν := by
  have h : |profile μ t - profile ν t| ≤ ‖charFun μ t - charFun ν t‖ := by
    simpa only [profile, Complex.sub_re] using
      Complex.abs_re_le_norm (charFun μ t - charFun ν t)
  exact h.trans (charFun_sub_le_wasserstein1 μ ν hμ hν t)

private theorem square_diff_bound (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |x^2-y^2| ≤ 2*|x-y| := by
  rw [show x^2-y^2=(x-y)*(x+y) by ring, abs_mul]
  have h : |x+y| ≤ 2 := (abs_add_le x y).trans (by linarith)
  calc
    |x-y|*|x+y| ≤ |x-y|*2 := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

theorem X_transport
    (a : ℝ) (ha : 0 ≤ a) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) (t : ℝ) :
    |X a μ t - X a ν t| ≤ 2*a*t^2*wasserstein1 μ ν := by
  rw [show X a μ t - X a ν t =
      a*t*(profile ν (2*t)-profile μ (2*t)) by unfold X; ring,
    abs_mul, abs_mul, abs_of_nonneg ha, abs_sub_comm (profile ν (2*t)) (profile μ (2*t))]
  calc
    a * |t|*|profile μ (2*t)-profile ν (2*t)| ≤
        a * |t|*(|2*t|*wasserstein1 μ ν) :=
      mul_le_mul_of_nonneg_left (profile_transport μ ν hμ hν (2*t)) (by positivity)
    _ = _ := by
      rw [abs_mul, show |(2:ℝ)|=2 by norm_num, ← sq_abs t]
      ring

theorem Y_transport
    (a : ℝ) (ha : 0 ≤ a) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) (t : ℝ) :
    |Y a μ t - Y a ν t| ≤ a * |t|^3*wasserstein1 μ ν := by
  have hs := square_diff_bound (profile μ t) (profile ν t)
    (profile_abs_le_one μ t) (profile_abs_le_one ν t)
  rw [show Y a μ t - Y a ν t =
      (a*t^2/2)*((profile μ t)^2-(profile ν t)^2) by unfold Y; ring,
      abs_mul, abs_of_nonneg (show 0 ≤ a*t^2/2 by positivity)]
  calc
    _ ≤ (a*t^2/2)*(2*|profile μ t-profile ν t|) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (a*t^2/2)*(2*(|t|*wasserstein1 μ ν)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (profile_transport μ ν hμ hν t) (by norm_num))
        (by positivity)
    _ = _ := by rw [← sq_abs t]; ring

/-- Actual real-coordinate bounds for the symmetric-law reconstruction;
real characteristic functions coincide with the real-part profile.
The bounds in fact hold for real-part profiles of arbitrary probability laws. -/
theorem reconstruction_transport
    (a : ℝ) (ha : 0 ≤ a) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) (t : ℝ) :
    |X a μ t-X a ν t| ≤ 2*a*t^2*wasserstein1 μ ν ∧
    |Y a μ t-Y a ν t| ≤ a * |t|^3*wasserstein1 μ ν :=
  ⟨X_transport a ha μ ν hμ hν t, Y_transport a ha μ ν hμ hν t⟩

def hopfScalar : ℝ := (2*Real.pi)^2

def terminalLeading (M : ℕ) : ℝ :=
  1/(2*(2*Real.pi)^(2*(M-1)))

theorem terminal_hopf_scalar (M : ℕ) :
    terminalLeading M = 1/(2*hopfScalar^(M-1)) := by
  unfold terminalLeading hopfScalar
  rw [pow_mul]

def oddSectorScalar (φ g : ℝ) : ℝ :=
  4*Real.pi*φ^2*Real.exp (-2*g)

def evenSectorScalar (φ g : ℝ) : ℝ :=
  Real.pi*Real.exp (2*g)/φ^2

theorem sector_scalar_product (φ g : ℝ) (hφ : 0 < φ) :
    oddSectorScalar φ g * evenSectorScalar φ g = hopfScalar := by
  have he : Real.exp (-2*g) * Real.exp (2*g) = 1 := by
    rw [← Real.exp_add, show -2*g+2*g=0 by ring, Real.exp_zero]
  unfold oddSectorScalar evenSectorScalar hopfScalar
  calc
    _ = (2*Real.pi)^2 * (Real.exp (-2*g)*Real.exp (2*g)) := by
      field_simp [ne_of_gt hφ] <;> ring
    _ = _ := by rw [he, mul_one]

theorem sector_scalar_ratio (φ g : ℝ) (hφ : 0 < φ) :
    oddSectorScalar φ g / evenSectorScalar φ g = 4*φ^4*Real.exp (-4*g) := by
  have hd : evenSectorScalar φ g ≠ 0 := ne_of_gt (by unfold evenSectorScalar; positivity)
  apply (div_eq_iff hd).2
  have he : Real.exp (-4*g)*Real.exp (2*g) = Real.exp (-2*g) := by
    rw [← Real.exp_add, show -4*g+2*g = -2*g by ring]
  unfold oddSectorScalar evenSectorScalar
  calc
    _ = 4*Real.pi*φ^2*(Real.exp (-4*g)*Real.exp (2*g)) := by rw [he]
    _ = _ := by field_simp [ne_of_gt hφ] <;> ring

theorem terminal_sector_scalar (M : ℕ) (φ g : ℝ) (hφ : 0 < φ) :
    terminalLeading M = 1/(2*(oddSectorScalar φ g * evenSectorScalar φ g)^(M-1)) := by
  rw [sector_scalar_product φ g hφ, terminal_hopf_scalar]

#print axioms Manuscript15.Revision20261115.profile_abs_le_one
#print axioms Manuscript15.Revision20261115.profile_transport
#print axioms Manuscript15.Revision20261115.X_transport
#print axioms Manuscript15.Revision20261115.Y_transport
#print axioms Manuscript15.Revision20261115.reconstruction_transport
#print axioms Manuscript15.Revision20261115.terminal_hopf_scalar
#print axioms Manuscript15.Revision20261115.sector_scalar_product
#print axioms Manuscript15.Revision20261115.sector_scalar_ratio
#print axioms Manuscript15.Revision20261115.terminal_sector_scalar

end Manuscript15.Revision20261115
