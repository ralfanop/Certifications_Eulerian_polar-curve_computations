import Mathlib

/-! M13 §4.5, Theorem 4.14, equations (78)–(81).
First checkpoint: exact spectral multiplier, sharp pointwise bound and
attainment, algebraic band projection and monodromy on spectral functions.
Not yet the L² essential-supremum/operator norm, Mellin unitary or kernel integral.
Source TeX SHA256 c19570110db446d6e0178ea965b1ed6075af166f0ed7424d7421b1bd7bee3dcd.
-/
namespace Manuscript13.MellinRindler20261124

def band : Set ℝ := Set.Icc (-(1/2 : ℝ)) (1/2 : ℝ)

noncomputable def multiplier (n : ℤ) (ξ : ℝ) : ℝ :=
  Real.exp (-(2 * Real.pi * (n : ℝ) * ξ))

theorem multiplier_pos (n : ℤ) (ξ : ℝ) : 0 < multiplier n ξ :=
  Real.exp_pos _

theorem multiplier_reciprocal (n : ℤ) (ξ : ℝ) :
    multiplier n ξ = 1 / Real.exp (2 * Real.pi * (n : ℝ) * ξ) := by
  unfold multiplier
  rw [Real.exp_neg, one_div]

theorem multiplier_zero (ξ : ℝ) : multiplier 0 ξ = 1 := by
  simp [multiplier]

theorem multiplier_add (n m : ℤ) (ξ : ℝ) :
    multiplier (n + m) ξ = multiplier n ξ * multiplier m ξ := by
  unfold multiplier
  rw [Int.cast_add, ← Real.exp_add]
  congr 1
  ring

theorem multiplier_inverse (n : ℤ) (ξ : ℝ) :
    multiplier n ξ * multiplier (-n) ξ = 1 := by
  rw [← multiplier_add, add_neg_cancel, multiplier_zero]

theorem multiplier_bound (n : ℤ) (ξ : ℝ) (h : ξ ∈ band) :
    multiplier n ξ ≤ Real.exp (Real.pi * |(n : ℝ)|) := by
  change -(1/2 : ℝ) ≤ ξ ∧ ξ ≤ (1/2 : ℝ) at h
  unfold multiplier
  apply Real.exp_le_exp.mpr
  have hp : 0 ≤ Real.pi := Real.pi_pos.le
  by_cases hn : 0 ≤ (n : ℝ)
  · rw [abs_of_nonneg hn]
    have hh := mul_nonneg (mul_nonneg hp hn) (show 0 ≤ ξ + 1/2 by linarith [h.1])
    nlinarith only [hh]
  · have hn' : (n : ℝ) ≤ 0 := le_of_not_ge hn
    rw [abs_of_nonpos hn']
    have hh := mul_nonneg (mul_nonneg hp (neg_nonneg.mpr hn')) (show 0 ≤ 1/2 - ξ by linarith [h.2])
    nlinarith only [hh]

theorem multiplier_attains (n : ℤ) :
    ∃ ξ ∈ band, multiplier n ξ = Real.exp (Real.pi * |(n : ℝ)|) := by
  by_cases hn : 0 ≤ (n : ℝ)
  · refine ⟨-(1/2 : ℝ), ?_, ?_⟩
    · change -(1/2 : ℝ) ≤ -(1/2 : ℝ) ∧ -(1/2 : ℝ) ≤ (1/2 : ℝ)
      constructor <;> norm_num
    · unfold multiplier
      rw [abs_of_nonneg hn]
      congr 1
      ring
  · refine ⟨(1/2 : ℝ), ?_, ?_⟩
    · change -(1/2 : ℝ) ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ (1/2 : ℝ)
      constructor <;> norm_num
    · unfold multiplier
      rw [abs_of_nonpos (le_of_not_ge hn)]
      congr 1
      ring

theorem multiplier_isGreatest (n : ℤ) :
    IsGreatest (multiplier n '' band) (Real.exp (Real.pi * |(n : ℝ)|)) := by
  constructor
  · obtain ⟨ξ, hξ, heq⟩ := multiplier_attains n
    exact ⟨ξ, hξ, heq⟩
  · intro y hy
    obtain ⟨ξ, hξ, rfl⟩ := hy
    exact multiplier_bound n ξ hξ

noncomputable def project (f : ℝ → ℂ) (ξ : ℝ) : ℂ := by
  classical
  exact if ξ ∈ band then f ξ else 0

theorem project_idempotent (f : ℝ → ℂ) : project (project f) = project f := by
  classical
  funext ξ
  by_cases h : ξ ∈ band <;> simp [project, h]

theorem project_add (f g : ℝ → ℂ) :
    project (fun ξ => f ξ + g ξ) = fun ξ => project f ξ + project g ξ := by
  classical
  funext ξ
  by_cases h : ξ ∈ band <;> simp [project, h]

noncomputable def mono (n : ℤ) (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (multiplier n ξ : ℂ) * f ξ

theorem mono_zero (f : ℝ → ℂ) : mono 0 f = f := by
  funext ξ
  simp [mono, multiplier_zero]

theorem mono_add (n m : ℤ) (f : ℝ → ℂ) :
    mono n (mono m f) = mono (n + m) f := by
  funext ξ
  simp only [mono, multiplier_add, Complex.ofReal_mul, mul_assoc]

theorem mono_inverse (n : ℤ) (f : ℝ → ℂ) :
    mono n (mono (-n) f) = f := by
  rw [mono_add, add_neg_cancel, mono_zero]

theorem mono_project_commute (n : ℤ) (f : ℝ → ℂ) :
    mono n (project f) = project (mono n f) := by
  classical
  funext ξ
  by_cases h : ξ ∈ band <;> simp [mono, project, h]

#print axioms multiplier_pos
#print axioms multiplier_reciprocal
#print axioms multiplier_zero
#print axioms multiplier_add
#print axioms multiplier_inverse
#print axioms multiplier_bound
#print axioms multiplier_attains
#print axioms multiplier_isGreatest
#print axioms project_idempotent
#print axioms project_add
#print axioms mono_zero
#print axioms mono_add
#print axioms mono_inverse
#print axioms mono_project_commute
end Manuscript13.MellinRindler20261124
