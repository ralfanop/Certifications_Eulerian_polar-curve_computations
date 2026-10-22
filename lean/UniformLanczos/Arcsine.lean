/-
Uniform Lanczos note, Lemma 3 (v): the Levin–Lubinsky form of the Mhaskar–Rakhmanov–Saff
equations, `(1/π) ∫_{-1}^{1} y Q'(y) dy/√(1-y²) = 1` and `(1/π) ∫_{-1}^{1} Q'(y) dy/√(1-y²) = 0`
(LL (1.13)–(1.14)), as Lebesgue integrals over `(-1,1)`.

* `arcsine_substitution` : `∫_{(-1,1)} f(y)/√(1-y²) dy = ∫₀^π f(cos θ) dθ` for **every**
  `f : ℝ → ℝ` (equality of Bochner integrals; no integrability hypothesis is needed, by the
  one-dimensional change-of-variables theorem for injective differentiable maps);
* `mrs_LL_first_iff` : LL (1.13) for `Q'(y) = (aM/(2N)) P(ay)` (P odd, continuous) holds iff
  `Hint (y ↦ y P y) a = N/M`, the note's endpoint equation;
* `mrs_LL_second` : LL (1.14) holds for every odd `Q'`.
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import UniformLanczos.MRS

open Set Real MeasureTheory intervalIntegral

namespace UniformLanczos

lemma cos_image_Ioo : cos '' Ioo 0 π = Ioo (-1 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    constructor
    · have := cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
      rwa [cos_pi] at this
    · have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
      rwa [cos_zero] at this
  · intro hy
    refine ⟨arccos y, ⟨arccos_pos.mpr hy.2, arccos_lt_pi.mpr hy.1⟩, ?_⟩
    exact cos_arccos hy.1.le hy.2.le

theorem arcsine_substitution (f : ℝ → ℝ) :
    ∫ y in Ioo (-1 : ℝ) 1, f y / √(1 - y ^ 2) = ∫ θ in (0 : ℝ)..π, f (cos θ) := by
  have hinj : InjOn cos (Ioo 0 π) := injOn_cos.mono Ioo_subset_Icc_self
  have hder : ∀ θ ∈ Ioo 0 π, HasDerivWithinAt cos (-sin θ) (Ioo 0 π) θ :=
    fun θ _ => (hasDerivAt_cos θ).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj
    (fun y => f y / √(1 - y ^ 2))
  rw [cos_image_Ioo] at h
  rw [h, intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsq : √(1 - cos θ ^ 2) = sin θ := (sin_eq_sqrt_one_sub_cos_sq hθ.1.le hθ.2.le).symm
  simp only [smul_eq_mul, abs_neg, abs_of_pos hs, hsq]
  field_simp

theorem mrs_LL_first_iff {P : ℝ → ℝ} (hP : Continuous P) (hodd : ∀ y, P (-y) = -P y)
    {a M N : ℝ} (hM : 0 < M) (hN : 0 < N) :
    (1 / π) * ∫ y in Ioo (-1 : ℝ) 1, y * (a * M / (2 * N) * P (a * y)) / √(1 - y ^ 2) = 1 ↔
      Hint (fun y => y * P y) a = N / M := by
  rw [arcsine_substitution (fun y => y * (a * M / (2 * N) * P (a * y)))]
  exact mrs_first_iff hP hodd hM hN

theorem mrs_LL_second {Qp : ℝ → ℝ} (hodd : ∀ y, Qp (-y) = -Qp y) :
    ∫ y in Ioo (-1 : ℝ) 1, Qp y / √(1 - y ^ 2) = 0 := by
  rw [arcsine_substitution Qp]
  exact mrs_second hodd

end UniformLanczos
