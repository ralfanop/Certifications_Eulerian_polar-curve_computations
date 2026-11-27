import EulerianGrothendieck.JacobiCFCIntegral20261127
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The manuscript uses angular frequency rather than the Mathlib
2*pi frequency convention. Real dilation gives precisely its normalised
Fourier density. Compact smooth functions are Schwartz functions,
so inversion and all absolute moments follow from Mathlib. -/
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory NormedSpace
open scoped SchwartzMap FourierTransform InnerProductSpace
namespace M12SchwartzFourier
open M12BilateralJacobi M12JacobiCFCIntegral

def dilation : ℝ ≃L[ℝ] ℝ where
  toLinearEquiv :=
    { toFun := fun x => (2*Real.pi)*x
      invFun := fun x => x/(2*Real.pi)
      left_inv := by
        intro x
        have h : (2*Real.pi:ℝ) ≠ 0 := by positivity
        field_simp
      right_inv := by
        intro x
        have h : (2*Real.pi:ℝ) ≠ 0 := by positivity
        field_simp
      map_add' := by intro x y; ring
      map_smul' := by intro c x; simp only [smul_eq_mul]; ring }
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_id.div_const _

theorem dilation_apply (x : ℝ) : dilation x = 2*Real.pi*x := rfl

def dilate (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ dilation f

theorem dilate_apply (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    dilate f x = f (2*Real.pi*x) := rfl

def weight (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) := 𝓕 (dilate f)

/-- Exact angular-frequency normalization in M12 (180). -/
theorem weight_formula (f : 𝓢(ℝ,ℂ)) (t : ℝ) :
    weight f t = ((2*Real.pi:ℝ)⁻¹:ℝ) •
      ∫ x : ℝ, f x * Complex.exp (-((t:ℂ)*Complex.I*(x:ℂ))) := by
  change (𝓕 (dilate f : ℝ → ℂ)) t = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h : (fun x : ℝ => Complex.exp (↑(-2 * Real.pi*x*t)*Complex.I) • dilate f x) =
      fun x : ℝ => (fun y : ℝ => f y*Complex.exp (-((t:ℂ)*Complex.I*(y:ℂ)))) (2*Real.pi*x) := by
    funext x
    rw [dilate_apply,smul_eq_mul]
    rw [mul_comm]
    congr 1
    push_cast
    ring
  rw [h,Measure.integral_comp_mul_left,abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ)⁻¹)]

theorem weight_continuous (f : 𝓢(ℝ,ℂ)) : Continuous (weight f : ℝ → ℂ) :=
  (weight f).continuous

theorem mixed_moment (g : 𝓢(ℝ,ℂ)) (N k : ℕ) :
    Integrable (fun t : ℝ => ‖g t‖*|t|^k*(1+|t|)^N) := by
  induction N generalizing k with
  | zero =>
    simpa [Real.norm_eq_abs,mul_comm] using g.integrable_pow_mul volume k
  | succ n ih =>
    have h := (ih k).add (ih (k+1))
    convert h using 1
    ext t
    simp only [Pi.add_apply,pow_succ]
    ring

theorem weight_moment (f : 𝓢(ℝ,ℂ)) (N : ℕ) :
    Integrable (fun t : ℝ => ‖weight f t‖*|t|*(1+|t|)^N) := by
  simpa only [pow_one] using mixed_moment (weight f) N 1

/-- Scalar Fourier inversion at angular frequency with the exact
normalisation of the manuscript. -/
theorem scalar_inversion (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    f x = ∫ t : ℝ, weight f t * Complex.exp (((t:ℂ)*Complex.I)*(x:ℂ)) := by
  have h := (dilate f).integrable.fourierInv_fourier_eq
    (weight f).integrable (v := x/(2*Real.pi)) (dilate f).continuous.continuousAt
  change (𝓕⁻ (weight f : ℝ → ℂ)) (x/(2*Real.pi)) = dilate f (x/(2*Real.pi)) at h
  rw [Real.fourierInv_eq',dilate_apply] at h
  have hpi : (2*Real.pi:ℝ) ≠ 0 := by positivity
  have hx : 2*Real.pi*(x/(2*Real.pi)) = x := by field_simp
  rw [hx] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_eq_mul,mul_comm]
  congr 1
  rw [Real.inner_apply]
  push_cast
  have hpic : (2*↑Real.pi:ℂ) ≠ 0 := by exact_mod_cast hpi
  field_simp
  <;> ring

/-- Full identification for an actual compactly supported smooth
function, with no scalar inversion or integrability assumption.
The function is evaluated on the real spectrum of J. -/
theorem actual_cfc_fourier (u : Bonds) (f : ℝ → ℂ)
    (hc : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) :
    hom u ({ toFun := fun z : Spec u => f (z:ℂ).re
             continuous_toFun := hs.continuous.comp (Complex.continuous_re.comp continuous_subtype_val) } :
      C(Spec u,ℂ)) =
      ∫ t : ℝ, weight (hc.toSchwartzMap hs) t • exp (((t:ℂ)*Complex.I) • J u) := by
  let g := hc.toSchwartzMap hs
  apply cfc_fourier u (weight g) (weight g).integrable
  intro z
  have hz : (z:ℂ).im = 0 := by
    have h := congrArg Complex.im (spectrum_real u z)
    simp at h
    linarith
  have he : ((z:ℂ).re:ℂ) = (z:ℂ) := by
    apply Complex.ext
    · simp
    · simp [hz]
  change g (z:ℂ).re = ∫ t : ℝ, weight g t * Complex.exp (((t:ℂ)*Complex.I)*(z:ℂ))
  rw [scalar_inversion g (z:ℂ).re]
  rw [he]

end M12SchwartzFourier
#print axioms M12SchwartzFourier.dilation_apply
#print axioms M12SchwartzFourier.dilate_apply
#print axioms M12SchwartzFourier.weight_formula
#print axioms M12SchwartzFourier.weight_continuous
#print axioms M12SchwartzFourier.mixed_moment
#print axioms M12SchwartzFourier.weight_moment
#print axioms M12SchwartzFourier.scalar_inversion
#print axioms M12SchwartzFourier.actual_cfc_fourier
