import GegenbauerFock.GegenbauerIntrinsicEntireFourierSampleRangeBijection
import GegenbauerFock.GegenbauerIntrinsicEntireFourierLocallyUniformInstability

/-!
# V007 — continuity of the forward Fourier map on bounded samples

The inverse of exact ultraspherical Fourier–Bochner sampling is nowhere
continuous in the uniform topology, even when exact identification holds.
In the opposite direction the GENUINE integral sampling operator is
globally Lipschitz, with a constant controlled by the evaluation-kernel
norm and the operator norm of the actual intrinsic Fock synthesis.

This proves the forward/backward topological asymmetry directly for the
actual Fourier–Bochner integral, not an auxiliary coefficient map.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A global pointwise Lipschitz bound UNIFORM over every bounded set of
complex sampling frequencies, in terms of the true intrinsic Gaussian
Fock continuous-linear-map operator norm. -/
theorem ultraspherical_fourierBochner_uniformSamples_forward_dist_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam)) (z : S) :
    dist
      (UniformFun.toFun (ultraspherical_fourierBochner_uniformSamples lam S g) z)
      (UniformFun.toFun (ultraspherical_fourierBochner_uniformSamples lam S f) z) ≤
    (Real.sqrt (Real.exp (alpha * R ^ 2)) *
      ‖C_intrinsicEntire lam alpha hlam ha‖) * dist g f := by
  have hdiff :
      (∫ v : ℝ, g v *
        Complex.exp (Complex.I * (z : ℂ) * (v : ℂ) / 2)
        ∂(Ultraspherical.measure lam)) -
      (∫ v : ℝ, f v *
        Complex.exp (Complex.I * (z : ℂ) * (v : ℂ) / 2)
        ∂(Ultraspherical.measure lam)) =
      (∫ v : ℝ, (g - f) v *
        Complex.exp (Complex.I * (z : ℂ) * (v : ℂ) / 2)
        ∂(Ultraspherical.measure lam)) := by
    rw [← evaluatedOperator_eq_integral lam alpha hlam ha (z : ℂ) g,
      ← evaluatedOperator_eq_integral lam alpha hlam ha (z : ℂ) f,
      ← evaluatedOperator_eq_integral lam alpha hlam ha (z : ℂ) (g - f)]
    exact (map_sub (evaluatedOperator lam alpha hlam ha (z : ℂ)) g f).symm
  have hb := ultraspherical_fourierBochner_norm_le_on_disk
    lam alpha hlam ha R hR (g - f) (z : ℂ) (hbound z z.property)
  have hc := (C_intrinsicEntire lam alpha hlam ha).le_opNorm (g - f)
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(∫ v : ℝ, g v *
      Complex.exp (Complex.I * (z : ℂ) * (v : ℂ) / 2)
      ∂(Ultraspherical.measure lam)) -
    (∫ v : ℝ, f v *
      Complex.exp (Complex.I * (z : ℂ) * (v : ℂ) / 2)
      ∂(Ultraspherical.measure lam))‖ ≤ _
  rw [hdiff]
  calc
    _ ≤ Real.sqrt (Real.exp (alpha * R ^ 2)) *
        ‖C_intrinsicEntire lam alpha hlam ha (g - f)‖ := hb
    _ ≤ Real.sqrt (Real.exp (alpha * R ^ 2)) *
        (‖C_intrinsicEntire lam alpha hlam ha‖ * ‖g - f‖) :=
      mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
    _ = (Real.sqrt (Real.exp (alpha * R ^ 2)) *
          ‖C_intrinsicEntire lam alpha hlam ha‖) * ‖g - f‖ := by ring

/-- The genuine uniform-frequency Fourier–Bochner sampling map is
continuous in the FORWARD direction on every bounded frequency set. -/
theorem ultraspherical_fourierBochner_uniformSamples_continuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R) :
    Continuous (ultraspherical_fourierBochner_uniformSamples lam S) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply UniformFun.tendsto_iff_tendstoUniformly.mpr
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let K : ℝ := Real.sqrt (Real.exp (alpha * R ^ 2)) *
    ‖C_intrinsicEntire lam alpha hlam ha‖
  have hK : 0 ≤ K :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hK1 : 0 < K + 1 := by linarith
  have hrad : 0 < ε / (K + 1) := div_pos hε hK1
  have hnear : Metric.ball f (ε / (K + 1)) ∈ nhds f :=
    Metric.ball_mem_nhds hrad
  have hfrac : K / (K + 1) < 1 :=
    (div_lt_iff₀ hK1).mpr (by linarith)
  have hstrict : K * (ε / (K + 1)) < ε := by
    calc
      K * (ε / (K + 1)) = (K / (K + 1)) * ε := by ring
      _ < 1 * ε := mul_lt_mul_of_pos_right hfrac hε
      _ = ε := one_mul _
  filter_upwards [hnear] with g hg z
  have hsmall : dist g f < ε / (K + 1) := Metric.mem_ball.mp hg
  have hb := ultraspherical_fourierBochner_uniformSamples_forward_dist_le
    lam alpha hlam ha S R hR hbound f g z
  have hscaled : K * dist g f ≤ K * (ε / (K + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hsmall) hK
  have hfinal :
      dist
        (UniformFun.toFun (ultraspherical_fourierBochner_uniformSamples lam S g) z)
        (UniformFun.toFun (ultraspherical_fourierBochner_uniformSamples lam S f) z) <
        ε :=
    lt_of_le_of_lt (le_trans (by simpa only [K] using hb) hscaled) hstrict
  simpa only [Function.comp_apply] using hfinal

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_forward_dist_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_continuous

end GegenbauerFock.GeneralUltrasphericalFock
