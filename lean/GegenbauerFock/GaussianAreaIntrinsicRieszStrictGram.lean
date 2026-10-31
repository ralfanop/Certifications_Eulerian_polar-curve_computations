import GegenbauerFock.GaussianAreaIntrinsicRieszExactGramScalar
import GegenbauerFock.GaussianAreaIntrinsicCoherentExponentialSeparation

/-!
# V007 — strict positivity and exact degeneracy of finite Gaussian Fock Gram energies

For the actual intrinsic Gaussian-L² Bargmann–Fock Riesz kernel, the
already certified identity of the full complex exponential Gram quadratic
form with the Hilbert norm squared permits an exact strict-positivity
criterion. This criterion is expressed in terms of the *actual* finite
coherent superposition and does not assume linear independence of
reproducing vectors at arbitrary repeated evaluation points.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The real part of the exact finite Gaussian exponential Gram energy
is strictly positive precisely when its intrinsic Hilbert-space coherent
superposition is nonzero. This also handles repeated evaluation points. -/
theorem intrinsicRieszKernel_exp_gram_re_pos_iff
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    0 < Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) ↔
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) ≠ 0 := by
  rw [intrinsicRieszKernel_exp_gram_re_eq_norm_sq s z c alpha ha]
  constructor
  · intro h hx
    rw [hx] at h
    simp at h
  · intro hx
    exact sq_pos_of_pos (norm_pos_iff.mpr hx)

/-- Vanishing of the real part of a finite Gaussian exponential
Gram form is equivalent to vanishing of its entire complex value. -/
theorem intrinsicRieszKernel_exp_gram_re_eq_zero_iff
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = 0 ↔
    (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = 0 := by
  rw [intrinsicRieszKernel_exp_gram_re_eq_norm_sq s z c alpha ha,
    intrinsicRieszKernel_exp_gram_eq_zero_iff s z c alpha ha]
  constructor
  · intro h
    have hn :
        ‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ = 0 := by
      have hnonneg :
          0 ≤ ‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ :=
        norm_nonneg _
      nlinarith
    exact norm_eq_zero.mp hn
  · intro h
    rw [h]
    simp

/-- A nonzero finite exponential Gram scalar has strictly positive
real part: it cannot be purely imaginary or negative. -/
theorem intrinsicRieszKernel_exp_gram_re_pos_iff_ne_zero
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    0 < Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) ↔
    (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) ≠ 0 := by
  rw [intrinsicRieszKernel_exp_gram_re_pos_iff s z c alpha ha]
  exact (not_congr (intrinsicRieszKernel_exp_gram_eq_zero_iff s z c alpha ha)).symm

/-- The genuine exponential Fock Gram energy lies on the strictly
positive real axis exactly when its finite coherent superposition is
nonzero, including for repeated evaluation points. -/
theorem intrinsicRieszKernel_exp_gram_positive_real_iff
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    (∃ r : ℝ, 0 < r ∧
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = (r : ℂ)) ↔
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) ≠ 0 := by
  constructor
  · rintro ⟨r, hr, hgram⟩
    apply (intrinsicRieszKernel_exp_gram_re_pos_iff s z c alpha ha).mp
    rw [hgram]
    simpa only [Complex.ofReal_re] using hr
  · intro hx
    refine ⟨‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ ^ 2, ?_, ?_⟩
    · exact sq_pos_of_pos (norm_pos_iff.mpr hx)
    · exact intrinsicRieszKernel_exp_gram_eq_complex_norm_sq s z c alpha ha

/-- A finite Gaussian-Fock exponential Gram energy is strictly
positive real exactly when its associated entire exponential sum is
nonzero at some point. No distinctness assumption on the nodes is
required. -/
theorem intrinsicRieszKernel_exp_gram_positive_real_iff_exists_witness
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    (∃ r : ℝ, 0 < r ∧
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = (r : ℂ)) ↔
    ∃ w : ℂ, (∑ i ∈ s,
      c i * Complex.exp ((alpha : ℂ) * w * star (z i))) ≠ 0 := by
  rw [intrinsicRieszKernel_exp_gram_positive_real_iff s z c alpha ha]
  constructor
  · intro hnonzero
    by_contra hnowitness
    push_neg at hnowitness
    exact hnonzero
      ((intrinsicRieszKernel_finite_coherent_eq_zero_iff_exp_sum
        s z c alpha ha).mpr hnowitness)
  · rintro ⟨w, hw⟩ hzero
    exact hw
      ((intrinsicRieszKernel_finite_coherent_eq_zero_iff_exp_sum
        s z c alpha ha).mp hzero w)

/-- A quantitative bound for finite coherent exponential sampling in
the genuine Gaussian-L² Fock space: the squared absolute value at any
complex test point is bounded by the exact exponential Gaussian weight
times the real Gram energy. This inequality does not require distinct
interpolation nodes. -/
theorem intrinsicRieszKernel_exp_sum_norm_sq_le_exp_mul_gram_re
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) (w : ℂ) :
    ‖∑ i ∈ s, c i *
        Complex.exp ((alpha : ℂ) * w * star (z i))‖ ^ 2 ≤
      Real.exp (alpha * ‖w‖ ^ 2) *
        Complex.re (∑ i ∈ s, ∑ j ∈ s,
          star (c i) * c j *
            Complex.exp ((alpha : ℂ) * z i * star (z j))) := by
  have h := intrinsicEntire_evaluation_sq_le_exp_norm alpha ha
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) w
  change
    ‖entireRepresentative alpha
      (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) w‖ ^ 2 ≤
      Real.exp (alpha * ‖w‖ ^ 2) *
        ‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ ^ 2 at h
  rw [← intrinsicRieszKernel_inner alpha ha w
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)),
    intrinsicRieszKernel_finite_coherent_pairing_exp s z c alpha ha w] at h
  rwa [intrinsicRieszKernel_exp_gram_re_eq_norm_sq s z c alpha ha]

/-- Each complex coherent sample gives a computable nonnegative
lower bound for the exact Gaussian Gram energy, normalized by the
strictly positive diagonal exponential weight. -/
theorem intrinsicRieszKernel_exp_gram_re_ge_normalized_sample
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) (w : ℂ) :
    ‖∑ i ∈ s, c i *
        Complex.exp ((alpha : ℂ) * w * star (z i))‖ ^ 2 /
      Real.exp (alpha * ‖w‖ ^ 2) ≤
        Complex.re (∑ i ∈ s, ∑ j ∈ s,
          star (c i) * c j *
            Complex.exp ((alpha : ℂ) * z i * star (z j))) := by
  apply (div_le_iff₀ (Real.exp_pos (alpha * ‖w‖ ^ 2))).2
  have h := intrinsicRieszKernel_exp_sum_norm_sq_le_exp_mul_gram_re
    s z c alpha ha w
  rw [mul_comm (Real.exp (alpha * ‖w‖ ^ 2))
    (Complex.re (∑ i ∈ s, ∑ j ∈ s,
      star (c i) * c j *
        Complex.exp ((alpha : ℂ) * z i * star (z j))))] at h
  exact h

/-- At the origin, the exact intrinsic Gaussian Gram energy bounds
the squared magnitude of the total coherent coefficient sum. -/
theorem intrinsicRieszKernel_exp_gram_re_ge_origin_coeff_sum
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    ‖∑ i ∈ s, c i‖ ^ 2 ≤
      Complex.re (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) := by
  simpa using
    (intrinsicRieszKernel_exp_sum_norm_sq_le_exp_mul_gram_re
      s z c alpha ha 0)

/-- Uniform Gaussian coherent sampling bound on every closed disk
of radius R: the entire exponential superposition is controlled in
supremum norm by its *exact* intrinsic Gram energy. -/
theorem intrinsicRieszKernel_exp_sum_uniform_disk_bound
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha)
    (R : ℝ) (hR : 0 ≤ R) (w : ℂ) (hw : ‖w‖ ≤ R) :
    ‖∑ i ∈ s, c i *
        Complex.exp ((alpha : ℂ) * w * star (z i))‖ ^ 2 ≤
      Real.exp (alpha * R ^ 2) *
        Complex.re (∑ i ∈ s, ∑ j ∈ s,
          star (c i) * c j *
            Complex.exp ((alpha : ℂ) * z i * star (z j))) := by
  have hRadiusSq : ‖w‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).mpr hw
  have hWeight :
      Real.exp (alpha * ‖w‖ ^ 2) ≤ Real.exp (alpha * R ^ 2) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hRadiusSq (le_of_lt ha))
  have hGram : 0 ≤ Complex.re (∑ i ∈ s, ∑ j ∈ s,
      star (c i) * c j *
        Complex.exp ((alpha : ℂ) * z i * star (z j))) :=
    intrinsicRieszKernel_exp_gram_nonneg s z c alpha ha
  exact (intrinsicRieszKernel_exp_sum_norm_sq_le_exp_mul_gram_re
    s z c alpha ha w).trans
      (mul_le_mul_of_nonneg_right hWeight hGram)

/-- Quantitative robustness under arbitrary finite coefficient
perturbations: the squared pointwise error on a closed disk is
controlled by the Gram energy of the coefficient difference.
Repeated nodes are allowed, so this is naturally a seminorm bound. -/
theorem intrinsicRieszKernel_exp_sum_coefficient_perturbation_disk_bound
    {ι : Type*} (s : Finset ι) (z c d : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha)
    (R : ℝ) (hR : 0 ≤ R) (w : ℂ) (hw : ‖w‖ ≤ R) :
    ‖(∑ i ∈ s, c i *
         Complex.exp ((alpha : ℂ) * w * star (z i))) -
      (∑ i ∈ s, d i *
         Complex.exp ((alpha : ℂ) * w * star (z i)))‖ ^ 2 ≤
      Real.exp (alpha * R ^ 2) *
        Complex.re (∑ i ∈ s, ∑ j ∈ s,
          star (c i - d i) * (c j - d j) *
            Complex.exp ((alpha : ℂ) * z i * star (z j))) := by
  simpa only [sub_mul, Finset.sum_sub_distrib] using
    (intrinsicRieszKernel_exp_sum_uniform_disk_bound
      s z (fun i => c i - d i) alpha ha R hR w hw)

/-- The uniform disk perturbation bound in its useful norm form:
the interpolation error is at most the square root of the exact
Gaussian Gram energy of the coefficient perturbation, times the
positive disk exponential weight. -/
theorem intrinsicRieszKernel_exp_sum_coefficient_perturbation_disk_norm_le_sqrt_gram
    {ι : Type*} (s : Finset ι) (z c d : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha)
    (R : ℝ) (hR : 0 ≤ R) (w : ℂ) (hw : ‖w‖ ≤ R) :
    ‖(∑ i ∈ s, c i *
        Complex.exp ((alpha : ℂ) * w * star (z i))) -
      (∑ i ∈ s, d i *
        Complex.exp ((alpha : ℂ) * w * star (z i)))‖ ≤
      Real.sqrt (Real.exp (alpha * R ^ 2) *
        Complex.re (∑ i ∈ s, ∑ j ∈ s,
          star (c i - d i) * (c j - d j) *
            Complex.exp ((alpha : ℂ) * z i * star (z j)))) := by
  have hgram : 0 ≤ Complex.re (∑ i ∈ s, ∑ j ∈ s,
      star (c i - d i) * (c j - d j) *
        Complex.exp ((alpha : ℂ) * z i * star (z j))) :=
    intrinsicRieszKernel_exp_gram_nonneg
      s z (fun i => c i - d i) alpha ha
  have hnonneg : 0 ≤ Real.exp (alpha * R ^ 2) *
      Complex.re (∑ i ∈ s, ∑ j ∈ s,
        star (c i - d i) * (c j - d j) *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hgram
  have hsq := intrinsicRieszKernel_exp_sum_coefficient_perturbation_disk_bound
    s z c d alpha ha R hR w hw
  have hsqrt := Real.sq_sqrt hnonneg
  have hnon := norm_nonneg
    ((∑ i ∈ s, c i *
        Complex.exp ((alpha : ℂ) * w * star (z i))) -
      (∑ i ∈ s, d i *
        Complex.exp ((alpha : ℂ) * w * star (z i))))
  have hsqrt_nonneg := Real.sqrt_nonneg
    (Real.exp (alpha * R ^ 2) *
      Complex.re (∑ i ∈ s, ∑ j ∈ s,
        star (c i - d i) * (c j - d j) *
          Complex.exp ((alpha : ℂ) * z i * star (z j))))
  nlinarith

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_pos_iff
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_eq_zero_iff
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_pos_iff_ne_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_positive_real_iff
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_positive_real_iff_exists_witness
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_sum_norm_sq_le_exp_mul_gram_re
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_ge_normalized_sample
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_ge_origin_coeff_sum
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_sum_uniform_disk_bound
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_sum_coefficient_perturbation_disk_bound
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_sum_coefficient_perturbation_disk_norm_le_sqrt_gram

end GegenbauerFock.GaussianArea
