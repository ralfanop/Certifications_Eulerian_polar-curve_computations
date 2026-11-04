import GegenbauerFock.RealCompactGramPositiveSingularBasisBridge

/-!
# V007 — removing zero Gram modes from a real singular system

For ANY bounded map T between real Hilbert spaces, the actual source
Gram G = T†T has precisely the same kernel as T. If an orthonormal
source family consists of Gram eigenvectors with NONNEGATIVE real
eigenvalues, its zero-eigenvalue elements are annihilated by T.

On the subtype of strictly positive eigenvalue indices, the
normalized images T(b_i)/sqrt(mu_i) are an orthonormal target family.
No assumption that zero eigenvalues are absent, that the output
family is complete, or that a global unitary phase exists.

This prepares the support-restricted singular system needed for a
general polar partial isometry. It does NOT establish existence of a
spectral eigenbasis for arbitrary compact real T or a global SVD.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
variable [CompleteSpace E] [CompleteSpace F]

/-- The source Gram and the original real map have the same kernel,
for every bounded real Hilbert operator, compact or otherwise. -/
theorem realGram_apply_eq_zero_iff_v007
    (T : E →L[ℝ] F) (x : E) :
    (T.adjoint ∘L T) x = 0 ↔ T x = 0 := by
  constructor
  · intro hx
    have hsq : ‖T x‖ ^ 2 = 0 := by
      have heig : (T.adjoint ∘L T) x = (0 : ℝ) • x := by
        simpa using hx
      simpa using realGram_eigenvector_norm_sq_v007 T 0 x heig
    have hn : ‖T x‖ = 0 := by
      nlinarith [norm_nonneg (T x)]
    exact norm_eq_zero.mp hn
  · intro hx
    change T.adjoint (T x) = 0
    simp [hx]

/-- A zero Gram eigenvector must lie in the actual kernel of T. -/
theorem realGram_zeroEigenvector_in_kernel_v007
    (T : E →L[ℝ] F) (x : E)
    (hx : (T.adjoint ∘L T) x = (0 : ℝ) • x) :
    T x = 0 := by
  apply (realGram_apply_eq_zero_iff_v007 T x).mp
  simpa using hx

/-- For an eigenfamily with nonnegative eigenvalues, all indices
outside the positive support are necessarily annihilated by T. -/
theorem realGram_nonpositiveEigenfamily_in_kernel_v007
    {ι : Type*} (T : E →L[ℝ] F)
    (b : ι → E) (mu : ι → ℝ)
    (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i)
    (i : ι) (hi : ¬ 0 < mu i) :
    T (b i) = 0 := by
  have hzero : mu i = 0 := le_antisymm (le_of_not_gt hi) (hmu i)
  have hz : (T.adjoint ∘L T) (b i) = (0 : ℝ) • b i := by
    simpa [hzero] using heig i
  exact realGram_zeroEigenvector_in_kernel_v007 T (b i) hz

/-- The normalized image of a strictly positive Gram eigenvector
satisfies the left singular-vector equation T†c = sqrt(mu)b. -/
theorem realGram_active_singular_pair_adjoint_v007
    (T : E →L[ℝ] F)
    (mu : ℝ) (hmu : 0 < mu)
    (x : E) (hx : (T.adjoint ∘L T) x = mu • x) :
    T.adjoint ((Real.sqrt mu)⁻¹ • T x) =
      Real.sqrt mu • x := by
  have hroot : Real.sqrt mu ≠ 0 := (Real.sqrt_pos.2 hmu).ne'
  have hsq : (Real.sqrt mu) ^ 2 = mu :=
    Real.sq_sqrt hmu.le
  rw [map_smul]
  change (Real.sqrt mu)⁻¹ • ((T.adjoint ∘L T) x) = _
  rw [hx, smul_smul, ← hsq, pow_two, ← mul_assoc,
    inv_mul_cancel₀ hroot, one_mul]

/-- Normalizing the actual images on only the POSITIVE source
Gram eigenmodes produces an orthonormal family in the target.
Zero eigenvalues are permitted anywhere among the source indices. -/
theorem realGram_positiveSupport_output_orthonormal_v007
    {ι : Type*} (T : E →L[ℝ] F)
    (b : ι → E) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i) :
    Orthonormal ℝ
      (fun i : {i : ι // 0 < mu i} =>
        (Real.sqrt (mu i))⁻¹ • T (b i)) := by
  have hrestricted : Orthonormal ℝ
      (fun i : {i : ι // 0 < mu i} => b i) := by
    constructor
    · intro i
      exact hb.norm_eq_one i
    · intro i j hij
      apply hb.inner_eq_zero
      intro hval
      exact hij (Subtype.ext hval)
  exact realGram_positiveEigenfamily_output_orthonormal_v007
    T (fun i : {i : ι // 0 < mu i} => b i)
    hrestricted (fun i : {i : ι // 0 < mu i} => mu i)
    (fun i => i.property) (fun i => heig i)

#print axioms GegenbauerFock.Ultraspherical.realGram_apply_eq_zero_iff_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_zeroEigenvector_in_kernel_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_nonpositiveEigenfamily_in_kernel_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_active_singular_pair_adjoint_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_positiveSupport_output_orthonormal_v007

end GegenbauerFock.Ultraspherical
