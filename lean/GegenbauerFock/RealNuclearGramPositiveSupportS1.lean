import GegenbauerFock.RealNuclearGeneralIndexSingularSummability
import GegenbauerFock.RealCompactGramActiveSingularModes

/-!
# V007 — positive Gram support singular mass, with arbitrary zero modes

For an actual arbitrary real-Hilbert nuclear T and an orthonormal
family of eigenvectors of its genuine Gram T†T, allow nonnegative
eigenvalues including zero. Restrict indices to the POSITIVE support
{ i // 0 < μ_i }; this type may be finite, countable, or empty.

The actual normalized output vectors on this subtype are orthonormal.
The arbitrary-index nuclear trace duality then proves that the sum of
their singular amplitudes sqrt(μ_i) is finite and at most the universal
real nuclear projective infimum, with NO global unitary phase.

The existence of a complete eigenbasis and the operator-level
SVD/polar partial isometry remain separately necessary.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

/-- The positive-subtype restriction of an orthonormal source
eigenfamily remains orthonormal even with zero Gram modes elsewhere. -/
theorem realNuclearGram_positiveSupport_source_orthonormal
    (b : ι → H) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) :
    Orthonormal ℝ (fun i : {i : ι // 0 < mu i} => b i) := by
  constructor
  · intro i
    exact hb.norm_eq_one i
  · intro i j hij
    apply hb.inner_eq_zero
    intro hval
    exact hij (Subtype.ext hval)

/-- Nuclearity forces summability of the ACTUAL singular amplitudes
restricted to the positive Gram support, even with any zero modes. -/
theorem HasRealNuclearRankOneSeries.gram_positiveSupport_summable
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b : ι → H) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i) :
    Summable (fun i : {i : ι // 0 < mu i} => Real.sqrt (mu i)) := by
  let ba : {i : ι // 0 < mu i} → H := fun i => b i
  let ca : {i : ι // 0 < mu i} → H :=
    fun i => (Real.sqrt (mu i))⁻¹ • T (b i)
  let sigma : {i : ι // 0 < mu i} → ℝ :=
    fun i => Real.sqrt (mu i)
  have hba : Orthonormal ℝ ba :=
    realNuclearGram_positiveSupport_source_orthonormal b hb mu
  have hca : Orthonormal ℝ ca :=
    realGram_positiveSupport_output_orthonormal_v007 T b hb mu hmu heig
  have hpair : ∀ i, T (ba i) = sigma i • ca i := by
    intro i
    dsimp only [ba, ca, sigma]
    rw [smul_smul,
      mul_inv_cancel₀ (Real.sqrt_pos.2 i.property).ne', one_smul]
  exact hT.generalIndexSingular_summable
    ba ca hba hca sigma (fun i => Real.sqrt_nonneg _) hpair

/-- For any orthonormal actual Gram eigenfamily, the TOTAL
positive-support singular mass is bounded by every nuclear cost,
hence by the universal projective real S₁ infimum. -/
theorem HasRealNuclearRankOneSeries.gram_positiveSupport_tsum_le_infimum
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b : ι → H) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i) :
    (∑' i : {i : ι // 0 < mu i}, Real.sqrt (mu i)) ≤
      realNuclearInfimum T := by
  let ba : {i : ι // 0 < mu i} → H := fun i => b i
  let ca : {i : ι // 0 < mu i} → H :=
    fun i => (Real.sqrt (mu i))⁻¹ • T (b i)
  let sigma : {i : ι // 0 < mu i} → ℝ :=
    fun i => Real.sqrt (mu i)
  have hba : Orthonormal ℝ ba :=
    realNuclearGram_positiveSupport_source_orthonormal b hb mu
  have hca : Orthonormal ℝ ca :=
    realGram_positiveSupport_output_orthonormal_v007 T b hb mu hmu heig
  have hpair : ∀ i, T (ba i) = sigma i • ca i := by
    intro i
    dsimp only [ba, ca, sigma]
    rw [smul_smul,
      mul_inv_cancel₀ (Real.sqrt_pos.2 i.property).ne', one_smul]
  exact hT.generalIndexSingular_tsum_le_infimum
    ba ca hba hca sigma (fun i => Real.sqrt_nonneg _) hpair

#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_positiveSupport_source_orthonormal
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.gram_positiveSupport_summable
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.gram_positiveSupport_tsum_le_infimum

end GegenbauerFock.Ultraspherical
