import GegenbauerFock.RealNuclearGramBoundedPartialPhase
import GegenbauerFock.RealNuclearGramPositiveSupportS1

/-!
# V007 — bounded real partial phase for the ACTUAL positive Gram modes

For any real bounded T and any actual Gram eigenfamily b with
nonnegative eigenvalues μ, construct the genuine whole-space bounded
real partial phase by restricting to the positive spectral subtype
{ i // 0 < μ i } and forming W=C B†.

The crucial orthonormality of the normalized output is derived from
the actual T†T eigenrelations, not postulated. Zero modes are never
normalized and the phase is allowed to have initial/final defects
of different dimensions.

This W maps every supplied positive input Gram mode to its normalized
output singular vector. The construction is a true bounded partial
isometry on H; to identify it with the FULL polar factor of T and
obtain T=W|T|, the supplied positive family must be proved COMPLETE
in (ker T)ᗮ and a positive absolute value |T| must be constructed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

/-- Construct the bounded real polar partial phase directly from the
actual nonnegative Gram T†T eigenrelations on the positive subtype. -/
noncomputable def realGramPositivePartialPhase
    (T : H →L[ℝ] H)
    (b : ι → H) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i) :
    H →L[ℝ] H :=
  realPhasePartialCLM
    (fun i : {i : ι // 0 < mu i} => b i)
    (fun i : {i : ι // 0 < mu i} =>
      (Real.sqrt (mu i))⁻¹ • T (b i))
    (realNuclearGram_positiveSupport_source_orthonormal b hb mu)
    (realGram_positiveSupport_output_orthonormal_v007
      T b hb mu hmu heig)

/-- The real bounded phase of the actual Gram sends each positive
source eigenvector to the corresponding normalized T-output. -/
theorem realGramPositivePartialPhase_on_mode
    (T : H →L[ℝ] H)
    (b : ι → H) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i)
    (i : {i : ι // 0 < mu i}) :
    realGramPositivePartialPhase T b hb mu hmu heig (b i) =
      (Real.sqrt (mu i))⁻¹ • T (b i) := by
  unfold realGramPositivePartialPhase
  exact realPhasePartialCLM_on_source_mode
    (fun j : {j : ι // 0 < mu j} => b j)
    (fun j : {j : ι // 0 < mu j} =>
      (Real.sqrt (mu j))⁻¹ • T (b j))
    (realNuclearGram_positiveSupport_source_orthonormal b hb mu)
    (realGram_positiveSupport_output_orthonormal_v007
      T b hb mu hmu heig) i

/-- Exact source projection of the bounded polar phase attached to
the actual positive Gram eigenmodes. -/
theorem realGramPositivePartialPhase_initial_projection
    (T : H →L[ℝ] H)
    (b : ι → H) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i) :
    (realGramPositivePartialPhase T b hb mu hmu heig).adjoint ∘L
      realGramPositivePartialPhase T b hb mu hmu heig =
    (realPhaseOrthSynthesis
      (fun i : {i : ι // 0 < mu i} => b i)
      (realNuclearGram_positiveSupport_source_orthonormal b hb mu)
    ).toContinuousLinearMap ∘L
    (realPhaseOrthSynthesis
      (fun i : {i : ι // 0 < mu i} => b i)
      (realNuclearGram_positiveSupport_source_orthonormal b hb mu)
    ).toContinuousLinearMap.adjoint := by
  unfold realGramPositivePartialPhase
  exact realPhasePartialCLM_initial_projection
    (fun i : {i : ι // 0 < mu i} => b i)
    (fun i : {i : ι // 0 < mu i} =>
      (Real.sqrt (mu i))⁻¹ • T (b i))
    (realNuclearGram_positiveSupport_source_orthonormal b hb mu)
    (realGram_positiveSupport_output_orthonormal_v007
      T b hb mu hmu heig)

/-- Exact final projection of the bounded polar phase attached to
the actual positive Gram eigenmodes, with arbitrary output defect. -/
theorem realGramPositivePartialPhase_final_projection
    (T : H →L[ℝ] H)
    (b : ι → H) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i) :
    realGramPositivePartialPhase T b hb mu hmu heig ∘L
      (realGramPositivePartialPhase T b hb mu hmu heig).adjoint =
    (realPhaseOrthSynthesis
      (fun i : {i : ι // 0 < mu i} =>
        (Real.sqrt (mu i))⁻¹ • T (b i))
      (realGram_positiveSupport_output_orthonormal_v007
        T b hb mu hmu heig)
    ).toContinuousLinearMap ∘L
    (realPhaseOrthSynthesis
      (fun i : {i : ι // 0 < mu i} =>
        (Real.sqrt (mu i))⁻¹ • T (b i))
      (realGram_positiveSupport_output_orthonormal_v007
        T b hb mu hmu heig)
    ).toContinuousLinearMap.adjoint := by
  unfold realGramPositivePartialPhase
  exact realPhasePartialCLM_final_projection
    (fun i : {i : ι // 0 < mu i} => b i)
    (fun i : {i : ι // 0 < mu i} =>
      (Real.sqrt (mu i))⁻¹ • T (b i))
    (realNuclearGram_positiveSupport_source_orthonormal b hb mu)
    (realGram_positiveSupport_output_orthonormal_v007
      T b hb mu hmu heig)

#print axioms GegenbauerFock.Ultraspherical.realGramPositivePartialPhase_on_mode
#print axioms GegenbauerFock.Ultraspherical.realGramPositivePartialPhase_initial_projection
#print axioms GegenbauerFock.Ultraspherical.realGramPositivePartialPhase_final_projection

end GegenbauerFock.Ultraspherical
