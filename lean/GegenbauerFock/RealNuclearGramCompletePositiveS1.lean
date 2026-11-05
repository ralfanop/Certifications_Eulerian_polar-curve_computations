import GegenbauerFock.RealNuclearGramSingularSummability
import GegenbauerFock.RealCompactGramPositiveSingularBasisBridge
import GegenbauerFock.RealNuclearOneCompleteSourceSingularS1

/-!
# V007 — exact nuclear S₁ singular trace for actual positive Gram basis

Combine the independently certified real Gram singular summability
converse with the existing complete-source singular-basis exact
real projective nuclear norm theorem.

If an arbitrary real nuclear T admits a COMPLETE source Hilbert basis
of STRICTLY POSITIVE eigenvectors of its actual Gram T†T, then
the normalized output vectors are automatically orthonormal, the
singular operator series converges in operator norm, and the genuine
universal projective nuclear infimum equals the positive singular sum.

Crucially, no target complete basis, unitary polar extension or
surjectivity of T is required: T may be a nuclear weighted unilateral
shift with a nontrivial cokernel.

The general non-injective case still requires the zero-eigenspace
support construction and arbitrary-index spectral assembly.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Nuclearity makes the complete *positive* actual Gram-basis
singular amplitudes summable, with no prior summability hypothesis. -/
theorem HasRealNuclearRankOneSeries.completePositiveGram_singular_summable
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b : HilbertBasis ℕ ℝ H)
    (mu : ℕ → ℝ) (hmu : ∀ n, 0 < mu n)
    (heig : ∀ n, (T.adjoint ∘L T) (b n) = mu n • b n) :
    Summable (fun n => Real.sqrt (mu n)) := by
  let c : ℕ → H := fun n =>
    (Real.sqrt (mu n))⁻¹ • T (b n)
  have hc : Orthonormal ℝ c :=
    realGram_positiveEigenfamily_output_orthonormal_v007
      T b b.orthonormal mu hmu heig
  have hpair : ∀ n, T (b n) = Real.sqrt (mu n) • c n := by
    intro n
    dsimp only [c]
    rw [smul_smul,
      mul_inv_cancel₀ (Real.sqrt_pos.2 (hmu n)).ne',
      one_smul]
  exact hT.singularFamily_summable
    b c b.orthonormal hc (fun n => Real.sqrt (mu n))
    (fun n => Real.sqrt_nonneg _) hpair

/-- Exact universal real S₁ trace norm for an arbitrary actual
nuclear operator possessing a complete strictly positive Gram
eigenbasis, with no assumption that the output singular family
is complete or that kernel and cokernel dimensions agree. -/
theorem HasRealNuclearRankOneSeries.completePositiveGram_exact_nuclear_infimum
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b : HilbertBasis ℕ ℝ H)
    (mu : ℕ → ℝ) (hmu : ∀ n, 0 < mu n)
    (heig : ∀ n, (T.adjoint ∘L T) (b n) = mu n • b n) :
    realNuclearInfimum T =
      ∑' n : ℕ, Real.sqrt (mu n) := by
  have hs : Summable (fun n => Real.sqrt (mu n)) :=
    hT.completePositiveGram_singular_summable b mu hmu heig
  exact (realGram_completePositiveEigenbasis_nuclear_exact_trace_v007
    T b mu hmu hs heig).2

/-- Full operator-norm convergent ACTUAL singular rank-one series
for an arbitrary nuclear operator with a complete positive Gram
source eigenbasis. The target vectors need NOT be a Hilbert basis. -/
theorem HasRealNuclearRankOneSeries.completePositiveGram_operator_svd
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b : HilbertBasis ℕ ℝ H)
    (mu : ℕ → ℝ) (hmu : ∀ n, 0 < mu n)
    (heig : ∀ n, (T.adjoint ∘L T) (b n) = mu n • b n) :
    T = ∑' n : ℕ,
      Real.sqrt (mu n) •
        rankOne ℝ
          ((Real.sqrt (mu n))⁻¹ • T (b n)) (b n) := by
  let c : ℕ → H := fun n =>
    (Real.sqrt (mu n))⁻¹ • T (b n)
  have hc : Orthonormal ℝ c :=
    realGram_positiveEigenfamily_output_orthonormal_v007
      T b b.orthonormal mu hmu heig
  have hpair : ∀ n, T (b n) = Real.sqrt (mu n) • c n := by
    intro n
    dsimp only [c]
    rw [smul_smul,
      mul_inv_cancel₀ (Real.sqrt_pos.2 (hmu n)).ne',
      one_smul]
  have hs : Summable (fun n => Real.sqrt (mu n)) :=
    hT.completePositiveGram_singular_summable b mu hmu heig
  exact realOneFullSourceSingular_operator_tsum_eq
    T b c hc (fun n => Real.sqrt (mu n))
    (fun n => Real.sqrt_nonneg _) hs hpair

#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.completePositiveGram_singular_summable
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.completePositiveGram_exact_nuclear_infimum
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.completePositiveGram_operator_svd

end GegenbauerFock.Ultraspherical
