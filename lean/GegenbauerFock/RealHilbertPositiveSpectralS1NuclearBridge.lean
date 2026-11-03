import GegenbauerFock.RealHilbertPositiveDiagonalTraceNorm
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealS1SpectralBridge

/-!
# V007 — arbitrary real Hilbert positive spectral S1 implies nuclear S1

If a bounded real Hilbert operator has a complete countable orthonormal
eigenbasis with nonnegative summable eigenvalues, then its spectral
rank-one expansion converges absolutely in operator norm. Its projective
nuclear norm, defined as the infimum over ALL real rank-one series
representations, equals the positive spectral trace.

Unlike a proof about one special resolvent or one chosen positive
nuclear witness, this is an abstract real-Hilbert bridge. It does not
claim an equivalence with a separate complex CFC / Physlib trace norm.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Absolute summability of the positive rank-one spectral operators
in the full bounded-operator norm. -/
theorem realHilbert_positiveEigenbasis_rankOne_summable
    (b : HilbertBasis ℕ ℝ H) (σ : ℕ → ℝ)
    (hs : Summable σ) (hσ : ∀ n, 0 ≤ σ n) :
    Summable (fun n : ℕ => σ n • rankOne ℝ (b n) (b n)) := by
  apply Summable.of_norm
  convert hs using 1
  funext n
  rw [norm_smul, norm_rankOne, b.orthonormal.norm_eq_one n]
  simp only [one_mul, mul_one, Real.norm_eq_abs, abs_of_nonneg (hσ n)]

/-- An actual bounded operator diagonalised by the complete real
Hilbert eigenbasis equals its absolutely norm-convergent rank-one sum. -/
theorem realHilbert_positiveEigenbasis_operator_tsum_eq
    (b : HilbertBasis ℕ ℝ H) (T : H →L[ℝ] H)
    (σ : ℕ → ℝ) (hs : Summable σ) (hσ : ∀ n, 0 ≤ σ n)
    (heig : ∀ n, T (b n) = σ n • b n) :
    T = ∑' n : ℕ, σ n • rankOne ℝ (b n) (b n) := by
  let F : ℕ → H →L[ℝ] H :=
    fun n => σ n • rankOne ℝ (b n) (b n)
  let S : H →L[ℝ] H := ∑' n : ℕ, F n
  have hseries : Summable F :=
    realHilbert_positiveEigenbasis_rankOne_summable b σ hs hσ
  have hSb (k : ℕ) : S (b k) = σ k • b k := by
    have hsingle :
        HasSum (fun n : ℕ => if n = k then σ k • b k else 0)
          (σ k • b k) :=
      hasSum_ite_eq k (σ k • b k)
    have happly :
        HasSum (fun n : ℕ => F n (b k)) (S (b k)) := by
      have h := hseries.hasSum.mapL
        ((ContinuousLinearMap.apply ℝ H) (b k))
      simpa only [S, ContinuousLinearMap.apply_apply] using h
    have hterms :
        (fun n : ℕ => F n (b k)) =
          (fun n : ℕ => if n = k then σ k • b k else 0) := by
      funext n
      by_cases hnk : n = k
      · subst n
        have hinner : inner ℝ (b k) (b k) = 1 := by
          rw [real_inner_self_eq_norm_sq,
            b.orthonormal.norm_eq_one k]
          norm_num
        change σ k • (inner ℝ (b k) (b k) • b k) =
          if k = k then σ k • b k else 0
        rw [if_pos rfl, hinner, one_smul]
      · have horth : inner ℝ (b n) (b k) = 0 :=
          b.orthonormal.inner_eq_zero hnk
        change σ n • (inner ℝ (b n) (b k) • b n) =
          if n = k then σ k • b k else 0
        rw [if_neg hnk, horth, zero_smul, smul_zero]
    rw [hterms] at happly
    exact happly.unique hsingle
  have hdense :
      Dense ((Submodule.span ℝ (Set.range b)) : Set H) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    exact b.dense_span
  have hEq : T = S := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨k, rfl⟩
    exact (heig k).trans (hSb k).symm
  simpa only [S, F] using hEq

/-- Abstract positive spectral-S1 membership entails a real nuclear
rank-one decomposition of the ACTUAL operator and the exact intrinsic
projective nuclear norm as a spectral trace. -/
theorem HasRealPositiveS1Eigenbasis.exists_nuclear_exact_trace
    {T : H →L[ℝ] H} (hT : HasRealPositiveS1Eigenbasis T) :
    ∃ (b : HilbertBasis ℕ ℝ H) (σ : ℕ → ℝ),
      (∀ n, 0 ≤ σ n) ∧ Summable σ ∧
      HasRealNuclearRankOneSeries T ∧
      realNuclearInfimum T = ∑' n : ℕ, σ n := by
  obtain ⟨b, σ, hσ, hs, heig⟩ := hT
  have hseries := realHilbert_positiveEigenbasis_operator_tsum_eq
    b T σ hs hσ heig
  have hcost :
      Summable (fun n : ℕ => ‖σ n‖ * ‖b n‖ * ‖b n‖) := by
    apply hs.congr
    intro n
    rw [b.orthonormal.norm_eq_one n,
      Real.norm_eq_abs, abs_of_nonneg (hσ n)]
    ring
  have hclass : HasRealNuclearRankOneSeries T :=
    ⟨b, b, σ, hcost, hseries⟩
  have hdiag (n : ℕ) :
      inner ℝ (b n) (T (b n)) = σ n := by
    rw [heig n, real_inner_smul_right,
      real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one n]
    ring
  refine ⟨b, σ, hσ, hs, hclass, ?_⟩
  exact realHilbert_positiveDiagonal_nuclearInfimum_eq_trace
    b T σ hs hσ hseries hdiag

#print axioms GegenbauerFock.Ultraspherical.realHilbert_positiveEigenbasis_rankOne_summable
#print axioms GegenbauerFock.Ultraspherical.realHilbert_positiveEigenbasis_operator_tsum_eq
#print axioms GegenbauerFock.Ultraspherical.HasRealPositiveS1Eigenbasis.exists_nuclear_exact_trace

end GegenbauerFock.Ultraspherical
