import GegenbauerFock.RealComplexPositiveSpectralTraceBridge
import GegenbauerFock.UltrasphericalSturmLiouvilleRealS2BasisGeneral
import GegenbauerFock.PhyslibHilbertSchmidtCompat
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — intrinsic S2 bridge for real and complex shared positive spectra

Given real and complex bounded Hilbert-space endomorphisms with complete
countable eigenbases and the SAME nonnegative summable eigenvalues,
both belong to their respective intrinsic real / source-compatible
complex Hilbert-Schmidt classes. Their squared S2 masses coincide on
arbitrary complete Hilbert bases (possibly differently indexed).

This is a conditional MATCHED-SPECTRUM statement. No canonical
complexification of the actual real Sturm operator is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open InnerProductSpace

variable {HR HC : Type*}
variable [NormedAddCommGroup HR] [InnerProductSpace ℝ HR] [CompleteSpace HR]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- An arbitrary nonnegative summable real sequence has summable
squares, with no boundedness parameter assumed. -/
theorem nonnegative_summable_has_summable_squares
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    (hs : Summable σ) :
    Summable (fun n : ℕ => σ n ^ 2) := by
  let M : ℝ := ∑' n : ℕ, σ n
  have hbound (n : ℕ) : σ n ≤ M := by
    have h := sum_le_hasSum ({n} : Finset ℕ)
      (fun j _ => hσ j) hs.hasSum
    simpa only [Finset.sum_singleton, M] using h
  have hterm (n : ℕ) : σ n ^ 2 ≤ M * σ n := by
    have hh := hbound n
    have hp := hσ n
    nlinarith
  apply Summable.of_nonneg_of_le
  · intro n
    exact sq_nonneg _
  · exact hterm
  · exact hs.mul_left M

/-- Positivity and summable eigenvalues imply actual basis-free real
S2 membership and Physlib-compatible COMPLEX S2 membership, with
the identical numerical square mass on every complete basis. -/
theorem real_complex_shared_positive_spectrum_intrinsicS2
    (R : HR →L[ℝ] HR) (T : HC →L[ℂ] HC)
    (bR : HilbertBasis ℕ ℝ HR) (bC : HilbertBasis ℕ ℂ HC)
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hs : Summable σ)
    (hR : ∀ n, R (bR n) = σ n • bR n)
    (hT : ∀ n, T (bC n) = (σ n : ℂ) • bC n)
    (hTpos : 0 ≤ T) :
    ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt T ∧
    (∀ {ι : Type*} (b : HilbertBasis ι ℝ HR),
      HasSum (fun i : ι => ‖R (b i)‖ ^ 2)
        (∑' n : ℕ, σ n ^ 2)) ∧
    (∀ {κ : Type*} (b : HilbertBasis κ ℂ HC),
      HasSum (fun i : κ => ‖T (b i)‖ ^ 2)
        (∑' n : ℕ, σ n ^ 2)) := by
  have hsq : Summable (fun n : ℕ => σ n ^ 2) :=
    nonnegative_summable_has_summable_squares σ hσ hs
  have hRmass (n : ℕ) : ‖R (bR n)‖ ^ 2 = σ n ^ 2 := by
    rw [hR n, norm_smul, bR.orthonormal.norm_eq_one n]
    simp only [mul_one, Real.norm_eq_abs, abs_of_nonneg (hσ n)]
  have hTmass (n : ℕ) : ‖T (bC n)‖ ^ 2 = σ n ^ 2 := by
    rw [hT n, norm_smul, bC.orthonormal.norm_eq_one n]
    simp only [mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hσ n)]
  have hbR : Summable (fun n : ℕ => ‖R (bR n)‖ ^ 2) :=
    hsq.congr (fun n => (hRmass n).symm)
  have hbC : Summable (fun n : ℕ => ‖T (bC n)‖ ^ 2) :=
    hsq.congr (fun n => (hTmass n).symm)
  have hself : IsSelfAdjoint T := .of_nonneg hTpos
  have hRealMass : (∑' n : ℕ, ‖R (bR n)‖ ^ 2) =
      ∑' n : ℕ, σ n ^ 2 := tsum_congr hRmass
  have hComplexMass : (∑' n : ℕ, ‖T (bC n)‖ ^ 2) =
      ∑' n : ℕ, σ n ^ 2 := tsum_congr hTmass
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ HC
  refine ⟨⟨w, b, ?_⟩, ?_, ?_⟩
  · exact (ProbabilisticTheory.hasSum_norm_sq_apply_of_selfAdjoint
      hself bC b hbC).summable
  · intro ι c
    have hh := realHilbert_hsMass_hasSum_any_basis R bR c hbR
    rw [← hRealMass]
    exact hh
  · intro κ c
    have hh := ProbabilisticTheory.hasSum_norm_sq_apply_of_selfAdjoint
      hself bC c hbC
    rw [← hComplexMass]
    exact hh

#print axioms GegenbauerFock.Ultraspherical.nonnegative_summable_has_summable_squares
#print axioms GegenbauerFock.Ultraspherical.real_complex_shared_positive_spectrum_intrinsicS2

end GegenbauerFock.Ultraspherical
