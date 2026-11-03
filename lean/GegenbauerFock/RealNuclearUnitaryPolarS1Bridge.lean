import GegenbauerFock.RealNuclearUnitaryLeftInvariance

/-!
# V007 — conditional nonselfadjoint real Schatten-S₁ via a unitary polar factor

This proves a genuine NON-SELFADJOINT extension: a real Hilbert
operator T that factors as U ∘ A, with U unitary and A having a
summable nonnegative complete eigenbasis, is nuclear with exact
universal projective cost equal to the singular-value sum.

A second, independent input predicate permits TWO complete Hilbert
bases b and c such that T(b_n) = sigma_n c_n. It implies existence
of the above unitary polar factorization by sending b to c.

Crucial scope: we do NOT yet prove that every arbitrary real nuclear
operator admits a two-sided SVD, or identify a separate CFC abs norm.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A potentially nonselfadjoint real Hilbert operator with a
unitary phase and positive diagonalizable nuclear amplitude. -/
def HasRealUnitaryPolarS1Factorization
    (T : H →L[ℝ] H) : Prop :=
  ∃ (U : H ≃ₗᵢ[ℝ] H) (A : H →L[ℝ] H),
    T = realUnitaryLeftCLM U A ∧ HasRealPositiveS1Eigenbasis A

/-- The TWO-basis summable singular-value criterion: source and
target orthonormal Hilbert bases may be different, hence T need
not be selfadjoint nor normal. -/
def HasRealSummableSingularHilbertBases
    (T : H →L[ℝ] H) : Prop :=
  ∃ (b c : HilbertBasis ℕ ℝ H) (sigma : ℕ → ℝ),
    (∀ n, 0 ≤ sigma n) ∧ Summable sigma ∧
    (∀ n, T (b n) = sigma n • c n)

/-- Every two-sided full real singular Hilbert basis gives a
unitary phase U sending b_n to c_n and a positive spectral-S₁
amplitude U⁻¹ T. -/
theorem HasRealSummableSingularHilbertBases.toUnitaryPolarS1
    {T : H →L[ℝ] H}
    (hT : HasRealSummableSingularHilbertBases T) :
    HasRealUnitaryPolarS1Factorization T := by
  obtain ⟨b, c, sigma, hnonneg, hs, heig⟩ := hT
  let U : H ≃ₗᵢ[ℝ] H := b.repr.trans c.repr.symm
  have hmap (n : ℕ) : U (b n) = c n := by
    change c.repr.symm (b.repr (b n)) = c n
    rw [b.repr_self, c.repr_symm_single]
  let A : H →L[ℝ] H := realUnitaryLeftCLM U.symm T
  have hA : HasRealPositiveS1Eigenbasis A := by
    refine ⟨b, sigma, hnonneg, hs, ?_⟩
    intro n
    change U.symm (T (b n)) = sigma n • b n
    rw [heig n, map_smul, ← hmap n, U.symm_apply_apply]
  have hTA : T = realUnitaryLeftCLM U A := by
    have h := realUnitaryLeftCLM_symm_comp U.symm T
    simpa only [A, LinearIsometryEquiv.symm_symm] using h.symm
  exact ⟨U, A, hTA, hA⟩

/-- Genuine rank-one nuclear operator class for every (possibly
nonselfadjoint) real unitary-polar S₁ factorization. -/
theorem HasRealUnitaryPolarS1Factorization.toRealNuclearRankOneSeries
    {T : H →L[ℝ] H}
    (hT : HasRealUnitaryPolarS1Factorization T) :
    HasRealNuclearRankOneSeries T := by
  obtain ⟨U, A, hTA, hA⟩ := hT
  obtain ⟨u, v, beta, hs, hseries⟩ :=
    hA.toPositiveRealNuclearExpansion.toRealNuclearRankOneSeries
  have hc : (∑' n : ℕ, ‖beta n‖ * ‖u n‖ * ‖v n‖) ∈
      RealNuclearCosts A :=
    ⟨u, v, beta, hs, hseries, rfl⟩
  have hc' := RealNuclearCosts.unitary_left U A hc
  obtain ⟨u', v', beta', hs', hseries', _⟩ := hc'
  rw [hTA]
  exact ⟨u', v', beta', hs', hseries'⟩

/-- Exact universal projective nuclear norm of any real operator
with a summable positive unitary polar factor. The right-hand
side is the sum of singular weights of that SAME operator; the
source eigenbasis also realizes T e_n = sigma_n U e_n. -/
theorem HasRealUnitaryPolarS1Factorization.exists_exact_singular_norm
    {T : H →L[ℝ] H}
    (hT : HasRealUnitaryPolarS1Factorization T) :
    ∃ (U : H ≃ₗᵢ[ℝ] H) (b : HilbertBasis ℕ ℝ H)
      (sigma : ℕ → ℝ),
      (∀ n, 0 ≤ sigma n) ∧ Summable sigma ∧
      (∀ n, T (b n) = sigma n • U (b n)) ∧
      realNuclearInfimum T = ∑' n : ℕ, sigma n := by
  obtain ⟨U, A, hTA, hA⟩ := hT
  obtain ⟨b, sigma, hnonneg, hs, heig, hnorm⟩ :=
    hA.exists_projective_norm_eq_eigenSum
  refine ⟨U, b, sigma, hnonneg, hs, ?_, ?_⟩
  · intro n
    rw [hTA]
    change U (A (b n)) = sigma n • U (b n)
    rw [heig n, map_smul]
  · rw [hTA, realNuclearInfimum_unitary_left_eq, hnorm]

/-- A TWO-basis nonselfadjoint singular-value summability witness
therefore supplies a genuine nuclear operator and a certified
singular-sum representation of its optimal nuclear norm. -/
theorem HasRealSummableSingularHilbertBases.nuclear_and_exact_norm
    {T : H →L[ℝ] H}
    (hT : HasRealSummableSingularHilbertBases T) :
    HasRealNuclearRankOneSeries T ∧
    ∃ (U : H ≃ₗᵢ[ℝ] H) (b : HilbertBasis ℕ ℝ H)
      (sigma : ℕ → ℝ),
      (∀ n, 0 ≤ sigma n) ∧ Summable sigma ∧
      (∀ n, T (b n) = sigma n • U (b n)) ∧
      realNuclearInfimum T = ∑' n : ℕ, sigma n := by
  have hpolar := hT.toUnitaryPolarS1
  exact ⟨hpolar.toRealNuclearRankOneSeries,
    hpolar.exists_exact_singular_norm⟩

#print axioms GegenbauerFock.Ultraspherical.HasRealSummableSingularHilbertBases.toUnitaryPolarS1
#print axioms GegenbauerFock.Ultraspherical.HasRealUnitaryPolarS1Factorization.toRealNuclearRankOneSeries
#print axioms GegenbauerFock.Ultraspherical.HasRealUnitaryPolarS1Factorization.exists_exact_singular_norm
#print axioms GegenbauerFock.Ultraspherical.HasRealSummableSingularHilbertBases.nuclear_and_exact_norm

end GegenbauerFock.Ultraspherical
