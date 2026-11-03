import GegenbauerFock.RealNuclearUnitaryPolarS1Bridge

/-!
# V007 — exact real nonselfadjoint S₁ norm for the GIVEN singular bases

This strengthens the generic two-basis S₁ statement: the nuclear
projective norm is the sum of the specific singular weights supplied
in the hypothesis, not merely another existential presentation.

The proof uses the explicit positive nuclear representation for the
upper bound, and the universal finite-trace rank-one dual estimate
for the lower bound. A unitary between the two complete Hilbert
bases carries this result to nonselfadjoint/non-normal operators.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every explicitly given positive real complete eigenbasis whose
eigenvalues are summable computes the true infimum over ALL rank-one
representations, not just a witnessing decomposition's mass. -/
theorem realPositiveEigenSummable_exact_nuclearInfimum
    (A : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 ≤ sigma n)
    (hs : Summable sigma)
    (heig : ∀ n, A (b n) = sigma n • b n) :
    realNuclearInfimum A = ∑' n : ℕ, sigma n := by
  have hseries :
      A = ∑' n : ℕ, sigma n • rankOne ℝ (b n) (b n) :=
    realPositiveEigenSummable_operator_tsum_eq A b sigma hpos hs heig
  have hterm (n : ℕ) :
      ‖sigma n‖ * ‖b n‖ * ‖b n‖ = sigma n := by
    rw [b.orthonormal.norm_eq_one n, Real.norm_eq_abs,
      abs_of_nonneg (hpos n)]
    ring
  have hcost : Summable (fun n : ℕ =>
      ‖sigma n‖ * ‖b n‖ * ‖b n‖) :=
    hs.congr (fun n => (hterm n).symm)
  have hmem : (∑' n : ℕ, sigma n) ∈ RealNuclearCosts A := by
    refine ⟨b, b, sigma, hcost, hseries, ?_⟩
    exact (tsum_congr hterm).symm
  have hupper : realNuclearInfimum A ≤ ∑' n : ℕ, sigma n :=
    realNuclearInfimum_le_cost A hmem
  have hlower (c : ℝ) (hc : c ∈ RealNuclearCosts A) :
      (∑' n : ℕ, sigma n) ≤ c := by
    have hfinite (N : ℕ) :
        (∑ n ∈ Finset.range N, sigma n) ≤ c := by
      have hh := realHilbertFiniteTrace_abs_le_nuclearCost b N A hc
      have hd (n : ℕ) :
          inner ℝ (b n) (A (b n)) = sigma n := by
        rw [heig n, real_inner_smul_right,
          real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one n]
        ring
      have hsum :
          (∑ n ∈ Finset.range N, inner ℝ (b n) (A (b n))) =
          ∑ n ∈ Finset.range N, sigma n :=
        Finset.sum_congr rfl (fun n _ => hd n)
      rw [hsum] at hh
      have hp : 0 ≤ ∑ n ∈ Finset.range N, sigma n :=
        Finset.sum_nonneg (fun n _ => hpos n)
      simpa only [abs_of_nonneg hp] using hh
    exact le_of_tendsto hs.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hfinite)
  exact le_antisymm hupper
    (le_csInf ⟨∑' n : ℕ, sigma n, hmem⟩ hlower)

/-- For arbitrary TWO supplied complete real singular Hilbert bases,
the actual (possibly NONSELFADJOINT) operator's universal projective
nuclear norm is EXACTLY the sum of the supplied singular weights. -/
theorem realTwoBasisSummableSingular_exact_nuclearInfimum
    (T : H →L[ℝ] H) (b c : HilbertBasis ℕ ℝ H)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 ≤ sigma n)
    (hs : Summable sigma)
    (heig : ∀ n, T (b n) = sigma n • c n) :
    realNuclearInfimum T = ∑' n : ℕ, sigma n := by
  let U : H ≃ₗᵢ[ℝ] H := b.repr.trans c.repr.symm
  have hmap (n : ℕ) : U (b n) = c n := by
    change c.repr.symm (b.repr (b n)) = c n
    rw [b.repr_self, c.repr_symm_single]
  let A : H →L[ℝ] H := realUnitaryLeftCLM U.symm T
  have hAeig (n : ℕ) : A (b n) = sigma n • b n := by
    change U.symm (T (b n)) = sigma n • b n
    rw [heig n, map_smul, ← hmap n, U.symm_apply_apply]
  have hTA : T = realUnitaryLeftCLM U A := by
    have h := realUnitaryLeftCLM_symm_comp U.symm T
    simpa only [A, LinearIsometryEquiv.symm_symm] using h.symm
  calc
    realNuclearInfimum T =
        realNuclearInfimum A := by
      rw [hTA]
      exact realNuclearInfimum_unitary_left_eq U A
    _ = ∑' n : ℕ, sigma n :=
      realPositiveEigenSummable_exact_nuclearInfimum
        A b sigma hpos hs hAeig

/-- Norm invariance across all possible real full two-sided SVD
presentations: every given witness yields its own EXACT trace sum. -/
theorem HasRealSummableSingularHilbertBases.exists_exact_given_basis_sum
    {T : H →L[ℝ] H}
    (hT : HasRealSummableSingularHilbertBases T) :
    ∃ (b c : HilbertBasis ℕ ℝ H) (sigma : ℕ → ℝ),
      (∀ n, 0 ≤ sigma n) ∧ Summable sigma ∧
      (∀ n, T (b n) = sigma n • c n) ∧
      realNuclearInfimum T = ∑' n : ℕ, sigma n := by
  obtain ⟨b, c, sigma, hpos, hs, heig⟩ := hT
  exact ⟨b, c, sigma, hpos, hs, heig,
    realTwoBasisSummableSingular_exact_nuclearInfimum
      T b c sigma hpos hs heig⟩

#print axioms GegenbauerFock.Ultraspherical.realPositiveEigenSummable_exact_nuclearInfimum
#print axioms GegenbauerFock.Ultraspherical.realTwoBasisSummableSingular_exact_nuclearInfimum
#print axioms GegenbauerFock.Ultraspherical.HasRealSummableSingularHilbertBases.exists_exact_given_basis_sum

end GegenbauerFock.Ultraspherical
