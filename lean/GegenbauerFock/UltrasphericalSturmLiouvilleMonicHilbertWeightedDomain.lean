import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph

/-!
# V007 — EXACT weighted-ℓ² domain of the genuine closed Sturm operator

Let b be the concrete Gegenbauer Hilbert basis of the genuine real
weighted L² Hilbert space. Its Fourier coordinates are in ℓ².
Define the spectral shifted-weight domain by requiring the sequence

    (t+n(n+2λ)) * (b.repr u n)

to be the coordinate sequence of ANOTHER ℓ² vector.

Because the already-certified positive Sturm resolvent R_t is
everywhere defined and has exactly diagonal multiplier
(t+n(n+2λ))⁻¹ in these same actual Hilbert coordinates, its range
is EXACTLY the above weighted-ℓ² domain. Since the canonical
closed polynomial Sturm operator has domain equal to Ran R_t,
this identifies the unbounded differential operator's domain with
the explicit diagonal spectral domain — not just with an extension.

No abstract unproved basis, diagonalization, or core hypotheses.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

private def shiftedEigenweight (lam t : ℝ) (n : ℕ) : ℝ :=
  t + (n : ℝ) * ((n : ℝ) + 2 * lam)

/-- Every positive shifted ultraspherical eigenvalue is nonzero. -/
private theorem shiftedEigenweight_ne_zero
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    shiftedEigenweight lam t n ≠ 0 := by
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsum : 0 ≤ (n : ℝ) + 2 * lam := by positivity
  have hmul : 0 ≤ (n : ℝ) * ((n : ℝ) + 2 * lam) :=
    mul_nonneg hN hsum
  apply ne_of_gt
  dsimp [shiftedEigenweight]
  linarith

/-- The intrinsic positive-shift diagonal domain is specified by
the genuine Gegenbauer Hilbert coefficients in weighted ℓ².
It is not defined by referring to the operator graph. -/
noncomputable def sturmMonicHilbertWeightedDomain
    (lam t : ℝ) (hlam : 0 < lam) : Set (SturmH lam) :=
  {u | ∃ a : lp (fun _ : ℕ => ℝ) 2, ∀ n : ℕ,
     a n = shiftedEigenweight lam t n *
       (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr u n}

/-- The actual closed real ultraspherical Sturm operator has
EXACTLY the explicit spectral domain of weighted Hilbert
coefficient sequences, for every λ>0 and positive shift t>0. -/
theorem sturmRealClosed_domain_eq_monicHilbert_weightedL2
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ((sturmRealPartialOperator lam hlam).closure.domain :
      Set (SturmH lam)) =
      sturmMonicHilbertWeightedDomain lam t hlam := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  rw [sturmRealClosed_domain_eq_full_resolvent_range lam t hlam ht]
  ext u
  change u ∈ Set.range R ↔
    ∃ a : lp (fun _ : ℕ => ℝ) 2, ∀ n : ℕ,
      a n = shiftedEigenweight lam t n * (b.repr u) n
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨b.repr f, ?_⟩
    intro n
    have hcoord :=
      sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
        lam t hlam ht f n
    change (b.repr (R f)) n =
      (shiftedEigenweight lam t n)⁻¹ * (b.repr f) n at hcoord
    rw [hcoord]
    have hd := shiftedEigenweight_ne_zero lam t hlam ht n
    simp only [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  · rintro ⟨a, ha⟩
    refine ⟨b.repr.symm a, ?_⟩
    apply b.repr.injective
    ext n
    have hcoord :=
      sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
        lam t hlam ht (b.repr.symm a) n
    change (b.repr (R (b.repr.symm a))) n =
      (shiftedEigenweight lam t n)⁻¹ *
        (b.repr (b.repr.symm a)) n at hcoord
    rw [hcoord, b.repr.apply_symm_apply, ha n]
    have hd := shiftedEigenweight_ne_zero lam t hlam ht n
    simp only [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_domain_eq_monicHilbert_weightedL2

end GegenbauerFock.Ultraspherical
