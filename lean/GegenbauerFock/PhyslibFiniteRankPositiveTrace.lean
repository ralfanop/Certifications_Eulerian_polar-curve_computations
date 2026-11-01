import GegenbauerFock.PhyslibRankOneTrace
import GegenbauerFock.PhyslibPositiveFiniteFamilyGeneral

/-!
# V007 — finite positive sums of rank-one trace-class Grams

For any finite family of bounded scalar functionals rᵢ on an arbitrary
complete complex Hilbert space, prove genuine CFC-absolute Physlib S₁
membership and the exact trace norm of ∑ rᵢ† rᵢ.

The diagonal sum is equal to ∑ ‖rᵢ‖² on EVERY complete Hilbert basis,
without requiring commutativity, orthogonality, or finite-dimensional H.
This is the positive finite-rank building block for the general ideal;
it does not constitute the unrestricted nonpositive S₁ Banach theory.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite sum of arbitrary positive rank-one Gram endomorphisms. -/
noncomputable def rankOneGramFinite {ι : Type*}
    (s : Finset ι) (r : ι → H →L[ℂ] ℂ) : H →L[ℂ] H :=
  ∑ i ∈ s, GegenbauerFock.HilbertGram.gram (r i)

/-- Positivity does not require the rank-one terms to commute. -/
theorem rankOneGramFinite_nonneg {ι : Type*}
    (s : Finset ι) (r : ι → H →L[ℂ] ℂ) :
    0 ≤ rankOneGramFinite s r := by
  unfold rankOneGramFinite
  exact Finset.sum_nonneg (fun i _ => rankOneGram_nonneg (r i))

private theorem rankOneFinite_re_inner_swap (x y : H) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

/-- Every rank-one Gram has summable diagonal on ANY Hilbert basis,
not only the basis supplied by its trace-class witness. -/
theorem rankOneGram_basisSummable (r : H →L[ℂ] ℂ)
    {κ : Type*} (b : HilbertBasis κ ℂ H) :
    Summable (fun j : κ =>
      (inner ℂ (b j) (GegenbauerFock.HilbertGram.gram r (b j))).re) := by
  have hterm (j : κ) :
      (inner ℂ (b j) (GegenbauerFock.HilbertGram.gram r (b j))).re =
        ‖r (b j)‖ ^ 2 := by
    calc
      (inner ℂ (b j) (GegenbauerFock.HilbertGram.gram r (b j))).re =
        (inner ℂ (GegenbauerFock.HilbertGram.gram r (b j)) (b j)).re :=
          rankOneFinite_re_inner_swap _ _
      _ = ‖r (b j)‖ ^ 2 :=
        (GegenbauerFock.HilbertGram.gram_norm_sq r (b j)).symm
  exact (GegenbauerFock.FockEnergy.functional_basis_energy r b).1.congr
    (fun j => (hterm j).symm)

/-- The finite positive sum is genuinely Physlib CFC trace class on
arbitrary complete complex Hilbert spaces, using one common basis. -/
theorem rankOneGramFinite_isTraceClass {ι : Type*}
    (s : Finset ι) (r : ι → H →L[ℂ] ℂ) :
    IsTraceClass (rankOneGramFinite s r) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  unfold rankOneGramFinite
  exact isTraceClass_finset_sum_of_nonneg_sameBasis
    s (fun i => GegenbauerFock.HilbertGram.gram (r i))
    (fun i => rankOneGram_nonneg (r i)) b
    (fun i => rankOneGram_basisSummable (r i) b)

private theorem rankOneFinite_diagonal_sum {ι : Type*}
    (s : Finset ι) (A : ι → H →L[ℂ] H) (x : H) :
    (inner ℂ x ((∑ i ∈ s, A i) x)).re =
      ∑ i ∈ s, (inner ℂ x (A i x)).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ContinuousLinearMap.add_apply,
        inner_add_right, Complex.add_re, ih]

private theorem rankOneFinite_tsum_sum
    {ι κ : Type*} (s : Finset ι) (f : ι → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    (∑' j : κ, ∑ i ∈ s, f i j) =
      ∑ i ∈ s, ∑' j : κ, f i j := by
  classical
  have hsum (t : Finset ι) :
      Summable (fun j : κ => ∑ i ∈ t, f i j) := by
    induction t using Finset.induction_on with
    | empty =>
        simpa using (summable_zero : Summable (fun _ : κ => (0 : ℝ)))
    | @insert i t hit ih =>
        simpa only [Finset.sum_insert hit] using (hf i).add ih
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hit ih =>
      calc
        (∑' j : κ, ∑ k ∈ insert i s, f k j) =
          ∑' j : κ, (f i j + ∑ k ∈ s, f k j) := by
            simp only [Finset.sum_insert hit]
        _ = (∑' j : κ, f i j) +
              (∑' j : κ, ∑ k ∈ s, f k j) :=
          (hf i).tsum_add (hsum s)
        _ = ∑ k ∈ insert i s, ∑' j : κ, f k j := by
          rw [ih, Finset.sum_insert hit]

/-- For any finite family of scalar Riesz functionals,
the CFC trace norm is EXACTLY the sum of squared functional norms.
This makes finite-rank positive trace independent of basis. -/
theorem rankOneGramFinite_traceNorm_eq {ι : Type*}
    (s : Finset ι) (r : ι → H →L[ℂ] ℂ) :
    traceNorm (rankOneGramFinite s r)
      (rankOneGramFinite_isTraceClass s r) =
        ∑ i ∈ s, ‖r i‖ ^ 2 := by
  let h := rankOneGramFinite_isTraceClass s r
  let b := h.choose_spec.choose
  change traceNorm (rankOneGramFinite s r) h = _
  rw [traceNorm_eq_diagonal_of_nonneg
    (rankOneGramFinite s r) (rankOneGramFinite_nonneg s r) h]
  calc
    (∑' j : h.choose, (inner ℂ (b j)
      (rankOneGramFinite s r (b j))).re) =
        ∑' j : h.choose,
          ∑ i ∈ s, (inner ℂ (b j)
            (GegenbauerFock.HilbertGram.gram (r i) (b j))).re := by
              apply tsum_congr
              intro j
              exact rankOneFinite_diagonal_sum s
                (fun i => GegenbauerFock.HilbertGram.gram (r i)) (b j)
    _ = ∑ i ∈ s,
        ∑' j : h.choose, (inner ℂ (b j)
          (GegenbauerFock.HilbertGram.gram (r i) (b j))).re :=
      rankOneFinite_tsum_sum s
        (fun i j => (inner ℂ (b j)
          (GegenbauerFock.HilbertGram.gram (r i) (b j))).re)
        (fun i => rankOneGram_basisSummable (r i) b)
    _ = ∑ i ∈ s, ‖r i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact rankOneGram_basisTrace_eq (r i) b

#print axioms ProbabilisticTheory.rankOneGramFinite_nonneg
#print axioms ProbabilisticTheory.rankOneGram_basisSummable
#print axioms ProbabilisticTheory.rankOneGramFinite_isTraceClass
#print axioms ProbabilisticTheory.rankOneGramFinite_traceNorm_eq

end ProbabilisticTheory
