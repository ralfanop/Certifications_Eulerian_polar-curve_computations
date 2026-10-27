import GegenbauerFock.HSRightIdeal
import GegenbauerFock.ConcreteFockRowEnergy

/-!
# V007: input-Hilbert-basis invariance of concrete Fock coordinate energy

For the *actual* ultraspherical transform, Parseval holds for each
output coordinate against an arbitrary complete orthonormal Hilbert
basis of the source L² space. Finite sums of output-coordinate energies
are therefore independent of the chosen source Hilbert basis.

The exchange of the two infinite basis sums, and the identification
with a separately bundled Schatten S₂ ideal norm, remain separate
obligations. No finite-dimensionality assumption is made.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For every source Hilbert basis (possibly infinite and not countably
enumerated), the squared energy of the n-th genuine Fock row is exactly
the sum of its values on the source basis. -/
theorem C_row_any_basis_parseval
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (n : ℕ) :
    (∑' i : ι, ‖C lam alpha hlam ha (b i) n‖ ^ 2) =
      ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  calc
    (∑' i : ι, ‖C lam alpha hlam ha (b i) n‖ ^ 2) =
        ∑' i : ι,
          ‖WeightedMoments.coefficient
            (Ultraspherical.measure lam) (ae_abs_le_one lam)
            alpha n (b i)‖ ^ 2 := by
          apply tsum_congr
          intro i
          rw [C_coefficient lam alpha hlam ha (b i) n]
    _ = ‖WeightedMoments.coefficient
          (Ultraspherical.measure lam) (ae_abs_le_one lam)
          alpha n‖ ^ 2 :=
        FockEnergy.weightedMoment_row_basis_energy
          (Ultraspherical.measure lam) (ae_abs_le_one lam)
          alpha ha b n
    _ = ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
          rw [C_row_eq lam alpha hlam ha n]

/-- Every finite output truncation has an input-basis-independent
squared Hilbert energy. This is an exact theorem for the concrete C,
not an assumption that the full Schatten ideal has been constructed. -/
theorem C_finite_rows_any_basis_energy
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (s : Finset ℕ) :
    (∑ n ∈ s, ∑' i : ι, ‖C lam alpha hlam ha (b i) n‖ ^ 2) =
      ∑ n ∈ s, ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro n hn
  exact C_row_any_basis_parseval lam alpha hlam ha b n

/-- The double array of actual Gegenbauer--Fock squared coefficients
is absolutely summable for ANY source Hilbert basis. The proof uses
Parseval on each Riesz monomial, and the already verified summability
of the actual canonical Fock rows. -/
private theorem C_double_basis_energy_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    Summable (fun p : ℕ × ι =>
      ‖C lam alpha hlam ha (b p.2) p.1‖ ^ 2) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let f : ℕ × ι → ℝ := fun p =>
    ‖C lam alpha hlam ha (b p.2) p.1‖ ^ 2
  have hinner (n : ℕ) : Summable (fun i : ι => f (n, i)) := by
    let m := WeightedMoments.monomial
      (Ultraspherical.measure lam) (ae_abs_le_one lam) n
    let cw := WeightedMoments.complexWeight alpha n
    have hrepr : Summable (fun i : ι => ‖inner ℂ (b i) m‖ ^ 2) := by
      have h : Summable (fun i : ι => ‖(b.repr m) i‖ ^ 2) :=
        (lp.memℓp (b.repr m)).summable
          (by norm_num : 0 < (2 : ENNReal).toReal)
      simpa only [HilbertBasis.repr_apply_apply] using h
    have hscaled := hrepr.mul_left (‖cw‖ ^ 2)
    have heq (i : ι) :
        ‖C lam alpha hlam ha (b i) n‖ ^ 2 =
          ‖cw‖ ^ 2 * ‖inner ℂ (b i) m‖ ^ 2 := by
      rw [C_coefficient lam alpha hlam ha (b i) n]
      change ‖cw * inner ℂ m (b i)‖ ^ 2 = _
      rw [norm_mul, mul_pow, norm_inner_symm]
    change Summable (fun i : ι =>
      ‖C lam alpha hlam ha (b i) n‖ ^ 2)
    exact hscaled.congr (fun i => (heq i).symm)
  have houter : Summable (fun n : ℕ => ∑' i : ι, f (n, i)) := by
    change Summable (fun n : ℕ =>
      ∑' i : ι, ‖C lam alpha hlam ha (b i) n‖ ^ 2)
    simpa only [C_row_any_basis_parseval lam alpha hlam ha b] using
      (C_rows_summable lam alpha hlam ha)
  change Summable f
  exact (summable_prod_of_nonneg (fun p : ℕ × ι => sq_nonneg _)).2
    ⟨hinner, houter⟩

/-- For an arbitrary complete source Hilbert basis, the *full* sum
of squared norms of the actual C-images converges. -/
theorem C_any_source_basis_energy_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    Summable (fun i : ι => ‖C lam alpha hlam ha (b i)‖ ^ 2) := by
  have hswap : Summable (fun p : ι × ℕ =>
      ‖C lam alpha hlam ha (b p.1) p.2‖ ^ 2) :=
    (C_double_basis_energy_summable lam alpha hlam ha b).prod_symm
  have houter : Summable (fun i : ι =>
      ∑' n : ℕ, ‖C lam alpha hlam ha (b i) n‖ ^ 2) :=
    ((summable_prod_of_nonneg (fun p : ι × ℕ => sq_nonneg _)).1 hswap).2
  apply houter.congr
  intro i
  simpa using (lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal)
    (C lam alpha hlam ha (b i))).symm

/-- True source-basis independence of the *entire* Hilbert--Schmidt
squared energy of the concrete C. No canonical source basis is chosen.
This is a two-infinite-series theorem, not just a finite-row identity.
The separate abstract Schatten ideal packaging is still pending. -/
theorem C_any_source_basis_energy_eq_rowEnergy
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, ‖C lam alpha hlam ha (b i)‖ ^ 2) =
      rowEnergy lam alpha hlam ha := by
  calc
    (∑' i : ι, ‖C lam alpha hlam ha (b i)‖ ^ 2) =
        ∑' i : ι, ∑' n : ℕ,
          ‖C lam alpha hlam ha (b i) n‖ ^ 2 := by
          apply tsum_congr
          intro i
          simpa using (lp.norm_rpow_eq_tsum
            (by norm_num : 0 < (2 : ENNReal).toReal)
            (C lam alpha hlam ha (b i)))
    _ = ∑' n : ℕ, ∑' i : ι,
          ‖C lam alpha hlam ha (b i) n‖ ^ 2 :=
        Summable.tsum_comm
          (C_double_basis_energy_summable lam alpha hlam ha b)
    _ = rowEnergy lam alpha hlam ha := by
          unfold rowEnergy
          apply tsum_congr
          intro n
          exact C_row_any_basis_parseval lam alpha hlam ha b n

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_any_source_basis_energy_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_any_source_basis_energy_eq_rowEnergy

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_row_any_basis_parseval
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_finite_rows_any_basis_energy

end GegenbauerFock.GeneralUltrasphericalFock
