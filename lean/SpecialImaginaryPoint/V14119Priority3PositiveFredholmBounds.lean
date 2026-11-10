import SpecialImaginaryPoint.V14119Priority3FredholmSectorFunctional

/-!
# Manuscript 14.119 Priority 3 — quantitative positive-sector Fredholm bounds

For ANY summable nonnegative real diagonal data, the finite determinants
of genuine Hilbert-space compressions are bounded between one and the
exponential of their finite spectral trace. Passing to the actual
infinite Fredholm product gives a uniform operatorial estimate in terms
of the genuine CFC-absolute Schatten-S₁ trace norm.

These are positive-diagonal-sector theorems, NOT construction or
trace-norm continuity of the universal determinant on all S₁ operators.
There is no relative zeta-regularization claim.
-/

noncomputable section

namespace Manuscript14Priority3.PositiveDiagonalFredholm
open Filter Topology
open Manuscript14Priority3.TraceClassModel

/-- Every positive-shift finite real compressed determinant is at
least one, for arbitrary nonnegative summable diagonal data. -/
theorem finiteRealShift_ge_one (D : Data) (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) : 1 ≤ finiteRealShift D N t := by
  unfold finiteRealShift
  apply Finset.one_le_prod₀
  intro n hn
  have h := mul_nonneg ht (D.nonneg n)
  linarith

/-- The determinant of each true finite Hilbert compression is
bounded by the exponential of its actual finite trace. -/
theorem finiteRealShift_le_exp_sum (D : Data) (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) :
    finiteRealShift D N t ≤
      Real.exp (∑ n ∈ Finset.range N, t * D.coeff n) := by
  calc
    finiteRealShift D N t =
        ∏ n ∈ Finset.range N, (1 + t * D.coeff n) := rfl
    _ ≤ ∏ n ∈ Finset.range N, Real.exp (t * D.coeff n) := by
      apply Finset.prod_le_prod₀
      · intro n hn
        have h := mul_nonneg ht (D.nonneg n)
        linarith
      · intro n hn
        linarith [Real.add_one_le_exp (t * D.coeff n)]
    _ = Real.exp (∑ n ∈ Finset.range N, t * D.coeff n) := by
      rw [Real.exp_sum]

/-- Infinite positive diagonal Fredholm product is at least one. -/
theorem determinant_ge_one (D : Data) (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ determinant D t := by
  have hlim : Tendsto (fun N : ℕ => finiteRealShift D N t)
      atTop (𝓝 (determinant D t)) := by
    simpa only [finiteRealShift, determinant] using
      ((multipliable_factor D t).hasProd_iff_tendsto_nat).mp
        (multipliable_factor D t).hasProd
  exact ge_of_tendsto hlim
    (Filter.Eventually.of_forall (fun N => finiteRealShift_ge_one D N t ht))

/-- The infinite operatorial positive-sector determinant is bounded by
exp(t times the genuine S₁ spectral mass), for nonnegative real shift. -/
theorem determinant_le_exp_mass (D : Data) (t : ℝ) (ht : 0 ≤ t) :
    determinant D t ≤ Real.exp (t * ∑' n : ℕ, D.coeff n) := by
  have hprod : Tendsto (fun N : ℕ => finiteRealShift D N t)
      atTop (𝓝 (determinant D t)) := by
    simpa only [finiteRealShift, determinant] using
      ((multipliable_factor D t).hasProd_iff_tendsto_nat).mp
        (multipliable_factor D t).hasProd
  have hsum :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, t * D.coeff n)
        atTop (𝓝 (t * ∑' n : ℕ, D.coeff n)) := by
    simpa only [tsum_mul_left] using
      (D.summable.mul_left t).hasSum.tendsto_sum_nat
  have hexp :
      Tendsto
        (fun N : ℕ => Real.exp (∑ n ∈ Finset.range N, t * D.coeff n))
        atTop (𝓝 (Real.exp (t * ∑' n : ℕ, D.coeff n))) :=
    (Real.continuous_exp.tendsto _).comp hsum
  exact le_of_tendsto_of_tendsto hprod hexp
    (Filter.Eventually.of_forall
      (fun N => finiteRealShift_le_exp_sum D N t ht))

/-- The sector determinant as a genuine function of the S₁ OPERATOR
is bounded below by one. No arbitrary diagonal witness is exposed. -/
theorem determinantOnSector_ge_one (T : sector) (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ determinantOnSector T t := by
  let D : Data := Classical.choose T.property
  have hD : S1Diagonal D = T.val := Classical.choose_spec T.property
  rw [determinantOnSector_eq T D hD t]
  exact determinant_ge_one D t ht

/-- Quantitative Fredholm growth bound expressed using the *actual*
basis-independent CFC Schatten-S₁ trace norm of the sector operator. -/
theorem determinantOnSector_le_exp_traceNorm
    (T : sector) (t : ℝ) (ht : 0 ≤ t) :
    determinantOnSector T t ≤
      Real.exp (t * ProbabilisticTheory.TraceClass.traceNorm H T.val) := by
  let D : Data := Classical.choose T.property
  have hD : S1Diagonal D = T.val := Classical.choose_spec T.property
  have hnorm :
      ProbabilisticTheory.TraceClass.traceNorm H T.val =
        ∑' n : ℕ, D.coeff n := by
    rw [← hD]
    exact S1Diagonal_traceNorm_eq D
  rw [determinantOnSector_eq T D hD t, hnorm]
  exact determinant_le_exp_mass D t ht

#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.finiteRealShift_ge_one
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.finiteRealShift_le_exp_sum
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinant_ge_one
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinant_le_exp_mass
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinantOnSector_ge_one
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinantOnSector_le_exp_traceNorm

end Manuscript14Priority3.PositiveDiagonalFredholm
