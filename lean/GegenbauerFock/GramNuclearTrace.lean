import GegenbauerFock.GramIntegralComplete
import GegenbauerFock.GramKernelSeries
import GegenbauerFock.RowEnergyExpIntegral
import GegenbauerFock.UltrasphericalKummerBridge

/-!
# V007: operator-norm summable nuclear Gram decomposition

A trace-class positive Gram operator can be presented as an absolutely
operator-norm-summable series of positive rank-one terms. The row
functionals are the genuine ultraspherical Fourier moments. This
module certifies absolute convergence of the rank-one operators,
not just convergence after applying to a fixed L² vector.

Note: identifying this constructive nuclear presentation with a
separately bundled Schatten S₁ API is a further formal bridge.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Each rank-one positive Gram summand of the genuine operator. -/
noncomputable def gramNuclearTerm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let r := WeightedMoments.coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n
  exact r.adjoint.comp r

/-- Operator-norm bound for each concrete positive rank-one term. -/
theorem gramNuclearTerm_norm_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    ‖gramNuclearTerm lam alpha hlam ha n‖ ≤
      WeightedMoments.squareWeight alpha n := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let r := WeightedMoments.coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n
  change ‖r.adjoint.comp r‖ ≤ _
  calc
    ‖r.adjoint.comp r‖ = ‖r‖ ^ 2 := by
      rw [ContinuousLinearMap.norm_adjoint_comp_self]
      ring
    _ ≤ WeightedMoments.squareWeight alpha n :=
      WeightedMoments.coefficient_norm_sq_le
        (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha n

/-- The *actual* infinite family of positive rank-one Gram pieces
is absolutely summable in the full Banach operator norm. -/
theorem gramNuclearTerm_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Summable (gramNuclearTerm lam alpha hlam ha) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (gramNuclearTerm_norm_le lam alpha hlam ha)
    (WeightedMoments.squareWeight_summable alpha)

/-- Exact identity of the Gram map with the infinite positive
rank-one sum, now as an equality of *bounded operators*, not merely
as separate convergent vectors. -/
theorem gram_eq_nuclear_tsum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    gram lam alpha hlam ha =
      ∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n := by
  apply ContinuousLinearMap.ext
  intro f
  rw [gram_eq_tsum_rows lam alpha hlam ha f]
  have hs := gramNuclearTerm_summable lam alpha hlam ha
  have heval :
      (∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n) f =
        ∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n f := by
    exact (ContinuousLinearMap.apply ℂ
      (Lp ℂ 2 (Ultraspherical.measure lam)) f).map_tsum hs
  rw [heval]
  apply tsum_congr
  intro n
  rfl

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearTerm_norm_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearTerm_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_eq_nuclear_tsum

/-- Rank-one positivity makes the operator norm of the n-th Gram
summand equal to the exact squared norm of the n-th Fock moment row. -/
theorem gramNuclearTerm_norm_eq_row_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    ‖gramNuclearTerm lam alpha hlam ha n‖ =
      ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let r := WeightedMoments.coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n
  change ‖r.adjoint.comp r‖ = _
  rw [C_row_eq lam alpha hlam ha n]
  change ‖r.adjoint.comp r‖ = ‖r‖ ^ 2
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  ring

/-- The mass of the positive nuclear rank-one presentation is
exactly the verified squared canonical Hilbert-Schmidt row energy. -/
theorem gramNuclearMass_eq_rowEnergy
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      rowEnergy lam alpha hlam ha := by
  unfold rowEnergy
  apply tsum_congr
  intro n
  exact gramNuclearTerm_norm_eq_row_sq lam alpha hlam ha n

/-- Exact exponential integral for the nuclear Gram mass. This is
the scalar trace of the positive rank-one presentation, independent
trace-class ideal equivalence still being formalized. -/
theorem gramNuclearMass_eq_exp_integral
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      ∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
        ∂(Ultraspherical.measure lam) := by
  rw [gramNuclearMass_eq_rowEnergy]
  exact rowEnergy_eq_exp_integral lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearTerm_norm_eq_row_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_rowEnergy
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_exp_integral


/-- Unconditional Kummer closed form for the absolute rank-one
nuclear mass of the concrete positive Gram operator C†C. The
summands are actual norm-one-rank Hilbert operators, not merely
formal coefficients. -/
theorem gramNuclearMass_eq_kummerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [gramNuclearMass_eq_rowEnergy]
  exact rowEnergy_eq_kummerSeries lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_kummerSeries

/-- The nuclear mass of the concrete positive Gram presentation has
the exact unregularized Mathlib-Pochhammer Kummer series, with
physical parameter t = 1/(4α). -/
theorem gramNuclearMass_eq_pochhammerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      ∑' n : ℕ,
        ((Polynomial.ascPochhammer ℝ n).eval (1 / 2) /
          (Polynomial.ascPochhammer ℝ n).eval (lam + 1)) *
          ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) := by
  rw [gramNuclearMass_eq_rowEnergy]
  exact rowEnergy_eq_pochhammerSeries lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_pochhammerSeries

end GegenbauerFock.GeneralUltrasphericalFock
