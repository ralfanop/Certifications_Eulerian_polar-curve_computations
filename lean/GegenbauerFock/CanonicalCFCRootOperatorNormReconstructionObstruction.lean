import GegenbauerFock.CanonicalCFCQuantitativePolarInstability
import Mathlib.Topology.Order.OrderClosed

/-!
# V007 — sharp uniform reconstruction obstruction for CFC, Fock and Gram

For a bounded transform T with a normalized approximate-null sequence,
any bounded linear reconstruction R has operator-norm error at least one:
‖id - R ∘ T‖ ≥ 1.

This is a genuinely uniform statement, stronger than failure of a
continuous exact inverse. It applies separately to the canonical positive
CFC Gram root, the genuine Gegenbauer--Fock analysis map, and the source
Gram. It does not preclude strong (pointwise) regularized convergence.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A normalized approximate-null sequence prevents any bounded
reconstruction from uniformly approximating the identity with
operator-norm error smaller than one. The bound is sharp because
the zero reconstruction has error one on a nonzero source. -/
theorem opNorm_id_sub_reconstruction_ge_one_of_unit_null
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : H →L[ℂ] K)
    (u : ℕ → H)
    (hunit : ∀ n : ℕ, ‖u n‖ = 1)
    (hzero : Filter.Tendsto (fun n : ℕ => T (u n))
      Filter.atTop (nhds (0 : K)))
    (R : K →L[ℂ] H) :
    (1 : ℝ) ≤ ‖(ContinuousLinearMap.id ℂ H) - R.comp T‖ := by
  let E : H →L[ℂ] H := (ContinuousLinearMap.id ℂ H) - R.comp T
  have hR : Filter.Tendsto (fun n : ℕ => R (T (u n)))
      Filter.atTop (nhds (0 : H)) := by
    have h := R.continuous.continuousAt.tendsto.comp hzero
    simpa only [map_zero] using h
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ‖E‖ + ‖R (T (u n))‖)
      Filter.atTop (nhds ‖E‖) := by
    simpa using (tendsto_const_nhds.add hR.norm)
  have hbound (n : ℕ) :
      (1 : ℝ) ≤ ‖E‖ + ‖R (T (u n))‖ := by
    have hid : E (u n) + R (T (u n)) = u n := by
      dsimp [E]
      simp
    have htri := norm_add_le (E (u n)) (R (T (u n)))
    rw [hid] at htri
    have hlin := E.le_opNorm (u n)
    calc
      (1 : ℝ) = ‖u n‖ := (hunit n).symm
      _ ≤ ‖E (u n)‖ + ‖R (T (u n))‖ := htri
      _ ≤ ‖E‖ * ‖u n‖ + ‖R (T (u n))‖ :=
        add_le_add_right hlin _
      _ = ‖E‖ + ‖R (T (u n))‖ := by rw [hunit n]; ring
  exact ge_of_tendsto' hnorm hbound

/-- For all positive ultraspherical and Gaussian parameters, no
bounded linear reconstruction of the genuine CFC root, Fock transform
or source Gram can have uniform operator-norm error smaller than one. -/
theorem cfc_fock_gram_uniform_reconstruction_error_ge_one
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∀ (R : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)),
      (1 : ℝ) ≤ ‖(ContinuousLinearMap.id ℂ
          (Lp ℂ 2 (Ultraspherical.measure lam))) -
        R.comp (localCFCGramSqrt lam alpha hlam ha)‖) ∧
    (∀ (R : InfiniteAnalysis.FockCoefficients →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)),
      (1 : ℝ) ≤ ‖(ContinuousLinearMap.id ℂ
          (Lp ℂ 2 (Ultraspherical.measure lam))) -
        R.comp (C lam alpha hlam ha)‖) ∧
    (∀ (R : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)),
      (1 : ℝ) ≤ ‖(ContinuousLinearMap.id ℂ
          (Lp ℂ 2 (Ultraspherical.measure lam))) -
        R.comp (gram lam alpha hlam ha)‖) := by
  obtain ⟨u, hunit, hP, hC, hG⟩ :=
    exists_shared_cfc_fock_gram_strong_null_sequence lam alpha hlam ha
  refine ⟨?_, ?_, ?_⟩
  · intro R
    exact opNorm_id_sub_reconstruction_ge_one_of_unit_null
      (localCFCGramSqrt lam alpha hlam ha) u hunit hP R
  · intro R
    exact opNorm_id_sub_reconstruction_ge_one_of_unit_null
      (C lam alpha hlam ha) u hunit hC R
  · intro R
    exact opNorm_id_sub_reconstruction_ge_one_of_unit_null
      (gram lam alpha hlam ha) u hunit hG R

#print axioms GegenbauerFock.GeneralUltrasphericalFock.opNorm_id_sub_reconstruction_ge_one_of_unit_null
#print axioms GegenbauerFock.GeneralUltrasphericalFock.cfc_fock_gram_uniform_reconstruction_error_ge_one

end GegenbauerFock.GeneralUltrasphericalFock
