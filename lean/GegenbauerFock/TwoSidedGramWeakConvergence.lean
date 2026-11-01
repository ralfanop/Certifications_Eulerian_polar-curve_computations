import GegenbauerFock.TwoSidedGramWeakOnDenseRange
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# V007 — genuine weak convergence to zero for both Gram Weyl sequences

Each actual Gram G=C†C or H=CC† has a sequence of UNIT vectors with
Gram images converging to zero in Hilbert norm. Both actual Gram ranges
are dense. Earlier kernel-certified results show inner products with
every range vector tend to zero.

This file extends the limit to EVERY test vector in the corresponding
Hilbert space using the uniform unit norm and Cauchy–Schwarz.
This is the full sequential definition of weak convergence, not merely
a dense set of test vectors. The two Hilbert spaces are not identified.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Dense-range test convergence plus a unit-vector bound upgrades
pointwise convergence of all Gram-range inner products to EVERY Hilbert
vector, i.e. weak convergence to zero. -/
private theorem weak_zero_of_unit_and_dense_range_tests
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (hdense : T.range.topologicalClosure = (⊤ : Submodule ℂ H))
    (u : ℕ → H)
    (hunit : ∀ n : ℕ, ‖u n‖ = 1)
    (hrange : ∀ y : H,
      Tendsto (fun n : ℕ => inner ℂ (T y) (u n))
        atTop (nhds (0 : ℂ)))
    (x : H) :
    Tendsto (fun n : ℕ => inner ℂ x (u n))
      atTop (nhds (0 : ℂ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hmem : x ∈ closure (T.range : Set H) := by
    rw [← Submodule.topologicalClosure_coe, hdense]
    trivial
  obtain ⟨y, hy, hxy⟩ :=
    (Metric.mem_closure_iff.mp hmem) (ε / 2) hhalf
  obtain ⟨z, rfl⟩ := hy
  have hclose : ‖x - T z‖ < ε / 2 := by
    simpa [dist_eq_norm] using hxy
  obtain ⟨N, hsmall⟩ :=
    (Metric.tendsto_atTop.mp (hrange z)) (ε / 2) hhalf
  refine ⟨N, ?_⟩
  intro n hnN
  have hn := hsmall n hnN
  rw [dist_zero_right] at hn ⊢
  have hdecomp : x = (x - T z) + T z := by abel
  calc
    ‖inner ℂ x (u n)‖ =
        ‖inner ℂ ((x - T z) + T z) (u n)‖ := by rw [← hdecomp]
    _ = ‖inner ℂ (x - T z) (u n) +
          inner ℂ (T z) (u n)‖ := by rw [inner_add_left]
    _ ≤ ‖inner ℂ (x - T z) (u n)‖ +
          ‖inner ℂ (T z) (u n)‖ := norm_add_le _ _
    _ ≤ ‖x - T z‖ * ‖u n‖ +
          ‖inner ℂ (T z) (u n)‖ :=
        add_le_add (norm_inner_le_norm _ _) le_rfl
    _ = ‖x - T z‖ + ‖inner ℂ (T z) (u n)‖ := by rw [hunit n, mul_one]
    _ < ε / 2 + ε / 2 := add_lt_add hclose hn
    _ = ε := by ring

/-- A normalized approximate-zero sequence for the source Gram C†C
converges WEAKLY to zero: all complex inner products, not just tests
on the dense Gram range, tend to zero. -/
theorem sourceGram_unit_approximate_zero_weakly_null
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ x : Lp ℂ 2 (Ultraspherical.measure lam),
        Tendsto (fun n : ℕ => inner ℂ x (u n))
          atTop (nhds (0 : ℂ))) := by
  obtain ⟨u, hunit, himage, hrange⟩ :=
    sourceGram_approx_zero_weak_on_dense_range lam alpha hlam ha
  refine ⟨u, hunit, himage, ?_⟩
  intro x
  exact weak_zero_of_unit_and_dense_range_tests
    (gram lam alpha hlam ha) (gram_dense_range lam alpha hlam ha)
    u hunit hrange x

/-- A normalized approximate-zero sequence for the output Gram CC†
converges WEAKLY to zero in the whole Fock coefficient Hilbert space. -/
theorem outputGram_unit_approximate_zero_weakly_null
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ Y : InfiniteAnalysis.FockCoefficients,
        Tendsto (fun n : ℕ => inner ℂ Y (v n))
          atTop (nhds (0 : ℂ))) := by
  obtain ⟨v, hunit, himage, hrange⟩ :=
    outputGram_approx_zero_weak_on_dense_range lam alpha hlam ha
  refine ⟨v, hunit, himage, ?_⟩
  intro Y
  exact weak_zero_of_unit_and_dense_range_tests
    (outputGram lam alpha hlam ha) (outputGram_dense_range lam alpha hlam ha)
    v hunit hrange Y

/-- Both actual compact Grams have normalized approximate-zero
sequences weakly tending to zero in their distinct Hilbert spaces. -/
theorem two_sided_gram_unit_approximate_zero_weakly_null
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ x : Lp ℂ 2 (Ultraspherical.measure lam),
        Tendsto (fun n : ℕ => inner ℂ x (u n))
          atTop (nhds (0 : ℂ)))) ∧
    (∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ Y : InfiniteAnalysis.FockCoefficients,
        Tendsto (fun n : ℕ => inner ℂ Y (v n))
          atTop (nhds (0 : ℂ)))) :=
  ⟨sourceGram_unit_approximate_zero_weakly_null lam alpha hlam ha,
   outputGram_unit_approximate_zero_weakly_null lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_unit_approximate_zero_weakly_null
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_unit_approximate_zero_weakly_null
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_unit_approximate_zero_weakly_null

end GegenbauerFock.GeneralUltrasphericalFock
