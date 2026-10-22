import V033PolynomialJets
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Polynomial

noncomputable section
namespace V033
open Polynomial Filter
open scoped Topology

theorem polynomial_second_order (p : ℝ[X]) (h0 : p.coeff 0=0) (h1 : p.coeff 1=0) :
    p = p.divX.divX * X^2 := by
  have h := divX_mul_X_add p
  have hh := divX_mul_X_add p.divX
  simp only [h0, coeff_divX, Nat.zero_add, h1, map_zero, add_zero] at h hh
  calc
    p = p.divX * X := h.symm
    _ = (p.divX.divX * X) * X := by rw [hh]
    _ = p.divX.divX * X^2 := by ring

/-- A finite algebraic identity, with no asymptotic hypothesis on its remainder. -/
theorem rational_second_order (P Q : ℝ[X]) (a b : ℝ)
    (h0 : P.coeff 0 = a*Q.coeff 0)
    (h1 : P.coeff 1 = b*Q.coeff 0+a*Q.coeff 1) :
    ∃ R : ℝ[X], ∀ t : ℝ, Q.eval t ≠ 0 →
      P.eval t / Q.eval t - (a+b*t) = t^2 * (R.eval t / Q.eval t) := by
  let N := P - (C a + C b * X)*Q
  have hn0 : N.coeff 0 = 0 := by
    dsimp [N]
    rw [coeff_zero_eq_eval_zero]
    simp only [eval_sub, eval_mul, eval_add,
      eval_C, eval_X, mul_zero, add_zero]
    rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, h0, sub_self]
  have hn1 : N.coeff 1 = 0 := by
    dsimp [N]
    rw [coeff_sub, Jet.mul_coeff_one]
    simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X, if_false,
      if_true, zero_ne_one, one_ne_zero, mul_zero, mul_one, zero_add, add_zero]
    rw [h1]
    ring
  refine ⟨N.divX.divX, ?_⟩
  intro t ht
  have he := congrArg (Polynomial.eval t) (polynomial_second_order N hn0 hn1)
  simp only [N, eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_pow] at he
  field_simp
  nlinarith [he]

/-- Quantitative fixed-degree remainder. The nonvanishing denominator and the
bound are established, rather than left as hypotheses on unspecified errors. -/
theorem rational_remainder_bound (P Q : ℝ[X]) (a b : ℝ)
    (hq : Q.coeff 0 ≠ 0)
    (h0 : P.coeff 0 = a*Q.coeff 0)
    (h1 : P.coeff 1 = b*Q.coeff 0+a*Q.coeff 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      Q.eval (1/(M:ℝ)) ≠ 0 ∧
      |P.eval (1/(M:ℝ))/Q.eval (1/(M:ℝ)) - (a+b/(M:ℝ))| ≤ C/(M:ℝ)^2 := by
  obtain ⟨R,hr⟩ := rational_second_order P Q a b h0 h1
  have hq0 : Q.eval 0 ≠ 0 := by simpa [coeff_zero_eq_eval_zero] using hq
  have hcont : ContinuousAt (fun t : ℝ => R.eval t / Q.eval t) 0 :=
    R.continuous.continuousAt.div Q.continuous.continuousAt hq0
  have hl := hcont.tendsto.comp tendsto_one_div_atTop_nhds_zero_nat
  have hb : ∀ᶠ M : ℕ in atTop,
      |R.eval (1/(M:ℝ))/Q.eval (1/(M:ℝ))| < |R.eval 0/Q.eval 0|+1 :=
    hl.abs.eventually (gt_mem_nhds (lt_add_one _))
  have hd : ∀ᶠ M : ℕ in atTop, Q.eval (1/(M:ℝ)) ≠ 0 :=
    (Q.continuous.continuousAt.tendsto.comp tendsto_one_div_atTop_nhds_zero_nat).eventually
      (eventually_ne_nhds hq0)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 (hb.and hd)
  refine ⟨|R.eval 0/Q.eval 0|+1, by positivity, N, ?_⟩
  intro M hM
  obtain ⟨hbound,hden⟩ := hN M hM
  refine ⟨hden, ?_⟩
  rw [show a+b/(M:ℝ) = a+b*(1/(M:ℝ)) by ring, hr _ hden, abs_mul,
    abs_of_nonneg (sq_nonneg _)]
  calc
    (1/(M:ℝ))^2 * |R.eval (1/(M:ℝ))/Q.eval (1/(M:ℝ))| ≤
        (1/(M:ℝ))^2 * (|R.eval 0/Q.eval 0|+1) :=
      mul_le_mul_of_nonneg_left hbound.le (sq_nonneg _)
    _ = (|R.eval 0/Q.eval 0|+1)/(M:ℝ)^2 := by ring

#print axioms rational_second_order
#print axioms rational_remainder_bound
end V033
