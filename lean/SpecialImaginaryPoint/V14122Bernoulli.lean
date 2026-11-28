import Mathlib
open Filter Topology
noncomputable section
namespace Manuscript14V14122Bernoulli

/-- The convention in v14.122 is Mathlib's positive-B1 convention. -/
theorem convention : bernoulli' 0 = 1 ∧ bernoulli' 1 = 1 / 2 :=
  ⟨bernoulli'_zero, bernoulli'_one⟩

theorem polynomial_one (t : ℚ) :
    (Polynomial.bernoulli 1).eval t =
      bernoulli' 0 * (t - 1) + bernoulli' 1 := by
  rw [Polynomial.bernoulli_one, bernoulli'_zero, bernoulli'_one]
  simp
  ring

theorem polynomial_endpoint :
    (Polynomial.bernoulli 1).eval 1 = bernoulli' 1 :=
  Polynomial.bernoulli_eval_one 1

/-- Removable value at zero; elsewhere use the actual Riemann zeta. -/
def bernoulliFunction (s : ℂ) : ℂ :=
  if s = 0 then 1 else -s * riemannZeta (1 - s)

theorem function_zero : bernoulliFunction 0 = 1 := by simp [bernoulliFunction]

theorem function_one : bernoulliFunction 1 = (1 : ℂ) / 2 := by
  norm_num [bernoulliFunction, riemannZeta_zero]

theorem interpolation (k : ℕ) :
    bernoulliFunction ((k : ℂ) + 1) = (bernoulli' (k + 1) : ℂ) := by
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [bernoulliFunction, if_neg hk, show (1 : ℂ) - ((k : ℂ) + 1) = -(k : ℂ) by ring,
    riemannZeta_neg_nat_eq_bernoulli']
  push_cast
  field_simp [hk] <;> ring

/-- The quartic uses the actual two Mathlib Bernoulli numbers. -/
theorem quartic (x : ℚ) :
    x^4 - x^2 / 2 + 1 / 32 =
      bernoulli' 0 * x^4 - bernoulli' 1 * (x^2 - (bernoulli' 1)^4) := by
  rw [bernoulli'_zero, bernoulli'_one]
  ring

/-- Discriminant formula evaluated on the prescribed scaled quartic. -/
theorem discriminant_family (s A C : ℝ)
    (hA : A = -(s^2 / 2)) (hC : C = s^4 / 32) :
    16*C*(4*C-A^2)^2 = s^12 / 128 := by
  rw [hA,hC]
  ring

theorem discriminant_monic : (16:ℚ)*(1/32)*(4*(1/32)-(1/2)^2)^2 = 1/128 := by
  norm_num

/-- Actual removable limit, using the established zeta residue at one. -/
theorem removable_limit :
    Tendsto bernoulliFunction (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
  have hcont : ContinuousAt (fun s : ℂ => 1-s) 0 :=
    (continuous_const.sub continuous_id).continuousAt
  have hmap : Tendsto (fun s : ℂ => 1-s) (𝓝[≠] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : s ≠ 0 := hs
      change 1-s ≠ 1
      intro he
      apply hs0
      linear_combination -he
  refine (riemannZeta_residue_one.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  simp only [Function.comp_def, bernoulliFunction, if_neg hs0]
  congr 1
  ring

#print axioms removable_limit
#print axioms convention
#print axioms polynomial_one
#print axioms polynomial_endpoint
#print axioms function_zero
#print axioms function_one
#print axioms interpolation
#print axioms quartic
#print axioms discriminant_family
#print axioms discriminant_monic
end Manuscript14V14122Bernoulli
