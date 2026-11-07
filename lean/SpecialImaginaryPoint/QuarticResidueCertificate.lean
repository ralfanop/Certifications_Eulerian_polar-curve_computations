import Mathlib

/-!
# Manuscript 14, Proposition 8.7: the quartic minimal polynomial of the residue integral

Kernel-checked identities of displays (139)-(147) of manuscript 14, version 14.91 (7 November 2026):

* `quartic_u`, `quartic_v`: `u = (2 + √2)/8` and `v = (2 - √2)/8` are the roots in `x^2` of
  `32 x^4 - 16 x^2 + 1` (display (139));
* `varpi_sq`, `varpi_quartic`: `ϖ = √(2 + √2)/√8 = μ_hex/√8` satisfies `ϖ^2 = u` and (139);
* `varpi'_sq`, `varpi'_quartic`: `ϖ' = 1/(2 μ_hex)` satisfies `ϖ'^2 = v` and (139) (display (140));
* `diff_sq`, `prod_sq`, `a_sq`: `ϖ^2 - ϖ'^2 = √2/4`, `(√2/4)^2 = (2 ϖ ϖ')^2 = 1/8 = a^2` (display (140));
* `ratio_sq`: `u = (1 + √2)^2 v`, so that `ϖ/ϖ' = 1 + √2` (display (146));
* `bender_identity`, `bender_root`: Bender's characteristic polynomial `P(y) = y^4 + (γ^2 - 2) y^2 + 1 - g^2`
  with `s^2 = 4 - 2 γ^2` and `g^2 = 1 - (2 - γ^2)^2/8` satisfies `P(s x) = s^4 (32 x^4 - 16 x^2 + 1)/32`,
  hence vanishes at `s x` for every root `x` of (139) (displays (142)-(145));
* `bender_hermitian`: at `γ = 0`, `s^2 = 4` and `g^2 = 1/2 = |z_0|^2` (display (147)).

The integral in (141), the irreducibility and minimality of (139) and `cot(π/8) = 1 + √2` are certified in
exact and Arb arithmetic by `numerics/arb/manuscript14_evening_additions_arb.py`.
-/

namespace SpecialImaginaryPoint.QuarticResidue

open Real

lemma sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem quartic_u : 32 * ((2 + Real.sqrt 2) / 8) ^ 2 - 16 * ((2 + Real.sqrt 2) / 8) + 1 = 0 := by
  linear_combination (1 / 2 : ℝ) * sqrt2_sq

theorem quartic_v : 32 * ((2 - Real.sqrt 2) / 8) ^ 2 - 16 * ((2 - Real.sqrt 2) / 8) + 1 = 0 := by
  linear_combination (1 / 2 : ℝ) * sqrt2_sq

theorem varpi_sq : (Real.sqrt (2 + Real.sqrt 2) / Real.sqrt 8) ^ 2 = (2 + Real.sqrt 2) / 8 := by
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]

theorem varpi_quartic :
    32 * (Real.sqrt (2 + Real.sqrt 2) / Real.sqrt 8) ^ 4
      - 16 * (Real.sqrt (2 + Real.sqrt 2) / Real.sqrt 8) ^ 2 + 1 = 0 := by
  have h4 : (Real.sqrt (2 + Real.sqrt 2) / Real.sqrt 8) ^ 4
      = ((Real.sqrt (2 + Real.sqrt 2) / Real.sqrt 8) ^ 2) ^ 2 := by ring
  rw [h4, varpi_sq]
  exact quartic_u

theorem varpi'_sq : (1 / (2 * Real.sqrt (2 + Real.sqrt 2))) ^ 2 = (2 - Real.sqrt 2) / 8 := by
  have hpos : (0 : ℝ) < 2 ^ 2 * (2 + Real.sqrt 2) := by positivity
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), div_eq_iff (ne_of_gt hpos)]
  linear_combination (1 / 2 : ℝ) * sqrt2_sq

theorem varpi'_quartic :
    32 * (1 / (2 * Real.sqrt (2 + Real.sqrt 2))) ^ 4
      - 16 * (1 / (2 * Real.sqrt (2 + Real.sqrt 2))) ^ 2 + 1 = 0 := by
  have h4 : (1 / (2 * Real.sqrt (2 + Real.sqrt 2))) ^ 4
      = ((1 / (2 * Real.sqrt (2 + Real.sqrt 2))) ^ 2) ^ 2 := by ring
  rw [h4, varpi'_sq]
  exact quartic_v

theorem diff_sq : (2 + Real.sqrt 2) / 8 - (2 - Real.sqrt 2) / 8 = Real.sqrt 2 / 4 := by ring

theorem a_sq : (1 / Real.sqrt 8) ^ 2 = 1 / 8 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem diff_is_a_sq : (Real.sqrt 2 / 4) ^ 2 = 1 / 8 := by
  linear_combination (1 / 16 : ℝ) * sqrt2_sq

theorem prod_sq : 4 * ((2 + Real.sqrt 2) / 8) * ((2 - Real.sqrt 2) / 8) = 1 / 8 := by
  linear_combination (-1 / 16 : ℝ) * sqrt2_sq

theorem ratio_sq : (2 + Real.sqrt 2) / 8 = (1 + Real.sqrt 2) ^ 2 * ((2 - Real.sqrt 2) / 8) := by
  linear_combination (Real.sqrt 2 / 8) * sqrt2_sq

theorem bender_identity (γ s x : ℝ) (hs : s ^ 2 = 4 - 2 * γ ^ 2) :
    (s * x) ^ 4 + (γ ^ 2 - 2) * (s * x) ^ 2 + 1 - (1 - (2 - γ ^ 2) ^ 2 / 8)
      = s ^ 4 * (32 * x ^ 4 - 16 * x ^ 2 + 1) / 32 := by
  have hγ : γ ^ 2 = (4 - s ^ 2) / 2 := by linarith
  rw [hγ]
  ring

theorem bender_root (γ s x : ℝ) (hs : s ^ 2 = 4 - 2 * γ ^ 2) (hx : 32 * x ^ 4 - 16 * x ^ 2 + 1 = 0) :
    (s * x) ^ 4 + (γ ^ 2 - 2) * (s * x) ^ 2 + 1 - (1 - (2 - γ ^ 2) ^ 2 / 8) = 0 := by
  rw [bender_identity γ s x hs, hx]
  ring

theorem bender_hermitian :
    (4 : ℝ) - 2 * 0 ^ 2 = 2 ^ 2 ∧ (1 : ℝ) - (2 - 0 ^ 2) ^ 2 / 8 = 1 / 2 ∧ (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [div_pow, sqrt2_sq]
  norm_num

end SpecialImaginaryPoint.QuarticResidue

#print axioms SpecialImaginaryPoint.QuarticResidue.quartic_u
#print axioms SpecialImaginaryPoint.QuarticResidue.quartic_v
#print axioms SpecialImaginaryPoint.QuarticResidue.varpi_sq
#print axioms SpecialImaginaryPoint.QuarticResidue.varpi_quartic
#print axioms SpecialImaginaryPoint.QuarticResidue.varpi'_sq
#print axioms SpecialImaginaryPoint.QuarticResidue.varpi'_quartic
#print axioms SpecialImaginaryPoint.QuarticResidue.diff_sq
#print axioms SpecialImaginaryPoint.QuarticResidue.a_sq
#print axioms SpecialImaginaryPoint.QuarticResidue.diff_is_a_sq
#print axioms SpecialImaginaryPoint.QuarticResidue.prod_sq
#print axioms SpecialImaginaryPoint.QuarticResidue.ratio_sq
#print axioms SpecialImaginaryPoint.QuarticResidue.bender_identity
#print axioms SpecialImaginaryPoint.QuarticResidue.bender_root
#print axioms SpecialImaginaryPoint.QuarticResidue.bender_hermitian
