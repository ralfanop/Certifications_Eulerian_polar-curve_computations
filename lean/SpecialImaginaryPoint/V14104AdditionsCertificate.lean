import Mathlib

/-!
# Manuscript 14, versions 14.95-14.104 (8 November 2026): the rewritten displays of Propositions 8.4, 8.6, 8.7

Kernel-checked identities behind the displays added or rewritten in versions 14.95-14.104 (equation
numbers of version 14.104). The discriminant formula of Gelfand, Kapranov and Zelevinsky (Chapter 12,
Eq. (1.35), p. 405) enters as the definition `gkzQuartic`, transcribed term by term, as in
`V1492AdditionsCertificate`; the identity `L_2(s, χ_1) = (1 - 2^(-s)) ζ(s)` of Mathar's Table 22 enters
`lseries_forms` as a hypothesis. Numerical values (the 50 decimals of (142), ζ(1/2), the Hurwitz value of
`L_2(1/2, χ_1)`) are certified in `numerics/arb/manuscript14_v14104_additions_arb.py`.

* `monic139_scaled`: 32 times the monic form (139) is the integer form `32x^4 - 16x^2 + 1` of the proof;
* `monic139_discriminant`, `monic139_discriminant_scaling`: the discriminant of (139) is `1/128`, and
  `32^6` times it is the discriminant `2^23` of the integer form;
* `x0_root`: `x_0 = (1/2) √(1 + 1/√2)` of (141) is a root of (139);
* `bender_scale_form`, `bender_coupling_form`: the forms `2(2 - γ^2)` of (145) and
  `1 - ((2 - γ^2)/√8)^2` of (146);
* `bender_monic`: (144), `P_PT(s x) = s^4 (x^4 - x^2/2 + 1/32)` under (145)-(146);
* `bender_family_discriminant_monic`: on (145)-(146) the discriminant of `P_PT` is `s^12` times that of (139);
* `bender_hermitian`: (148), `s^2 = 4` and `g^2 = 1/2` at `γ = 0`;
* `viete137`: the fraction form of (137);
* `lseries_forms`: (128)-(129), `1 - L/ζ = 1/√2` and `1/2 - L/ζ = (√2 - 1)/2` when `L = (1 - 1/√2) ζ`, `ζ ≠ 0`.

The variables `γ2`, `g2`, `s` stand for `γ_PT^2`, `g_PT^2`, `s_PT`.
-/

namespace SpecialImaginaryPoint.V14104Additions

/-- Gelfand-Kapranov-Zelevinsky, Chapter 12, Eq. (1.35): the discriminant of
`a_0 + a_1 x + a_2 x^2 + a_3 x^3 + a_4 x^4`. -/
def gkzQuartic (a0 a1 a2 a3 a4 : ℝ) : ℝ :=
  256 * a0 ^ 3 * a4 ^ 3 - 27 * a0 ^ 2 * a3 ^ 4 - 27 * a1 ^ 4 * a4 ^ 2 + 16 * a0 * a2 ^ 4 * a4
    - 4 * a0 * a2 ^ 3 * a3 ^ 2 - 4 * a1 ^ 2 * a2 ^ 3 * a4 - 4 * a1 ^ 3 * a3 ^ 3 + a1 ^ 2 * a2 ^ 2 * a3 ^ 2
    - 192 * a0 ^ 2 * a1 * a3 * a4 ^ 2 - 128 * a0 ^ 2 * a2 ^ 2 * a4 ^ 2 + 144 * a0 ^ 2 * a2 * a3 ^ 2 * a4
    + 144 * a0 * a1 ^ 2 * a2 * a4 ^ 2 - 6 * a0 * a1 ^ 2 * a3 ^ 2 * a4 - 80 * a0 * a1 * a2 ^ 2 * a3 * a4
    + 18 * a0 * a1 * a2 * a3 ^ 3 + 18 * a1 ^ 3 * a2 * a3 * a4

theorem monic139_scaled (x : ℝ) : 32 * (x ^ 4 - x ^ 2 / 2 + 1 / 32) = 32 * x ^ 4 - 16 * x ^ 2 + 1 := by
  ring

theorem monic139_discriminant : gkzQuartic (1 / 32) 0 (-1 / 2) 0 1 = 1 / 128 := by
  unfold gkzQuartic
  norm_num

theorem monic139_discriminant_scaling :
    gkzQuartic (1 / 32) 0 (-1 / 2) 0 1 * 32 ^ 6 = gkzQuartic 1 0 (-16) 0 32 := by
  unfold gkzQuartic
  norm_num

theorem x0_root :
    (Real.sqrt (1 + 1 / Real.sqrt 2) / 2) ^ 4 - (Real.sqrt (1 + 1 / Real.sqrt 2) / 2) ^ 2 / 2 + 1 / 32 = 0 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) ≤ 1 + 1 / Real.sqrt 2 := by positivity
  have hx : Real.sqrt (1 + 1 / Real.sqrt 2) ^ 2 = 1 + 1 / Real.sqrt 2 := Real.sq_sqrt hpos
  have hu : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by rw [div_pow, one_pow, h2]
  have e : (Real.sqrt (1 + 1 / Real.sqrt 2) / 2) ^ 4 - (Real.sqrt (1 + 1 / Real.sqrt 2) / 2) ^ 2 / 2 + 1 / 32
      = (Real.sqrt (1 + 1 / Real.sqrt 2) ^ 2) ^ 2 / 16 - Real.sqrt (1 + 1 / Real.sqrt 2) ^ 2 / 8 + 1 / 32 := by
    ring
  rw [e, hx]
  linear_combination (1 / 16 : ℝ) * hu

theorem bender_scale_form (γ2 : ℝ) : 2 * (2 - γ2) = 4 - 2 * γ2 := by
  ring

theorem bender_coupling_form (γ2 : ℝ) : 1 - ((2 - γ2) / Real.sqrt 8) ^ 2 = 1 - (2 - γ2) ^ 2 / 8 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]

theorem bender_monic (γ2 g2 s x : ℝ) (hs : s ^ 2 = 2 * (2 - γ2))
    (hg : g2 = 1 - ((2 - γ2) / Real.sqrt 8) ^ 2) :
    (s * x) ^ 4 + (γ2 - 2) * (s * x) ^ 2 + (1 - g2) = s ^ 4 * (x ^ 4 - x ^ 2 / 2 + 1 / 32) := by
  rw [hg, bender_coupling_form]
  linear_combination (x ^ 2 * s ^ 2 / 2 - (s ^ 2 + 2 * (2 - γ2)) / 32) * hs

theorem bender_family_discriminant_monic (γ2 s : ℝ) (hs : s ^ 2 = 2 * (2 - γ2)) :
    gkzQuartic (1 - (1 - (2 - γ2) ^ 2 / 8)) 0 (γ2 - 2) 0 1
      = s ^ 12 * gkzQuartic (1 / 32) 0 (-1 / 2) 0 1 := by
  have h12 : s ^ 12 = (s ^ 2) ^ 6 := by ring
  rw [h12, hs]
  unfold gkzQuartic
  ring

theorem bender_hermitian :
    2 * (2 - (0 : ℝ)) = 4 ∧ 1 - ((2 - (0 : ℝ)) / Real.sqrt 8) ^ 2 = 1 / 2 := by
  refine ⟨by norm_num, ?_⟩
  rw [bender_coupling_form]
  norm_num

theorem viete137 (z μ : ℝ) :
    z / 4 * μ * Real.sqrt (2 + μ) = z * (μ / 2) * (Real.sqrt (2 + μ) / 2) := by
  ring

theorem lseries_forms (L ζ : ℝ) (hζ : ζ ≠ 0) (hL : L = (1 - 1 / Real.sqrt 2) * ζ) :
    1 - L / ζ = 1 / Real.sqrt 2 ∧ 1 / 2 - L / ζ = (Real.sqrt 2 - 1) / 2 := by
  have h : L / ζ = 1 - 1 / Real.sqrt 2 := by
    rw [hL, mul_div_assoc, div_self hζ, mul_one]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    rw [eq_div_iff hs, div_mul_eq_mul_div, h2]
    norm_num
  constructor
  · rw [h]
    ring
  · rw [h]
    linear_combination (-1 : ℝ) * hinv

end SpecialImaginaryPoint.V14104Additions

#print axioms SpecialImaginaryPoint.V14104Additions.monic139_scaled
#print axioms SpecialImaginaryPoint.V14104Additions.monic139_discriminant
#print axioms SpecialImaginaryPoint.V14104Additions.monic139_discriminant_scaling
#print axioms SpecialImaginaryPoint.V14104Additions.x0_root
#print axioms SpecialImaginaryPoint.V14104Additions.bender_scale_form
#print axioms SpecialImaginaryPoint.V14104Additions.bender_coupling_form
#print axioms SpecialImaginaryPoint.V14104Additions.bender_monic
#print axioms SpecialImaginaryPoint.V14104Additions.bender_family_discriminant_monic
#print axioms SpecialImaginaryPoint.V14104Additions.bender_hermitian
#print axioms SpecialImaginaryPoint.V14104Additions.viete137
#print axioms SpecialImaginaryPoint.V14104Additions.lseries_forms
