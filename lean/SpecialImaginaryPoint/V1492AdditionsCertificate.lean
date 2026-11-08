import Mathlib

/-!
# Manuscript 14, version 14.92 (8 November 2026): the discriminants added to Sections 2.1 and 8.5

Kernel-checked identities behind two of the additions of version 14.92. The discriminant formulas
of Gelfand, Kapranov and Zelevinsky (Discriminants, Resultants, and Multidimensional Determinants,
Chapter 12, Eq. (1.38) for a trinomial and Eq. (1.35) for a quartic, pp. 405-406) enter as the
definitions `gkzTrinomial` and `gkzQuartic`, transcribed term by term; that they are discriminants is
a classical input, checked against Sylvester determinants in
`numerics/arb/manuscript14_v1492_additions_arb.py`.

* `gkz_trinomial_parry`: at `a = b = -1`, `c = 1`, `m = n - 1`, `n = k + 2`, the trinomial formula
  gives `(-1)^(n-1) (n^n + (n-1)^(n-1))` for the Parry trinomial `t^n - t^(n-1) - 1` (Section 2.1);
* `parry_discriminant_ne_zero`: this value is never zero;
* `gkz_quartic_even`: with `a_1 = a_3 = 0` the quartic formula is `16 a_0 a_4 (4 a_0 a_4 - a_2^2)^2`;
* `quartic139_discriminant`: the discriminant of `32 x^4 - 16 x^2 + 1` (display (139)) is `2^23`;
* `bender_discriminant`: for `P(y) = y^4 + (γ^2 - 2) y^2 + 1 - g^2` (display (142)) it is
  `16 (1 - g^2) (4 (1 - g^2) - (2 - γ^2)^2)^2`;
* `bender_family_discriminant`, `bender_family_pos`: on the family (144)-(145) it is `s^12/128`, with
  `s^2 = 4 - 2 γ^2`, positive for `γ^2 < 2`;
* `bender_coalescence`: where `4 (1 - g^2) = (2 - γ^2)^2`, `P(y) = (y^2 - (2 - γ^2)/2)^2`, two
  frequencies coalesce;
* `bender_zero_root`: at `g^2 = 1`, `P(y) = y^2 (y^2 + γ^2 - 2)`, one frequency vanishes.

The variables `γ2`, `g2` stand for `γ_PT^2`, `g_PT^2`.
-/

namespace SpecialImaginaryPoint.V1492Additions

/-- Gelfand-Kapranov-Zelevinsky, Chapter 12, Eq. (1.38): the discriminant of `a + b x^m + c x^n`. -/
def gkzTrinomial (a b c : ℤ) (m n : ℕ) : ℤ :=
  (n : ℤ) ^ n * a ^ (n - 1) * c ^ (n - 1)
    + (-1) ^ (n - 1) * (m : ℤ) ^ m * ((n - m : ℕ) : ℤ) ^ (n - m) * a ^ (m - 1) * b ^ n * c ^ (n - m - 1)

/-- Gelfand-Kapranov-Zelevinsky, Chapter 12, Eq. (1.35): the discriminant of
`a_0 + a_1 x + a_2 x^2 + a_3 x^3 + a_4 x^4`. -/
def gkzQuartic (a0 a1 a2 a3 a4 : ℚ) : ℚ :=
  256 * a0 ^ 3 * a4 ^ 3 - 27 * a0 ^ 2 * a3 ^ 4 - 27 * a1 ^ 4 * a4 ^ 2 + 16 * a0 * a2 ^ 4 * a4
    - 4 * a0 * a2 ^ 3 * a3 ^ 2 - 4 * a1 ^ 2 * a2 ^ 3 * a4 - 4 * a1 ^ 3 * a3 ^ 3 + a1 ^ 2 * a2 ^ 2 * a3 ^ 2
    - 192 * a0 ^ 2 * a1 * a3 * a4 ^ 2 - 128 * a0 ^ 2 * a2 ^ 2 * a4 ^ 2 + 144 * a0 ^ 2 * a2 * a3 ^ 2 * a4
    + 144 * a0 * a1 ^ 2 * a2 * a4 ^ 2 - 6 * a0 * a1 ^ 2 * a3 ^ 2 * a4 - 80 * a0 * a1 * a2 ^ 2 * a3 * a4
    + 18 * a0 * a1 * a2 * a3 ^ 3 + 18 * a1 ^ 3 * a2 * a3 * a4

lemma neg_one_pow_k_k2 (k : ℕ) : ((-1 : ℤ)) ^ k * (-1) ^ (k + 2) = 1 := by
  rw [← pow_add, show k + (k + 2) = 2 * (k + 1) by ring, pow_mul]
  norm_num

theorem gkz_trinomial_parry (k : ℕ) :
    gkzTrinomial (-1) (-1) 1 (k + 1) (k + 2)
      = (-1) ^ (k + 1) * (((k : ℤ) + 2) ^ (k + 2) + ((k : ℤ) + 1) ^ (k + 1)) := by
  unfold gkzTrinomial
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e4 : k + 2 - (k + 1) - 1 = 0 := by omega
  have e2 : k + 2 - (k + 1) = 1 := by omega
  have e3 : k + 1 - 1 = k := by omega
  rw [e1, e4, e2, e3]
  have h := neg_one_pow_k_k2 k
  try push_cast
  try simp only [one_pow, mul_one]
  linear_combination ((-1 : ℤ) ^ (k + 1) * ((k : ℤ) + 1) ^ (k + 1)) * h

theorem parry_discriminant_ne_zero (k : ℕ) :
    (-1 : ℤ) ^ (k + 1) * (((k : ℤ) + 2) ^ (k + 2) + ((k : ℤ) + 1) ^ (k + 1)) ≠ 0 := by
  have h1 : (0 : ℤ) < ((k : ℤ) + 2) ^ (k + 2) + ((k : ℤ) + 1) ^ (k + 1) := by positivity
  have h2 : ((-1 : ℤ)) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_ne_zero h2 (ne_of_gt h1)

theorem gkz_quartic_even (a0 a2 a4 : ℚ) :
    gkzQuartic a0 0 a2 0 a4 = 16 * a0 * a4 * (4 * a0 * a4 - a2 ^ 2) ^ 2 := by
  unfold gkzQuartic
  ring

theorem quartic139_discriminant : gkzQuartic 1 0 (-16) 0 32 = 2 ^ 23 := by
  unfold gkzQuartic
  norm_num

theorem bender_discriminant (γ2 g2 : ℚ) :
    gkzQuartic (1 - g2) 0 (γ2 - 2) 0 1 = 16 * (1 - g2) * (4 * (1 - g2) - (2 - γ2) ^ 2) ^ 2 := by
  unfold gkzQuartic
  ring

theorem bender_family_discriminant (γ2 : ℚ) :
    gkzQuartic (1 - (1 - (2 - γ2) ^ 2 / 8)) 0 (γ2 - 2) 0 1 = (4 - 2 * γ2) ^ 6 / 128 := by
  unfold gkzQuartic
  ring

theorem bender_family_pos (γ2 : ℚ) (h : γ2 < 2) : 0 < (4 - 2 * γ2) ^ 6 / 128 := by
  have hs : 0 < 4 - 2 * γ2 := by linarith
  exact div_pos (pow_pos hs 6) (by norm_num)

theorem bender_coalescence (γ2 g2 : ℚ) (h : 4 * (1 - g2) = (2 - γ2) ^ 2) (y : ℚ) :
    y ^ 4 + (γ2 - 2) * y ^ 2 + (1 - g2) = (y ^ 2 - (2 - γ2) / 2) ^ 2 := by
  linear_combination (1 / 4 : ℚ) * h

theorem bender_zero_root (γ2 y : ℚ) :
    y ^ 4 + (γ2 - 2) * y ^ 2 + (1 - 1) = y ^ 2 * (y ^ 2 + (γ2 - 2)) := by
  ring

end SpecialImaginaryPoint.V1492Additions

#print axioms SpecialImaginaryPoint.V1492Additions.gkz_trinomial_parry
#print axioms SpecialImaginaryPoint.V1492Additions.parry_discriminant_ne_zero
#print axioms SpecialImaginaryPoint.V1492Additions.gkz_quartic_even
#print axioms SpecialImaginaryPoint.V1492Additions.quartic139_discriminant
#print axioms SpecialImaginaryPoint.V1492Additions.bender_discriminant
#print axioms SpecialImaginaryPoint.V1492Additions.bender_family_discriminant
#print axioms SpecialImaginaryPoint.V1492Additions.bender_family_pos
#print axioms SpecialImaginaryPoint.V1492Additions.bender_coalescence
#print axioms SpecialImaginaryPoint.V1492Additions.bender_zero_root
