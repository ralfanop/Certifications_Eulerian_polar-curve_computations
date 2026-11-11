import Mathlib

/-!
# Priority 3: sharp global Lipschitz estimate for weighted Fredholm functionals

Suppose a complex functional f on a normed additive group obeys
‖f T‖ ≤ exp(r‖T‖) and
‖f T - f S‖ ≤ r‖T-S‖ exp(r(‖T‖+‖S‖)), with r≥0.
Then the weighted functional
    g(T) = exp(-2r‖T‖) • f(T)
is globally 3r-Lipschitz.

The assumptions are explicit theorem inputs. In particular this does
NOT assert the as-yet-unproved trace-norm estimate for the genuine
finite CFC-S₁ Fredholm determinant.
-/

noncomputable section

namespace Manuscript14Priority3.SharpWeightedLipschitz

private theorem weighted_pair_le_of_le
    (r x y d : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hd : y - x ≤ d)
    (A B : ℂ)
    (hA : ‖A‖ ≤ Real.exp (r * x))
    (hAB : ‖A - B‖ ≤ (r * d) * Real.exp (r * (x + y))) :
    ‖Real.exp (-2 * r * x) • A -
        Real.exp (-2 * r * y) • B‖ ≤ 3 * r * d := by
  let wL : ℝ := Real.exp (-2 * r * x)
  let wH : ℝ := Real.exp (-2 * r * y)
  have hdelta : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hd0 : 0 ≤ d := le_trans hdelta hd
  have hw0 : 0 ≤ wH := (Real.exp_pos _).le
  have hwmon : wH ≤ wL := by
    dsimp [wL, wH]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hr hdelta]
  have hwd : 0 ≤ wL - wH := sub_nonneg.mpr hwmon
  have hs : wH = wL * Real.exp (-2 * r * (y - x)) := by
    dsimp [wL, wH]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul : wL * Real.exp (r * x) = Real.exp (-r * x) := by
    dsimp [wL]
    rw [← Real.exp_add]
    congr 1
    ring
  have hE1 :
      1 - Real.exp (-2 * r * (y - x)) ≤ 2 * r * (y - x) := by
    have h := Real.add_one_le_exp (-2 * r * (y - x))
    linarith
  have heone : Real.exp (-r * x) ≤ 1 := by
    calc
      Real.exp (-r * x) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hr hx])
      _ = 1 := Real.exp_zero
  have hweight :
      (wL - wH) * Real.exp (r * x) =
        Real.exp (-r * x) *
          (1 - Real.exp (-2 * r * (y - x))) := by
    calc
      (wL - wH) * Real.exp (r * x) =
          (wL * (1 - Real.exp (-2 * r * (y - x)))) *
            Real.exp (r * x) := by rw [hs]; ring
      _ = (wL * Real.exp (r * x)) *
          (1 - Real.exp (-2 * r * (y - x))) := by ring
      _ = _ := by rw [hmul]
  have hterm1 :
      ‖(wL - wH) • A‖ ≤ 2 * r * d := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hwd]
    calc
      (wL - wH) * ‖A‖ ≤
          (wL - wH) * Real.exp (r * x) :=
        mul_le_mul_of_nonneg_left hA hwd
      _ = Real.exp (-r * x) *
          (1 - Real.exp (-2 * r * (y - x))) := hweight
      _ ≤ Real.exp (-r * x) * (2 * r * (y - x)) :=
        mul_le_mul_of_nonneg_left hE1 (Real.exp_pos _).le
      _ ≤ 1 * (2 * r * (y - x)) :=
        mul_le_mul_of_nonneg_right heone (by positivity)
      _ ≤ 2 * r * d := by
        have hfactor : 0 ≤ 2 * r := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hd hfactor]
  have hExpProd :
      wH * Real.exp (r * (x + y)) = Real.exp (r * (x - y)) := by
    dsimp [wH]
    rw [← Real.exp_add]
    congr 1
    ring
  have hExpSmall : Real.exp (r * (x - y)) ≤ 1 := by
    calc
      Real.exp (r * (x - y)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hr hdelta])
      _ = 1 := Real.exp_zero
  have hterm2 :
      ‖wH • (A - B)‖ ≤ r * d := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
    calc
      wH * ‖A - B‖ ≤
          wH * ((r * d) * Real.exp (r * (x + y))) :=
        mul_le_mul_of_nonneg_left hAB hw0
      _ = (r * d) * (wH * Real.exp (r * (x + y))) := by ring
      _ = (r * d) * Real.exp (r * (x - y)) := by rw [hExpProd]
      _ ≤ (r * d) * 1 :=
        mul_le_mul_of_nonneg_left hExpSmall (mul_nonneg hr hd0)
      _ = r * d := mul_one _
  have heq :
      wL • A - wH • B =
        (wL - wH) • A + wH • (A - B) := by
    rw [sub_smul, smul_sub]
    abel
  change ‖wL • A - wH • B‖ ≤ 3 * r * d
  calc
    ‖wL • A - wH • B‖ =
        ‖(wL - wH) • A + wH • (A - B)‖ := by rw [heq]
    _ ≤ ‖(wL - wH) • A‖ + ‖wH • (A - B)‖ := norm_add_le _ _
    _ ≤ 2 * r * d + r * d := add_le_add hterm1 hterm2
    _ = 3 * r * d := by ring

def weighted {E : Type*} [NormedAddCommGroup E]
    (f : E → ℂ) (r : ℝ) : E → ℂ :=
  fun T => Real.exp (-2 * r * ‖T‖) • f T

/-- Global 3r Lipschitz control from the explicitly assumed Fredholm
growth and TRUE norm perturbation estimates. -/
theorem weighted_norm_sub_le_three
    {E : Type*} [NormedAddCommGroup E]
    (f : E → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hgrowth : ∀ T : E, ‖f T‖ ≤ Real.exp (r * ‖T‖))
    (hdiff : ∀ T S : E,
      ‖f T - f S‖ ≤
        (r * ‖T - S‖) * Real.exp (r * (‖T‖ + ‖S‖)))
    (T S : E) :
    ‖weighted f r T - weighted f r S‖ ≤ 3 * r * ‖T - S‖ := by
  change ‖Real.exp (-2 * r * ‖T‖) • f T -
      Real.exp (-2 * r * ‖S‖) • f S‖ ≤ 3 * r * ‖T - S‖
  by_cases hxy : ‖T‖ ≤ ‖S‖
  · exact weighted_pair_le_of_le r ‖T‖ ‖S‖ ‖T - S‖
      hr (norm_nonneg T) hxy
      (by simpa only [norm_sub_rev] using (norm_sub_norm_le S T))
      (f T) (f S) (hgrowth T) (hdiff T S)
  · have hyx : ‖S‖ ≤ ‖T‖ := le_of_not_ge hxy
    have hAB : ‖f S - f T‖ ≤
        (r * ‖T - S‖) * Real.exp (r * (‖S‖ + ‖T‖)) := by
      simpa only [norm_sub_rev] using (hdiff S T)
    have h := weighted_pair_le_of_le r ‖S‖ ‖T‖ ‖T - S‖
      hr (norm_nonneg S) hyx (norm_sub_norm_le T S)
      (f S) (f T) (hgrowth S) hAB
    calc
      ‖Real.exp (-2 * r * ‖T‖) • f T -
          Real.exp (-2 * r * ‖S‖) • f S‖ =
        ‖Real.exp (-2 * r * ‖S‖) • f S -
          Real.exp (-2 * r * ‖T‖) • f T‖ := norm_sub_rev _ _
      _ ≤ _ := h

/-- An explicit global Lipschitz constant, hence uniform continuity,
on an arbitrary normed additive group (in particular CFC-S₁). -/
theorem weighted_lipschitzWith
    {E : Type*} [NormedAddCommGroup E]
    (f : E → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hgrowth : ∀ T : E, ‖f T‖ ≤ Real.exp (r * ‖T‖))
    (hdiff : ∀ T S : E,
      ‖f T - f S‖ ≤
        (r * ‖T - S‖) * Real.exp (r * (‖T‖ + ‖S‖))) :
    LipschitzWith ⟨3 * r, by positivity⟩ (weighted f r) := by
  apply LipschitzWith.of_dist_le_mul
  intro T S
  rw [dist_eq_norm, dist_eq_norm]
  change ‖weighted f r T - weighted f r S‖ ≤
    (3 * r) * ‖T - S‖
  exact weighted_norm_sub_le_three f r hr hgrowth hdiff T S

/-- Uniform continuity of the weighted functional derived WITHOUT an
extra uniform-continuity axiom, once the finite trace-norm estimate
is available. -/
theorem weighted_uniformContinuous
    {E : Type*} [NormedAddCommGroup E]
    (f : E → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hgrowth : ∀ T : E, ‖f T‖ ≤ Real.exp (r * ‖T‖))
    (hdiff : ∀ T S : E,
      ‖f T - f S‖ ≤
        (r * ‖T - S‖) * Real.exp (r * (‖T‖ + ‖S‖))) :
    UniformContinuous (weighted f r) :=
  (weighted_lipschitzWith f r hr hgrowth hdiff).uniformContinuous

#print axioms Manuscript14Priority3.SharpWeightedLipschitz.weighted_norm_sub_le_three
#print axioms Manuscript14Priority3.SharpWeightedLipschitz.weighted_lipschitzWith
#print axioms Manuscript14Priority3.SharpWeightedLipschitz.weighted_uniformContinuous

end Manuscript14Priority3.SharpWeightedLipschitz
