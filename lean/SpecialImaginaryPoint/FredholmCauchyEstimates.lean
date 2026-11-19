import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cauchy estimates with simultaneous translations

These are classical complex-analytic and algebraic lemmas. The Fredholm
application is in `V14119Priority3UniversalFredholmDerivativeVariation`.
No bound on the derivative difference is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace Manuscript14Priority3.FredholmCauchyEstimates

open Complex Metric

/-- Translate both functions by the same circle variable before applying Cauchy.
This allows the centres to differ without introducing a second derivative. -/
theorem translated_deriv_sub_norm_le
    (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z w : ℂ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hC : ∀ u ∈ sphere (0 : ℂ) ρ, ‖f (z + u) - g (w + u)‖ ≤ C) :
    ‖deriv f z - deriv g w‖ ≤ C / ρ := by
  have hdf : HasDerivAt (fun u : ℂ => f (z + u)) (deriv f z) 0 := by
    simpa! only [Function.comp_def, add_zero, mul_one] using
      (hf (z + 0)).hasDerivAt.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add z)
  have hdg : HasDerivAt (fun u : ℂ => g (w + u)) (deriv g w) 0 := by
    simpa! only [Function.comp_def, add_zero, mul_one] using
      (hg (w + 0)).hasDerivAt.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add w)
  have hd : Differentiable ℂ (fun u : ℂ => f (z + u) - g (w + u)) :=
    (hf.comp ((differentiable_const z).add differentiable_id)).sub
      (hg.comp ((differentiable_const w).add differentiable_id))
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hρ hd.diffContOnCl hC
  have heq : deriv (fun u : ℂ => f (z + u) - g (w + u)) 0 =
      deriv f z - deriv g w := by
    convert (hdf.sub hdg).deriv using 1
  rwa [heq] at h

/-- Cauchy applied after subtracting the centre value. Only increments need
to be bounded; no separate global growth theorem is needed. -/
theorem translated_deriv_norm_le
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (z : ℂ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hC : ∀ u ∈ sphere (0 : ℂ) ρ, ‖f (z + u) - f z‖ ≤ C) :
    ‖deriv f z‖ ≤ C / ρ := by
  simpa only [deriv_const, sub_zero] using
    translated_deriv_sub_norm_le f (fun _ => f z) hf (differentiable_const (f z))
      z 0 ρ C hρ hC

/-- An explicit quotient bound, with no unknown perturbed denominator.
The strict margin proves that both denominators are nonzero. -/
theorem quotient_difference_le_of_margin
    (A B a b : ℂ) (E Δ Bbound : ℝ)
    (hE : ‖a - b‖ ≤ E) (hΔ : ‖A - B‖ ≤ Δ) (hB : ‖B‖ ≤ Bbound)
    (hmargin : E < ‖b‖) :
    ‖A / a - B / b‖ ≤
      Δ / (‖b‖ - E) + (Bbound * E) / ((‖b‖ - E) * ‖b‖) := by
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hΔ0 : 0 ≤ Δ := (norm_nonneg _).trans hΔ
  have hB0 : 0 ≤ Bbound := (norm_nonneg _).trans hB
  have hm : 0 < ‖b‖ - E := sub_pos.mpr hmargin
  have hb : 0 < ‖b‖ := lt_of_le_of_lt hE0 hmargin
  have hlo : ‖b‖ - E ≤ ‖a‖ := by
    have ht' : ‖b‖ ≤ ‖b - a‖ + ‖a‖ := by
      simpa using norm_add_le (b - a) a
    rw [norm_sub_rev] at ht'
    linarith
  have ha : 0 < ‖a‖ := hm.trans_le hlo
  have hdecomp : A / a - B / b = (A - B) / a - B * (a - b) / (a * b) := by
    field_simp [norm_pos_iff.mp ha, norm_pos_iff.mp hb]
    <;> ring
  have hfirst : ‖A - B‖ / ‖a‖ ≤ Δ / (‖b‖ - E) := by
    apply (div_le_div_iff₀ ha hm).mpr
    exact (mul_le_mul_of_nonneg_right hΔ hm.le).trans
      (mul_le_mul_of_nonneg_left hlo hΔ0)
  have hnum : ‖B‖ * ‖a - b‖ ≤ Bbound * E :=
    mul_le_mul hB hE (norm_nonneg _) hB0
  have hden : (‖b‖ - E) * ‖b‖ ≤ ‖a‖ * ‖b‖ :=
    mul_le_mul_of_nonneg_right hlo hb.le
  have hsecond : (‖B‖ * ‖a - b‖) / (‖a‖ * ‖b‖) ≤
      (Bbound * E) / ((‖b‖ - E) * ‖b‖) := by
    apply (div_le_div_iff₀ (mul_pos ha hb) (mul_pos hm hb)).mpr
    exact (mul_le_mul_of_nonneg_right hnum (mul_pos hm hb).le).trans
      (mul_le_mul_of_nonneg_left hden (mul_nonneg hB0 hE0))
  calc
    ‖A / a - B / b‖ = ‖(A - B) / a - B * (a - b) / (a * b)‖ := by rw [hdecomp]
    _ ≤ ‖(A - B) / a‖ + ‖B * (a - b) / (a * b)‖ := norm_sub_le _ _
    _ = ‖A - B‖ / ‖a‖ + (‖B‖ * ‖a - b‖) / (‖a‖ * ‖b‖) := by
      simp only [norm_div, norm_mul]
    _ ≤ _ := add_le_add hfirst hsecond

#print axioms translated_deriv_sub_norm_le
#print axioms translated_deriv_norm_le
#print axioms quotient_difference_le_of_margin

end Manuscript14Priority3.FredholmCauchyEstimates
