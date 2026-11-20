import UniformLanczos.Lemma56

/-!
# Manuscript 12, Lemma 5.6: the cases `M = 2` and `M = 1`

Source: frozen `12.tex`, label `lem:ul-spline`.

* `deriv_φM_one`: `φ_1' ≡ 0` on `(-1/2, 1/2)`;
* `deriv_φM_two_pos`, `deriv_φM_two_neg`: `φ_2'(x) = 1/(1-2x)` for `0 < x < 1/2` and
  `φ_2'(x) = -1/(1+2x)` for `-1/2 < x < 0`;
* `lemma_5_6_two`: `x φ_2'(x) = |x| / (1 - 2|x|)` on `(-1/2, 1/2)`.

At `x = 0` the function `φ_2` is not differentiable; `lemma_5_6_two` holds there because both
sides vanish.
-/

open Set Filter Topology
open EulerianBridge.Saddle

namespace UniformLanczos.Lemma56

/-- **Lemma 5.6**, `M = 1`: `φ_1' ≡ 0` on `(-1/2, 1/2)`. -/
theorem deriv_φM_one {x : ℝ} (hx : x ∈ Ioo (-(1/2):ℝ) (1/2)) : deriv (φM 1) x = 0 := by
  have hev : φM 1 =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hmem : y ∈ Ioc (-1/2:ℝ) (1/2) := ⟨by linarith [hy.1], hy.2.le⟩
    unfold φM gM
    rw [Nat.cast_one, one_mul, one_mul, w_one_eq, if_pos hmem, Real.log_one, mul_zero]
  rw [hev.deriv_eq, deriv_const]

/-- `φ_2'(x) = 1/(1-2x)` for `0 < x < 1/2`. -/
theorem deriv_φM_two_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1/2) :
    deriv (φM 2) x = 1 / (1 - 2 * x) := by
  have hev : φM 2 =ᶠ[𝓝 x] fun y => -(1/2 : ℝ) * Real.log (2 * (1 - 2 * y)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    unfold φM gM
    simp only [Nat.cast_ofNat]
    rw [w_two_of_nonneg (y := 2 * y) (by linarith [hy.1]) (by linarith [hy.2])]
  have hpos : 0 < 1 - 2 * x := by linarith
  have hne : (2:ℝ) * (1 - 2 * x) ≠ 0 := mul_ne_zero two_ne_zero hpos.ne'
  have hd : HasDerivAt (fun y : ℝ => -(1/2 : ℝ) * Real.log (2 * (1 - 2 * y)))
      (-(1/2 : ℝ) * ((2 * -(2 * 1)) / (2 * (1 - 2 * x)))) x :=
    (((((hasDerivAt_id' x).const_mul (2:ℝ)).const_sub (1:ℝ)).const_mul (2:ℝ)).log hne).const_mul _
  rw [hev.deriv_eq, hd.deriv, mul_div_mul_left _ _ (two_ne_zero : (2:ℝ) ≠ 0)]
  ring

/-- `φ_2'(x) = -1/(1+2x)` for `-1/2 < x < 0`. -/
theorem deriv_φM_two_neg {x : ℝ} (h0 : x < 0) (h1 : -(1/2) < x) :
    deriv (φM 2) x = -(1 / (1 + 2 * x)) := by
  have hev : φM 2 =ᶠ[𝓝 x] fun y => -(1/2 : ℝ) * Real.log (2 * (1 + 2 * y)) := by
    filter_upwards [Ioo_mem_nhds h1 h0] with y hy
    unfold φM gM
    simp only [Nat.cast_ofNat]
    rw [w_two_of_nonpos (y := 2 * y) (by linarith [hy.2]) (by linarith [hy.1])]
  have hpos : 0 < 1 + 2 * x := by linarith
  have hne : (2:ℝ) * (1 + 2 * x) ≠ 0 := mul_ne_zero two_ne_zero hpos.ne'
  have hd : HasDerivAt (fun y : ℝ => -(1/2 : ℝ) * Real.log (2 * (1 + 2 * y)))
      (-(1/2 : ℝ) * ((2 * (2 * 1)) / (2 * (1 + 2 * x)))) x :=
    (((((hasDerivAt_id' x).const_mul (2:ℝ)).const_add (1:ℝ)).const_mul (2:ℝ)).log hne).const_mul _
  rw [hev.deriv_eq, hd.deriv, mul_div_mul_left _ _ (two_ne_zero : (2:ℝ) ≠ 0)]
  ring

/-- **Lemma 5.6**, `M = 2`: `x φ_2'(x) = |x| / (1 - 2|x|)` on `(-1/2, 1/2)`. -/
theorem lemma_5_6_two {x : ℝ} (hx : x ∈ Ioo (-(1/2):ℝ) (1/2)) :
    x * deriv (φM 2) x = |x| / (1 - 2 * |x|) := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [deriv_φM_two_neg h hx.1, abs_of_neg h]
    ring
  · subst h
    simp
  · rw [deriv_φM_two_pos h hx.2, abs_of_pos h]
    ring

end UniformLanczos.Lemma56

#print axioms UniformLanczos.Lemma56.deriv_φM_one
#print axioms UniformLanczos.Lemma56.deriv_φM_two_pos
#print axioms UniformLanczos.Lemma56.deriv_φM_two_neg
#print axioms UniformLanczos.Lemma56.lemma_5_6_two
