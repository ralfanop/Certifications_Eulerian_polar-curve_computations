import Mathlib

/-!
# Manuscript 14, display (52) at `λ = 0`: the planar spin

Display (52) of manuscript 14 gives the Fourier–Laplace transform of the ultraspherical law
`ν_λ`, the single-spin partition function of Stanley's `n`-vector model with `n = 2λ + 2`:
`∫_{-1}^{1} e^{xu} dν_λ(u) = Γ(λ+1) (2/x)^λ I_λ(x) = ∑_k (x²/4)^k / (k! (λ+1)_k)`.
The cases `λ = ±1/2` are certified numerically by `manuscript14_rem44_ising_readings_arb.py`.
This module kernel-checks the case `λ = 0`, the planar spin: `ν₀` is the arcsine law, with
density `π⁻¹ (1 - u²)^{-1/2}` on `(-1, 1)`, and `(1)_k = k!`.

* `arcsine_pushforward`: `ν₀` is the law of `cos θ` for `θ` uniform on `(0, π)`, in the form
  `∫ G(u) dν₀(u) = π⁻¹ ∫_0^π G(cos θ) dθ` for every measurable `G ≥ 0`.
* `nu0_univ`: `ν₀` is a probability measure.
* `cos_moment_even`, `cos_moment_odd`: the moments of `ν₀`, `C(2k,k)/4^k` and `0`.
* `planar_spin_series`: `π⁻¹ ∫_0^π e^{x cos θ} dθ = ∑_k (x²/4)^k / (k!)²` (as a `HasSum`).
* `planar_spin_52`: (52) at `λ = 0`, `∫_{-1}^{1} e^{xu} dν₀(u) = ∑_k (x²/4)^k / (k! (1)_k)`.
* `circle_average`: the same value is the average of `e^{x cos θ}` over the full circle, i.e.
  over the axial component of a uniform unit vector of `ℝ²` (`n = 2`).
-/

open MeasureTheory Set Filter
open scoped ENNReal Real Nat

noncomputable section

namespace Manuscript14PlanarSpin

/-! ## The moments of the arcsine law -/

theorem cos_moment_succ_succ (n : ℕ) :
    (∫ θ in (0 : ℝ)..π, Real.cos θ ^ (n + 2)) =
      ((n : ℝ) + 1) / ((n : ℝ) + 2) * ∫ θ in (0 : ℝ)..π, Real.cos θ ^ n := by
  rw [integral_cos_pow]
  simp [Real.sin_pi]

/-- The odd moments of `ν₀` vanish. -/
theorem cos_moment_odd (m : ℕ) : (∫ θ in (0 : ℝ)..π, Real.cos θ ^ (2 * m + 1)) = 0 := by
  induction m with
  | zero => simp [integral_cos]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, cos_moment_succ_succ, ih, mul_zero]

/-- The even moments of `ν₀`: `π⁻¹ ∫_0^π cos^{2m} θ dθ = C(2m,m)/4^m`. -/
theorem cos_moment_even (m : ℕ) :
    (∫ θ in (0 : ℝ)..π, Real.cos θ ^ (2 * m)) = π * (Nat.centralBinom m : ℝ) / 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, cos_moment_succ_succ, ih]
    have h := Nat.succ_mul_centralBinom_succ m
    have h' : ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ) =
        2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
      exact_mod_cast h
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    have e : (Nat.centralBinom (m + 1) : ℝ) =
        2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) / ((m : ℝ) + 1) := by
      rw [eq_div_iff hm]
      linarith
    rw [e, pow_succ]
    push_cast
    first
      | (field_simp; ring)
      | field_simp

/-! ## The series of the planar-spin partition function -/

theorem hasSum_cos_moments (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n ! : ℝ) * ∫ θ in (0 : ℝ)..π, Real.cos θ ^ n)
      (∫ θ in (0 : ℝ)..π, Real.exp (x * Real.cos θ)) := by
  have hF : ∀ n : ℕ, (∫ θ in (0 : ℝ)..π, (x * Real.cos θ) ^ n / (n ! : ℝ)) =
      x ^ n / (n ! : ℝ) * ∫ θ in (0 : ℝ)..π, Real.cos θ ^ n := by
    intro n
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    ring
  have key : HasSum (fun n : ℕ => ∫ θ in (0 : ℝ)..π, (x * Real.cos θ) ^ n / (n ! : ℝ))
      (∫ θ in (0 : ℝ)..π, Real.exp (x * Real.cos θ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => |x| ^ n / (n ! : ℝ)) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (by fun_prop : Continuous fun θ : ℝ => (x * Real.cos θ) ^ n / (n ! : ℝ)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall (fun θ _ => ?_)
      have h1 : |x * Real.cos θ| ≤ |x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg x) (Real.abs_cos_le_one θ)
      rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
      gcongr
    · exact Eventually.of_forall (fun θ _ => Real.summable_pow_div_factorial |x|)
    · exact intervalIntegrable_const
    · refine Eventually.of_forall (fun θ _ => ?_)
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (x * Real.cos θ)
  simpa only [hF] using key

/-- The planar-spin partition function as a series:
`π⁻¹ ∫_0^π e^{x cos θ} dθ = ∑_k (x²/4)^k / (k!)²`. -/
theorem planar_spin_series (x : ℝ) :
    HasSum (fun k : ℕ => (x ^ 2 / 4) ^ k / ((k ! : ℝ) ^ 2))
      ((∫ θ in (0 : ℝ)..π, Real.exp (x * Real.cos θ)) / π) := by
  have h := (hasSum_cos_moments x).div_const π
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab
    simp only at hab
    omega
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      x ^ n / (n ! : ℝ) * (∫ θ in (0 : ℝ)..π, Real.cos θ ^ n) / π = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact absurd ⟨m, by show 2 * m = n; omega⟩ hn
      · exact ⟨m, hm⟩
    rw [cos_moment_odd, mul_zero, zero_div]
  have h2 := (hinj.hasSum_iff (f := fun n : ℕ =>
      x ^ n / (n ! : ℝ) * (∫ θ in (0 : ℝ)..π, Real.cos θ ^ n) / π) hodd).mpr h
  convert h2 using 1
  funext k
  simp only [Function.comp_apply]
  rw [cos_moment_even]
  have hf : ((2 * k) ! : ℝ) = (Nat.centralBinom k : ℝ) * (k ! : ℝ) * (k ! : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rw [show 2 * k - k = k by omega] at this
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact_mod_cast this.symm
  have hπ := Real.pi_ne_zero
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  have hc : (Nat.centralBinom k : ℝ) ≠ 0 := by exact_mod_cast (Nat.centralBinom_pos k).ne'
  rw [hf, pow_mul, div_pow]
  first
    | (field_simp; ring)
    | field_simp

/-! ## The arcsine law as the image of the uniform angle -/

theorem cos_image : Real.cos '' Ioo 0 π = Ioo (-1) 1 := by
  ext u
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have h0 : (0 : ℝ) ∈ Icc 0 π := ⟨le_refl _, Real.pi_pos.le⟩
    have hπ : π ∈ Icc 0 π := ⟨Real.pi_pos.le, le_refl _⟩
    have hθ' : θ ∈ Icc 0 π := Ioo_subset_Icc_self hθ
    constructor
    · have := Real.strictAntiOn_cos hθ' hπ hθ.2
      rwa [Real.cos_pi] at this
    · have := Real.strictAntiOn_cos h0 hθ' hθ.1
      rwa [Real.cos_zero] at this
  · rintro ⟨h1, h2⟩
    refine ⟨Real.arccos u, ⟨Real.arccos_pos.mpr h2, Real.arccos_lt_pi.mpr h1⟩, ?_⟩
    exact Real.cos_arccos h1.le h2.le

/-- **The arcsine law `ν₀` is the law of `cos θ`, `θ` uniform on `(0, π)`**: for every
measurable `G ≥ 0`, `∫ G(u) π⁻¹ (1 - u²)^{-1/2} du = π⁻¹ ∫_0^π G(cos θ) dθ`. -/
theorem arcsine_pushforward (G : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (1 / (π * Real.sqrt (1 - u ^ 2))) * G u =
      ENNReal.ofReal (1 / π) * ∫⁻ θ in Ioo 0 π, G (Real.cos θ) := by
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul
    (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) π))
    (fun θ _ => (Real.hasDerivAt_cos θ).hasDerivWithinAt)
    (Real.injOn_cos.mono Ioo_subset_Icc_self)
    (fun u => ENNReal.ofReal (1 / (π * Real.sqrt (1 - u ^ 2))) * G u)
  rw [cos_image] at hcv
  rw [hcv, ← lintegral_const_mul' (ENNReal.ofReal (1 / π)) _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hs' : Real.sin θ ≠ 0 := hs.ne'
  have hsq : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [← Real.sin_eq_sqrt_one_sub_cos_sq hθ.1.le hθ.2.le]
  try dsimp only
  rw [hsq, abs_neg, abs_of_pos hs, ← mul_assoc, ← ENNReal.ofReal_mul hs.le]
  congr 2
  have hπ := Real.pi_ne_zero
  first
    | (field_simp; ring)
    | field_simp

/-- `ν₀` is a probability law. -/
theorem nu0_univ :
    ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (1 / (π * Real.sqrt (1 - u ^ 2))) = 1 := by
  have h := arcsine_pushforward (fun _ => 1)
  simp only [mul_one] at h
  rw [h, setLIntegral_const, one_mul, Real.volume_Ioo, sub_zero,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / π by positivity), one_div_mul_cancel Real.pi_ne_zero,
    ENNReal.ofReal_one]

/-- **Display (52) at `λ = 0`**: `∫_{-1}^{1} e^{xu} dν₀(u) = ∑_k (x²/4)^k / (k! (1)_k)`, with
`(1)_k = k!`; the series is `I₀(x)`. -/
theorem planar_spin_52 (x : ℝ) :
    ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (Real.exp (x * u) / (π * Real.sqrt (1 - u ^ 2))) =
      ENNReal.ofReal (∑' k : ℕ, (x ^ 2 / 4) ^ k / ((k ! : ℝ) * (k ! : ℝ))) := by
  have e1 : ∀ u : ℝ, ENNReal.ofReal (Real.exp (x * u) / (π * Real.sqrt (1 - u ^ 2))) =
      ENNReal.ofReal (1 / (π * Real.sqrt (1 - u ^ 2))) * ENNReal.ofReal (Real.exp (x * u)) := by
    intro u
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (π * Real.sqrt (1 - u ^ 2)) by positivity)]
    congr 1
    ring
  simp_rw [e1]
  rw [arcsine_pushforward (fun u => ENNReal.ofReal (Real.exp (x * u)))]
  have hint : IntegrableOn (fun θ : ℝ => Real.exp (x * Real.cos θ)) (Ioo 0 π) :=
    ((by fun_prop : Continuous fun θ : ℝ => Real.exp (x * Real.cos θ)).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall (fun θ => (Real.exp_pos _).le)),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / π by positivity), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]
  congr 1
  have hs : ∀ k : ℕ, (x ^ 2 / 4) ^ k / ((k ! : ℝ) * (k ! : ℝ)) = (x ^ 2 / 4) ^ k / ((k ! : ℝ) ^ 2) := by
    intro k
    rw [sq (k ! : ℝ)]
  simp_rw [hs]
  rw [(planar_spin_series x).tsum_eq]
  ring

/-- The planar spin as the axial component of a uniform unit vector of `ℝ²`: the average of
`e^{x cos θ}` over the full circle equals the average over `(0, π)`. -/
theorem circle_average (x : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * π), Real.exp (x * Real.cos θ)) / (2 * π) =
      (∫ θ in (0 : ℝ)..π, Real.exp (x * Real.cos θ)) / π := by
  have hc : Continuous fun θ : ℝ => Real.exp (x * Real.cos θ) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h2 : (∫ θ in π..(2 * π), Real.exp (x * Real.cos θ)) =
      ∫ θ in (0 : ℝ)..π, Real.exp (x * Real.cos θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Real.exp (x * Real.cos θ)) (a := 0) (b := π) (2 * π)
    simp only [Real.cos_two_pi_sub, sub_zero] at h
    rw [show 2 * π - π = π by ring] at h
    exact h.symm
  rw [h2]
  have hπ := Real.pi_ne_zero
  first
    | (field_simp; ring)
    | field_simp

/-! ## Axiom audit -/

#print axioms cos_moment_odd
#print axioms cos_moment_even
#print axioms hasSum_cos_moments
#print axioms planar_spin_series
#print axioms arcsine_pushforward
#print axioms nu0_univ
#print axioms planar_spin_52
#print axioms circle_average

end Manuscript14PlanarSpin
