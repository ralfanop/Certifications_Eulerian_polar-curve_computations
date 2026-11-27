import EulerianGrothendieck.JacobiFourier20261127
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! M12 Lemma 5.12, equation (181).
Use exponential tilting of the factorial series, rather than Stirling.
This yields the actual uniform exponential entry bound outside a linear
propagation cone and a polynomial decay estimate of any fixed order. -/
noncomputable section
open NormedSpace
open scoped ENNReal InnerProductSpace
namespace M12JacobiPropagation
open M12BilateralJacobi M12JacobiFourier

theorem entry_norm_le (T : Op) (k l : ℤ) : ‖entry T k l‖ ≤ ‖T‖ := by
  let x : H := lp.single 2 l 1
  have hx : ‖x‖ = 1 := by simp [x,lp.norm_single]
  calc
    _ ≤ ‖T x‖ := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ _
    _ ≤ ‖T‖*‖x‖ := T.le_opNorm x
    _ = ‖T‖ := by rw [hx,mul_one]

def entryMap (k l : ℤ) : Op →L[ℂ] ℂ :=
  ({ toFun := fun T => entry T k l
     map_add' := fun A C => rfl
     map_smul' := fun c A => rfl } : Op →ₗ[ℂ] ℂ).mkContinuous 1
      (fun T => by
        change ‖entry T k l‖ ≤ 1 * ‖T‖
        simpa only [one_mul] using entry_norm_le T k l)

theorem entryMap_apply (k l : ℤ) (T : Op) : entryMap k l T = entry T k l := rfl

theorem exp_entry_series (A : Op) (k l : ℤ) :
    entry (exp A) k l =
      ∑' n : ℕ, ((n.factorial:ℂ)⁻¹) * entry (A^n) k l := by
  rw [← entryMap_apply,NormedSpace.exp_eq_tsum ℂ,
    ContinuousLinearMap.map_tsum _ (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)]
  simp only [map_smul,entryMap_apply,smul_eq_mul]

theorem generator_power_norm (u : Bonds) (t : ℝ) (n : ℕ) :
    ‖((((t:ℂ)*Complex.I) • J u)^n : Op)‖ ≤ |t|^n := by
  have hA : ‖((t:ℂ)*Complex.I) • J u‖ ≤ |t| := by
    rw [norm_smul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left (J_norm_le u) (abs_nonneg t)
  by_cases hn : n=0
  · subst n
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact (norm_pow_le' _ (Nat.pos_of_ne_zero hn)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hA n)

theorem generator_power_outside (u : Bonds) (t : ℝ) (n : ℕ) (k l : ℤ)
    (h : k < l-(n:ℤ) ∨ l+(n:ℤ)<k) :
    entry ((((t:ℂ)*Complex.I) • J u)^n) k l = 0 := by
  rw [smul_pow]
  change (((t:ℂ)*Complex.I)^n)*entry ((J u)^n) k l = 0
  rw [power_entry_outside u n k l h,mul_zero]

theorem exp_real_series (x : ℝ) :
    Real.exp x = ∑' n : ℕ, ((n.factorial:ℝ)⁻¹)*x^n := by
  rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum ℝ]
  rfl

theorem exp_real_summable (x : ℝ) :
    Summable (fun n : ℕ => ((n.factorial:ℝ)⁻¹)*x^n) :=
  NormedSpace.expSeries_summable' (𝕂 := ℝ) x

theorem tilted_power (a : ℝ) (ha : 0 ≤ a) (d n : ℕ) (hd : d ≤ n) :
    a^n ≤ Real.exp (-(d:ℝ))*(Real.exp 1*a)^n := by
  rw [mul_pow,← mul_assoc,← Real.exp_nat_mul,← Real.exp_add]
  have h : 0 ≤ -(d:ℝ)+(n:ℝ)*1 := by
    have hh : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hd
    linarith
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right ((by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr h : 1 ≤ Real.exp (-(d:ℝ)+(n:ℝ)*1))) (pow_nonneg ha n)

/-- Exact exponential cone estimate for the actual bilateral operator. -/
theorem exponential_entry_bound (u : Bonds) (t : ℝ) (k l : ℤ) (d : ℕ)
    (hd : k ≤ l-(d:ℤ) ∨ l+(d:ℤ) ≤ k) :
    ‖entry (exp (((t:ℂ)*Complex.I) • J u)) k l‖ ≤
      Real.exp (Real.exp 1*|t|-(d:ℝ)) := by
  let A : Op := ((t:ℂ)*Complex.I) • J u
  let a : ℕ → ℂ := fun n => ((n.factorial:ℂ)⁻¹)*entry (A^n) k l
  let g : ℕ → ℝ := fun n => Real.exp (-(d:ℝ))*(((n.factorial:ℝ)⁻¹)*(Real.exp 1*|t|)^n)
  have hg : Summable g := (exp_real_summable _).mul_left _
  have hterm : ∀ n, ‖a n‖ ≤ g n := by
    intro n
    by_cases hn : n < d
    · have hz : entry (A^n) k l = 0 :=
        generator_power_outside u t n k l (by omega)
      simp only [a,hz,mul_zero,norm_zero]
      dsimp [g]
      positivity
    · have hn' : d ≤ n := by omega
      dsimp [a,g]
      rw [norm_mul,norm_inv,Complex.norm_natCast]
      calc
        _ ≤ ((n.factorial:ℝ)⁻¹)*|t|^n :=
          mul_le_mul_of_nonneg_left ((entry_norm_le _ k l).trans (generator_power_norm u t n)) (by positivity)
        _ ≤ ((n.factorial:ℝ)⁻¹)*(Real.exp (-(d:ℝ))*(Real.exp 1*|t|)^n) :=
          mul_le_mul_of_nonneg_left (tilted_power |t| (abs_nonneg t) d n hn') (by positivity)
        _ = _ := by ring
  have hs : Summable (fun n => ‖a n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hg
  change ‖entry (exp A) k l‖ ≤ _
  rw [exp_entry_series]
  change ‖∑' n, a n‖ ≤ _
  calc
    _ ≤ ∑' n, ‖a n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, g n := hs.tsum_le_tsum hterm hg
    _ = _ := by
      unfold g
      rw [tsum_mul_left,← exp_real_series,← Real.exp_add]
      congr 1
      ring

theorem far_cone (u : Bonds) (t : ℝ) (k l : ℤ) (d : ℕ)
    (hd : k ≤ l-(d:ℤ) ∨ l+(d:ℤ) ≤ k)
    (hfar : 2*Real.exp 1*|t| ≤ (d:ℝ)) :
    ‖entry (exp (((t:ℂ)*Complex.I) • J u)) k l‖ ≤ Real.exp (-(d:ℝ)/2) :=
  (exponential_entry_bound u t k l d hd).trans (Real.exp_le_exp.mpr (by linarith))

/-- Polynomial decay from the exponential cone, with explicit factorial
constant at every finite order. -/
theorem far_cone_polynomial (u : Bonds) (t : ℝ) (k l : ℤ) (d N : ℕ)
    (hd : k ≤ l-(d:ℤ) ∨ l+(d:ℤ) ≤ k)
    (hfar : 2*Real.exp 1*|t| ≤ (d:ℝ)) :
    ‖entry (exp (((t:ℂ)*Complex.I) • J u)) k l‖ ≤
      (Nat.factorial N:ℝ)*2^N*Real.exp (1/2)/(1+(d:ℝ))^N := by
  apply (far_cone u t k l d hd hfar).trans
  have h := Real.pow_div_factorial_le_exp ((1+(d:ℝ))/2) (by positivity) N
  have hf : 0 < (Nat.factorial N:ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hp : 0 < (1+(d:ℝ))^N := by positivity
  have h₁ : ((1+(d:ℝ))/2)^N ≤ Real.exp ((1+(d:ℝ))/2)*(Nat.factorial N:ℝ) :=
    (div_le_iff₀ hf).mp h
  rw [div_pow,div_le_iff₀ (by positivity : (0:ℝ)<2^N)] at h₁
  apply (le_div_iff₀ hp).2
  have h₂ := mul_le_mul_of_nonneg_left h₁ (Real.exp_nonneg (-(d:ℝ)/2))
  rw [show (1+(d:ℝ))/2 = 1/2+(d:ℝ)/2 by ring, Real.exp_add] at h₂
  have he : Real.exp (-(d:ℝ)/2)*Real.exp ((d:ℝ)/2) = 1 := by
    rw [← Real.exp_add,show -(d:ℝ)/2+(d:ℝ)/2=0 by ring,Real.exp_zero]
  calc
    _ ≤ Real.exp (-(d:ℝ)/2)*(Real.exp (1/2)*Real.exp ((d:ℝ)/2)*(Nat.factorial N:ℝ)*2^N) := h₂
    _ = _ := by
      rw [show Real.exp (-(d:ℝ)/2)*(Real.exp (1/2)*Real.exp ((d:ℝ)/2)*(Nat.factorial N:ℝ)*2^N) =
        (Real.exp (-(d:ℝ)/2)*Real.exp ((d:ℝ)/2))*((Nat.factorial N:ℝ)*2^N*Real.exp (1/2)) by ring,he,one_mul]

end M12JacobiPropagation
#print axioms M12JacobiPropagation.entry_norm_le
#print axioms M12JacobiPropagation.entryMap_apply
#print axioms M12JacobiPropagation.exp_entry_series
#print axioms M12JacobiPropagation.generator_power_norm
#print axioms M12JacobiPropagation.generator_power_outside
#print axioms M12JacobiPropagation.exp_real_series
#print axioms M12JacobiPropagation.exp_real_summable
#print axioms M12JacobiPropagation.tilted_power
#print axioms M12JacobiPropagation.exponential_entry_bound
#print axioms M12JacobiPropagation.far_cone
#print axioms M12JacobiPropagation.far_cone_polynomial
