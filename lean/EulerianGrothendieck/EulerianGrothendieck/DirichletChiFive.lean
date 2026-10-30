import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Task E, part 1: `L(1, χ₅) = (2/√5) log φ`

`χ₅` is the actual quadratic character of `ZMod 5` (Mathlib's `quadraticChar (ZMod 5)`), read on
natural numbers; it is nontrivial and quadratic, hence the primitive quadratic character
modulo the prime `5`.  The value `L(1, χ₅)` is the sum of the conditionally convergent Dirichlet
series `∑_{n ≥ 1} χ₅(n)/n`, i.e. the limit of its partial sums in their natural order
(`dirichlet_chiFive_tendsto`).  No regrouping is assumed: we prove convergence of the
partial sums of length `5N` by an exact integral representation, and then of all partial sums.

* `chiFive_block`: the block `n = 5k, …, 5k+4` is `∫₀¹ x^{5k}(1 - x - x² + x³) dx`;
* `partial_sum_five_mul`: `S_{5N} = ∫₀¹ p - ∫₀¹ p x^{5N}`, `p = (1-x²)/(1+x+x²+x³+x⁴)`;
* `integral_p`: `∫₀¹ p = (2/√5) log φ`, by the explicit primitive
  `(1/√5) log((x²+φx+1)/(x²+(1-φ)x+1))`. -/

noncomputable section
open scoped BigOperators
open Finset Filter Topology intervalIntegral
namespace EulerianGrothendieck.Dirichlet

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The primitive quadratic character modulo `5`, as a function on `ℕ`. -/
def chiFive (n : ℕ) : ℝ := ((quadraticChar (ZMod 5) (n : ZMod 5) : ℤ) : ℝ)

theorem chiFive_isQuadratic : (quadraticChar (ZMod 5)).IsQuadratic := quadraticChar_isQuadratic _

theorem chiFive_nontrivial : quadraticChar (ZMod 5) ≠ 1 :=
  quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; norm_num)

theorem chiFive_mod (n : ℕ) : chiFive n = chiFive (n % 5) := by
  unfold chiFive
  rw [ZMod.natCast_mod]

theorem chiFive_zero : chiFive 0 = 0 := by simp [chiFive]
theorem chiFive_one : chiFive 1 = 1 := by simp [chiFive]
theorem chiFive_four : chiFive 4 = 1 := by
  unfold chiFive
  have h : ((4 : ℕ) : ZMod 5) = 2 ^ 2 := by decide
  rw [h, quadraticChar_sq_one' (by decide)]
  simp
theorem chiFive_two : chiFive 2 = -1 := by
  unfold chiFive
  have h : quadraticChar (ZMod 5) ((2 : ℕ) : ZMod 5) = -1 := by
    rw [quadraticChar_neg_one_iff_not_isSquare]
    unfold IsSquare; decide
  rw [h]; simp
theorem chiFive_three : chiFive 3 = -1 := by
  unfold chiFive
  have h : quadraticChar (ZMod 5) ((3 : ℕ) : ZMod 5) = -1 := by
    rw [quadraticChar_neg_one_iff_not_isSquare]
    unfold IsSquare; decide
  rw [h]; simp

theorem chiFive_abs_le (n : ℕ) : |chiFive n| ≤ 1 := by
  rw [chiFive_mod]
  have h : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize n % 5 = r at h ⊢
  interval_cases r <;>
    simp [chiFive_zero, chiFive_one, chiFive_two, chiFive_three, chiFive_four]

theorem chiFive_block_values (k j : ℕ) (hj : j < 5) : chiFive (5 * k + j) = chiFive j := by
  rw [chiFive_mod, chiFive_mod j]
  congr 1; omega

/-- The partial sums `S_n = ∑_{m < n} χ₅(m)/m` (the `m = 0` term is `0`). -/
def partialSum (n : ℕ) : ℝ := ∑ m ∈ range n, chiFive m / m

theorem inv_succ_eq_integral (m : ℕ) : (1:ℝ) / (m + 1) = ∫ x in (0:ℝ)..1, x ^ m := by
  rw [integral_pow]; simp

def qPoly (x : ℝ) : ℝ := 1 - x - x ^ 2 + x ^ 3

theorem chiFive_block (k : ℕ) :
    ∑ j ∈ range 5, chiFive (5 * k + j) / ((5 * k + j : ℕ) : ℝ) =
      ∫ x in (0:ℝ)..1, x ^ (5 * k) * qPoly x := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [chiFive_block_values k 0 (by norm_num), chiFive_block_values k 1 (by norm_num),
    chiFive_block_values k 2 (by norm_num), chiFive_block_values k 3 (by norm_num),
    chiFive_block_values k 4 (by norm_num), chiFive_zero, chiFive_one, chiFive_two,
    chiFive_three, chiFive_four]
  have hint : ∀ m : ℕ, IntervalIntegrable (fun x : ℝ => x ^ m) MeasureTheory.volume 0 1 :=
    fun m => (continuous_pow m).intervalIntegrable _ _
  have hq : (fun x : ℝ => x ^ (5 * k) * qPoly x) =
      fun x => x ^ (5*k) - x ^ (5*k+1) - x ^ (5*k+2) + x ^ (5*k+3) := by
    funext x; unfold qPoly; ring
  rw [hq, integral_add (((hint _).sub (hint _)).sub (hint _)) (hint _),
    integral_sub ((hint _).sub (hint _)) (hint _), integral_sub (hint _) (hint _)]
  rw [← inv_succ_eq_integral, ← inv_succ_eq_integral, ← inv_succ_eq_integral,
    ← inv_succ_eq_integral]
  push_cast
  ring

theorem partialSum_five_mul_eq (N : ℕ) :
    partialSum (5 * N) = ∑ k ∈ range N, ∫ x in (0:ℝ)..1, x ^ (5 * k) * qPoly x := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
    rw [show 5 * (N + 1) = 5 * N + 5 by ring, partialSum, Finset.sum_range_add, ← partialSum, ih,
      Finset.sum_range_succ (fun k => ∫ x in (0:ℝ)..1, x ^ (5 * k) * qPoly x) N, chiFive_block]

def denomPoly (x : ℝ) : ℝ := 1 + x + x ^ 2 + x ^ 3 + x ^ 4

theorem denomPoly_pos {x : ℝ} (hx : 0 ≤ x) : 0 < denomPoly x := by
  unfold denomPoly; positivity

/-- `p(x) = (1 - x²)/(1 + x + x² + x³ + x⁴)`. -/
def pFun (x : ℝ) : ℝ := (1 - x ^ 2) / denomPoly x

theorem block_geometric_identity (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ range N, x ^ (5 * k) * qPoly x = pFun x * (1 - x ^ (5 * N)) := by
  have hD := (denomPoly_pos hx).ne'
  unfold pFun
  rw [div_mul_eq_mul_div, eq_div_iff hD, ← Finset.sum_mul]
  have hg := mul_neg_geom_sum (x ^ 5) N
  simp_rw [← pow_mul] at hg
  have : qPoly x * denomPoly x = (1 - x ^ 2) * (1 - x ^ 5) := by unfold qPoly denomPoly; ring
  calc (∑ k ∈ range N, x ^ (5 * k)) * qPoly x * denomPoly x
      = (1 - x ^ 2) * ((1 - x ^ 5) * ∑ k ∈ range N, x ^ (5 * k)) := by
        rw [mul_assoc, this]; ring
    _ = (1 - x ^ 2) * (1 - x ^ (5 * N)) := by rw [hg]

theorem continuousOn_pFun : ContinuousOn pFun (Set.uIcc 0 1) := by
  unfold pFun
  apply ContinuousOn.div (by fun_prop) (by unfold denomPoly; fun_prop)
  intro x hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  exact (denomPoly_pos hx.1).ne'

theorem partialSum_five_mul (N : ℕ) :
    partialSum (5 * N) = (∫ x in (0:ℝ)..1, pFun x) - ∫ x in (0:ℝ)..1, pFun x * x ^ (5 * N) := by
  rw [partialSum_five_mul_eq, ← integral_finset_sum]
  · have hcongr : Set.EqOn (fun x => ∑ k ∈ range N, x ^ (5 * k) * qPoly x)
        (fun x => pFun x - pFun x * x ^ (5 * N)) (Set.uIcc 0 1) := by
      intro x hx
      rw [Set.uIcc_of_le zero_le_one] at hx
      show ∑ k ∈ range N, x ^ (5 * k) * qPoly x = pFun x - pFun x * x ^ (5 * N)
      rw [block_geometric_identity N hx.1]; ring
    rw [integral_congr hcongr, integral_sub (continuousOn_pFun.intervalIntegrable)
      ((continuousOn_pFun.mul (by fun_prop)).intervalIntegrable)]
  · intro k _
    exact (by unfold qPoly; fun_prop : Continuous fun x : ℝ => x ^ (5 * k) * qPoly x).intervalIntegrable _ _

theorem pFun_mem {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ pFun x ∧ pFun x ≤ 1 := by
  have hD := denomPoly_pos hx.1
  unfold pFun
  constructor
  · apply div_nonneg _ hD.le; nlinarith [hx.1, hx.2]
  · rw [div_le_one hD]; unfold denomPoly; nlinarith [hx.1, hx.2, pow_nonneg hx.1 3, pow_nonneg hx.1 4]

theorem tail_integral_bound (N : ℕ) :
    |∫ x in (0:ℝ)..1, pFun x * x ^ (5 * N)| ≤ 1 / (5 * N + 1) := by
  have h0 : 0 ≤ ∫ x in (0:ℝ)..1, pFun x * x ^ (5 * N) := by
    apply integral_nonneg zero_le_one
    intro x hx
    exact mul_nonneg (pFun_mem hx).1 (pow_nonneg hx.1 _)
  rw [abs_of_nonneg h0]
  have h1 : (∫ x in (0:ℝ)..1, pFun x * x ^ (5 * N)) ≤ ∫ x in (0:ℝ)..1, x ^ (5 * N) := by
    apply integral_mono_on zero_le_one
      ((continuousOn_pFun.mul (by fun_prop)).intervalIntegrable)
      ((continuous_pow _).intervalIntegrable _ _)
    intro x hx
    have := pFun_mem hx
    calc pFun x * x ^ (5 * N) ≤ 1 * x ^ (5 * N) :=
          mul_le_mul_of_nonneg_right this.2 (pow_nonneg hx.1 _)
      _ = x ^ (5 * N) := one_mul _
  rw [← inv_succ_eq_integral] at h1
  push_cast at h1
  exact h1

/-- The golden ratio. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
theorem sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
theorem sqrt5_lt_three : Real.sqrt 5 < 3 := by
  rw [show (3:ℝ) = Real.sqrt 9 by rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The quadratic factors `x² + φx + 1` and `x² + (1-φ)x + 1` of `1 + x + x² + x³ + x⁴`. -/
def facA (x : ℝ) : ℝ := x ^ 2 + phi * x + 1
def facB (x : ℝ) : ℝ := x ^ 2 + (1 - phi) * x + 1

theorem facA_pos {x : ℝ} (hx : 0 ≤ x) : 0 < facA x := by
  unfold facA phi; have := sqrt5_pos; positivity

theorem facB_pos (x : ℝ) : 0 < facB x := by
  unfold facB phi
  nlinarith [sq_nonneg (x + (1 - (1 + Real.sqrt 5) / 2) / 2), sqrt5_sq, sqrt5_pos, sqrt5_lt_three]

theorem fac_product (x : ℝ) : facA x * facB x = denomPoly x := by
  unfold facA facB denomPoly phi
  linear_combination (-(x ^ 2) / 4) * sqrt5_sq

/-- The primitive `F(x) = (1/√5) (log(x²+φx+1) - log(x²+(1-φ)x+1))`. -/
def primitiveF (x : ℝ) : ℝ := (1 / Real.sqrt 5) * (Real.log (facA x) - Real.log (facB x))

theorem hasDerivAt_primitiveF {x : ℝ} (hx : 0 ≤ x) : HasDerivAt primitiveF (pFun x) x := by
  have hA : HasDerivAt facA (2 * x + phi) x := by
    have h := ((hasDerivAt_pow 2 x).add ((hasDerivAt_id x).const_mul phi)).add_const 1
    simp only [id_eq, pow_one, Nat.cast_ofNat, Nat.add_one_sub_one, mul_one] at h
    exact h
  have hB : HasDerivAt facB (2 * x + (1 - phi)) x := by
    have h := ((hasDerivAt_pow 2 x).add ((hasDerivAt_id x).const_mul (1 - phi))).add_const 1
    simp only [id_eq, pow_one, Nat.cast_ofNat, Nat.add_one_sub_one, mul_one] at h
    exact h
  have hApos := facA_pos hx
  have hBpos := facB_pos x
  have hs := sqrt5_pos.ne'
  have h := ((hA.log hApos.ne').sub (hB.log hBpos.ne')).const_mul (1 / Real.sqrt 5)
  have hnum : (2 * x + phi) * facB x - facA x * (2 * x + (1 - phi)) = Real.sqrt 5 * (1 - x ^ 2) := by
    unfold facA facB phi; ring
  have key : 1 / Real.sqrt 5 * ((2 * x + phi) / facA x - (2 * x + (1 - phi)) / facB x) = pFun x := by
    rw [div_sub_div _ _ hApos.ne' hBpos.ne', hnum, pFun, ← fac_product, ← mul_div_assoc,
      ← mul_assoc, one_div_mul_cancel hs, one_mul]
  rw [← key]
  exact h

theorem integral_pFun : ∫ x in (0:ℝ)..1, pFun x = 2 / Real.sqrt 5 * Real.log phi := by
  rw [integral_eq_sub_of_hasDerivAt (f := primitiveF)
    (fun x hx => hasDerivAt_primitiveF (by rw [Set.uIcc_of_le zero_le_one] at hx; exact hx.1))
    continuousOn_pFun.intervalIntegrable]
  have hphi : 0 < phi := by unfold phi; have := sqrt5_pos; positivity
  have h2b : 0 < 1 ^ 2 + (1 - phi) * 1 + 1 := by unfold phi; linarith [sqrt5_lt_three]
  have h0 : primitiveF 0 = 0 := by simp [primitiveF, facA, facB]
  have h1 : primitiveF 1 = 2 / Real.sqrt 5 * Real.log phi := by
    unfold primitiveF facA facB
    have hkey : (1:ℝ) ^ 2 + phi * 1 + 1 = phi ^ 2 * (1 ^ 2 + (1 - phi) * 1 + 1) := by
      unfold phi; linear_combination ((Real.sqrt 5 - 3) / 8) * sqrt5_sq
    rw [hkey, Real.log_mul (pow_pos hphi 2).ne' h2b.ne', Real.log_pow]
    push_cast
    ring
  rw [h1, h0, sub_zero]

/-- Convergence along the partial sums of length `5N`. -/
theorem partialSum_five_mul_tendsto :
    Tendsto (fun N => partialSum (5 * N)) atTop (𝓝 (2 / Real.sqrt 5 * Real.log phi)) := by
  have h : Tendsto (fun N : ℕ => ∫ x in (0:ℝ)..1, pFun x * x ^ (5 * N)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => (5 * (N:ℝ) + 1)) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    refine squeeze_zero_norm (a := fun N : ℕ => 1 / (5 * (N:ℝ) + 1))
      (fun N => by rw [Real.norm_eq_abs]; exact tail_integral_bound N) ?_
    exact tendsto_const_nhds.div_atTop this
  have := (tendsto_const_nhds (x := ∫ x in (0:ℝ)..1, pFun x)).sub h
  rw [sub_zero] at this
  rw [← integral_pFun]
  exact this.congr (fun N => (partialSum_five_mul N).symm)

/-- **`L(1, χ₅) = (2/√5) log φ`**: the partial sums `∑_{m<n} χ₅(m)/m` converge, in their natural
order, to `(2/√5) log((1+√5)/2)`. -/
theorem dirichlet_chiFive_tendsto :
    Tendsto partialSum atTop (𝓝 (2 / Real.sqrt 5 * Real.log phi)) := by
  have hq : Tendsto (fun n : ℕ => n / 5) atTop atTop := Nat.tendsto_div_const_atTop (by norm_num)
  have hmain := partialSum_five_mul_tendsto.comp hq
  have herr : Tendsto (fun n => partialSum n - partialSum (5 * (n / 5))) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, 5 ≤ n → |partialSum n - partialSum (5 * (n / 5))| ≤ 4 / (5 * ((n/5 : ℕ):ℝ)) := by
      intro n hn
      have hq1 : 1 ≤ n / 5 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
      have hsplit : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
      have hr : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
      have hdiff : partialSum n - partialSum (5 * (n / 5)) =
          ∑ j ∈ range (n % 5), chiFive (5 * (n / 5) + j) / ((5 * (n / 5) + j : ℕ) : ℝ) := by
        have e : partialSum n = partialSum (5 * (n / 5)) +
            ∑ j ∈ range (n % 5), chiFive (5 * (n / 5) + j) / ((5 * (n / 5) + j : ℕ) : ℝ) := by
          conv_lhs => rw [hsplit]
          rw [partialSum, Finset.sum_range_add, ← partialSum]
        rw [e]; ring
      rw [hdiff]
      have hpos : (0:ℝ) < 5 * ((n/5 : ℕ):ℝ) := by
        have : (1:ℝ) ≤ ((n/5 : ℕ):ℝ) := by exact_mod_cast hq1
        linarith
      calc |∑ j ∈ range (n % 5), chiFive (5 * (n / 5) + j) / ((5 * (n / 5) + j : ℕ) : ℝ)|
          ≤ ∑ j ∈ range (n % 5), |chiFive (5 * (n / 5) + j) / ((5 * (n / 5) + j : ℕ) : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ range (n % 5), 1 / (5 * ((n/5 : ℕ):ℝ)) := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_div, Nat.abs_cast]
            have hden : 5 * ((n/5 : ℕ):ℝ) ≤ ((5 * (n / 5) + j : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
            calc |chiFive (5 * (n / 5) + j)| / ((5 * (n / 5) + j : ℕ) : ℝ)
                ≤ 1 / ((5 * (n / 5) + j : ℕ) : ℝ) :=
                  div_le_div_of_nonneg_right (chiFive_abs_le _) (Nat.cast_nonneg _)
              _ ≤ 1 / (5 * ((n/5 : ℕ):ℝ)) := one_div_le_one_div_of_le hpos hden
        _ = (n % 5 : ℕ) * (1 / (5 * ((n/5 : ℕ):ℝ))) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ 4 * (1 / (5 * ((n/5 : ℕ):ℝ))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : n % 5 ≤ 4 := by omega
            exact_mod_cast this
        _ = 4 / (5 * ((n/5 : ℕ):ℝ)) := by ring
    have hlim : Tendsto (fun n : ℕ => 4 / (5 * ((n/5 : ℕ):ℝ))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => 5 * ((n/5 : ℕ):ℝ)) atTop atTop :=
        ((tendsto_natCast_atTop_atTop).comp hq).const_mul_atTop (by norm_num)
      exact tendsto_const_nhds.div_atTop this
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 5] with n hn
    rw [Real.norm_eq_abs]; exact hb n hn
  have := hmain.add herr
  rw [add_zero] at this
  refine this.congr (fun n => ?_)
  simp only [Function.comp_apply]
  ring

/-- `L(1, χ₅)`, defined as the limit of the partial sums of the Dirichlet series. -/
def LOneChiFive : ℝ := limUnder atTop partialSum

theorem LOneChiFive_eq : LOneChiFive = 2 / Real.sqrt 5 * Real.log phi :=
  dirichlet_chiFive_tendsto.limUnder_eq

end EulerianGrothendieck.Dirichlet
