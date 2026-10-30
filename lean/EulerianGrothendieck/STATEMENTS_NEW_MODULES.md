# Statements of all new declarations (V170 handoff 2026-10-29)

## EulerianGrothendieck/DirichletChiFive.lean
### def `chiFive`
_The primitive quadratic character modulo `5`, as a function on `ℕ`._
```lean
def chiFive (n : ℕ) : ℝ
```
### theorem `chiFive_isQuadratic`
```lean
theorem chiFive_isQuadratic : (quadraticChar (ZMod 5)).IsQuadratic
```
### theorem `chiFive_nontrivial`
```lean
theorem chiFive_nontrivial : quadraticChar (ZMod 5) ≠ 1
```
### theorem `chiFive_mod`
```lean
theorem chiFive_mod (n : ℕ) : chiFive n = chiFive (n % 5)
```
### theorem `chiFive_zero`
```lean
theorem chiFive_zero : chiFive 0 = 0
```
### theorem `chiFive_one`
```lean
theorem chiFive_one : chiFive 1 = 1
```
### theorem `chiFive_four`
```lean
theorem chiFive_four : chiFive 4 = 1
```
### theorem `chiFive_two`
```lean
theorem chiFive_two : chiFive 2 = -1
```
### theorem `chiFive_three`
```lean
theorem chiFive_three : chiFive 3 = -1
```
### theorem `chiFive_abs_le`
```lean
theorem chiFive_abs_le (n : ℕ) : |chiFive n| ≤ 1
```
### theorem `chiFive_block_values`
```lean
theorem chiFive_block_values (k j : ℕ) (hj : j < 5) : chiFive (5 * k + j) = chiFive j
```
### def `partialSum`
_The partial sums `S_n = ∑_{m < n} χ₅(m)/m` (the `m = 0` term is `0`)._
```lean
def partialSum (n : ℕ) : ℝ
```
### theorem `inv_succ_eq_integral`
```lean
theorem inv_succ_eq_integral (m : ℕ) : (1:ℝ) / (m + 1) = ∫ x in (0:ℝ)..1, x ^ m
```
### def `qPoly`
```lean
def qPoly (x : ℝ) : ℝ
```
### theorem `chiFive_block`
```lean
theorem chiFive_block (k : ℕ) : ∑ j ∈ range 5, chiFive (5 * k + j) / ((5 * k + j : ℕ) : ℝ) = ∫ x in (0:ℝ)..1, x ^ (5 * k) * qPoly x
```
### theorem `partialSum_five_mul_eq`
```lean
theorem partialSum_five_mul_eq (N : ℕ) : partialSum (5 * N) = ∑ k ∈ range N, ∫ x in (0:ℝ)..1, x ^ (5 * k) * qPoly x
```
### def `denomPoly`
```lean
def denomPoly (x : ℝ) : ℝ
```
### theorem `denomPoly_pos`
```lean
theorem denomPoly_pos {x : ℝ} (hx : 0 ≤ x) : 0 < denomPoly x
```
### def `pFun`
_`p(x) = (1 - x²)/(1 + x + x² + x³ + x⁴)`._
```lean
def pFun (x : ℝ) : ℝ
```
### theorem `block_geometric_identity`
```lean
theorem block_geometric_identity (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : ∑ k ∈ range N, x ^ (5 * k) * qPoly x = pFun x * (1 - x ^ (5 * N))
```
### theorem `continuousOn_pFun`
```lean
theorem continuousOn_pFun : ContinuousOn pFun (Set.uIcc 0 1)
```
### theorem `partialSum_five_mul`
```lean
theorem partialSum_five_mul (N : ℕ) : partialSum (5 * N) = (∫ x in (0:ℝ)..1, pFun x) - ∫ x in (0:ℝ)..1, pFun x * x ^ (5 * N)
```
### theorem `pFun_mem`
```lean
theorem pFun_mem {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ pFun x ∧ pFun x ≤ 1
```
### theorem `tail_integral_bound`
```lean
theorem tail_integral_bound (N : ℕ) : |∫ x in (0:ℝ)..1, pFun x * x ^ (5 * N)| ≤ 1 / (5 * N + 1)
```
### def `phi`
_The golden ratio._
```lean
def phi : ℝ
```
### theorem `sqrt5_sq`
```lean
theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5
```
### theorem `sqrt5_pos`
```lean
theorem sqrt5_pos : 0 < Real.sqrt 5
```
### theorem `sqrt5_lt_three`
```lean
theorem sqrt5_lt_three : Real.sqrt 5 < 3
```
### def `facA`
_The quadratic factors `x² + φx + 1` and `x² + (1-φ)x + 1` of `1 + x + x² + x³ + x⁴`._
```lean
def facA (x : ℝ) : ℝ
```
### def `facB`
```lean
def facB (x : ℝ) : ℝ
```
### theorem `facA_pos`
```lean
theorem facA_pos {x : ℝ} (hx : 0 ≤ x) : 0 < facA x
```
### theorem `facB_pos`
```lean
theorem facB_pos (x : ℝ) : 0 < facB x
```
### theorem `fac_product`
```lean
theorem fac_product (x : ℝ) : facA x * facB x = denomPoly x
```
### def `primitiveF`
_The primitive `F(x) = (1/√5) (log(x²+φx+1) - log(x²+(1-φ)x+1))`._
```lean
def primitiveF (x : ℝ) : ℝ
```
### theorem `hasDerivAt_primitiveF`
```lean
theorem hasDerivAt_primitiveF {x : ℝ} (hx : 0 ≤ x) : HasDerivAt primitiveF (pFun x) x
```
### theorem `integral_pFun`
```lean
theorem integral_pFun : ∫ x in (0:ℝ)..1, pFun x = 2 / Real.sqrt 5 * Real.log phi
```
### theorem `partialSum_five_mul_tendsto`
_Convergence along the partial sums of length `5N`._
```lean
theorem partialSum_five_mul_tendsto : Tendsto (fun N => partialSum (5 * N)) atTop (𝓝 (2 / Real.sqrt 5 * Real.log phi))
```
### theorem `dirichlet_chiFive_tendsto`
_**`L(1, χ₅) = (2/√5) log φ`**: the partial sums `∑_{m<n} χ₅(m)/m` converge, in their natural order, to `(2/√5) log((1+√5)/2)`._
```lean
theorem dirichlet_chiFive_tendsto : Tendsto partialSum atTop (𝓝 (2 / Real.sqrt 5 * Real.log phi))
```
### def `LOneChiFive`
_`L(1, χ₅)`, defined as the limit of the partial sums of the Dirichlet series._
```lean
def LOneChiFive : ℝ
```
### theorem `LOneChiFive_eq`
```lean
theorem LOneChiFive_eq : LOneChiFive = 2 / Real.sqrt 5 * Real.log phi
```

## EulerianGrothendieck/DirichletChiFiveLFunction.lean
### theorem `for`
```lean
theorem for Dirichlet series, in a form that needs no measure theory: * with `S_i = ∑_{m ≤ i} χ₅(m)` (so `|S_i| ≤ 1`), summation by parts gives for every `σ ≥ 1` `∑_{i ≤ n} i^{-σ} χ₅(i) = n^{-σ} S_n + ∑_{i < n} (i^{-σ} - (i+1)^{-σ}) S_i` (`abel_partial`);
* the transformed series `A(σ) = ∑_i (i^{-σ} - (i+1)^{-σ}) S_i` is dominated by `8/(i+1)²` uniformly for `1 ≤ σ ≤ 2` (mean value theorem, `weight_diff_le`, `term_bound`), hence `A(σ) → A(1)` as `σ → 1⁺` (dominated convergence for series, `abelSeries_tendsto_one`);
* `A(1)` is the limit of the partial sums, i.e. `(2/√5) log φ` (`abelSeries_one`), and for `σ > 1` Mathlib's `LSeries` equals `A(σ)` (`LSeries_chiFive_eq`);
* `LFunction χ₅ σ = LSeries χ₅ σ` for `σ > 1` (`LFunction_eq_LSeries`) and `LFunction χ₅` is continuous at `1` because `χ₅ ≠ 1` (`differentiable_LFunction`), so the two limits agree. Main result: `LFunction_chiFive_one : LFunction χ₅ 1 = (2/√5) log φ` (unconditional). -/ noncomputable section
open scoped BigOperators
open Finset Filter Topology namespace EulerianGrothendieck.Dirichlet /-- `χ₅` as a `ℂ`-valued Dirichlet character modulo `5`. -/
def chiFiveChar : DirichletCharacter ℂ 5
```
### theorem `chiFiveChar_apply`
```lean
theorem chiFiveChar_apply (n : ℕ) : chiFiveChar (n : ZMod 5) = ((chiFive n : ℝ) : ℂ)
```
### theorem `chiFiveChar_zero`
```lean
theorem chiFiveChar_zero : chiFiveChar ((0 : ℕ) : ZMod 5) = 0
```
### theorem `chiFiveChar_ne_one`
```lean
theorem chiFiveChar_ne_one : chiFiveChar ≠ 1
```
### def `chiPartial`
_`S n = ∑_{m ≤ n} χ₅(m)`._
```lean
def chiPartial (n : ℕ) : ℝ
```
### theorem `chiPartial_zero`
```lean
theorem chiPartial_zero : chiPartial 0 = 0
```
### theorem `chiFive_block_sum`
```lean
theorem chiFive_block_sum (m : ℕ) : ∑ x ∈ range 5, chiFive (m + x) = 0
```
### theorem `chiPartial_add_five`
```lean
theorem chiPartial_add_five (n : ℕ) : chiPartial (n + 5) = chiPartial n
```
### theorem `chiPartial_mod`
```lean
theorem chiPartial_mod (n : ℕ) : chiPartial n = chiPartial (n % 5)
```
### theorem `chiPartial_abs_le`
```lean
theorem chiPartial_abs_le (n : ℕ) : |chiPartial n| ≤ 1
```
### theorem `abel_partial`
```lean
theorem abel_partial (σ : ℝ) (n : ℕ) : ∑ i ∈ range (n + 1), (i : ℝ) ^ (-σ) * chiFive i = (n : ℝ) ^ (-σ) * chiPartial n + ∑ i ∈ range n, ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * chiPartial i
```
### theorem `summable_bound`
```lean
theorem summable_bound : Summable (fun i : ℕ => 8 / ((i : ℝ) + 1) ^ 2)
```
### theorem `weight_diff_le`
_Mean value theorem: `i^{-σ} - (i+1)^{-σ} ≤ σ i^{-σ-1} ≤ 2/i²` for `1 ≤ σ ≤ 2`, `i ≥ 1`._
```lean
theorem weight_diff_le {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) {i : ℕ} (hi : 1 ≤ i) : (i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ) ≤ 2 / (i : ℝ) ^ 2
```
### theorem `term_bound`
```lean
theorem term_bound {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (i : ℕ) : ‖((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * chiPartial i‖ ≤ 8 / ((i : ℝ) + 1) ^ 2
```
### def `abelSeries`
_`A(σ) = ∑_i (i^{-σ} - (i+1)^{-σ}) S_i`._
```lean
def abelSeries (σ : ℝ) : ℝ
```
### theorem `abelSeries_hasSum`
```lean
theorem abelSeries_hasSum {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) : HasSum (fun i : ℕ => ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * chiPartial i) (abelSeries σ)
```
### theorem `partial_tendsto_abelSeries`
```lean
theorem partial_tendsto_abelSeries {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) : Tendsto (fun n : ℕ => ∑ i ∈ range n, (i : ℝ) ^ (-σ) * chiFive i) atTop (𝓝 (abelSeries σ))
```
### theorem `abelSeries_one`
_At `σ = 1` the transformed series is the limit of the partial sums of `∑ χ₅(n)/n`._
```lean
theorem abelSeries_one : abelSeries 1 = 2 / Real.sqrt 5 * Real.log phi
```
### theorem `term_eq`
```lean
theorem term_eq (σ : ℝ) (n : ℕ) : LSeries.term (fun m : ℕ => chiFiveChar m) (σ : ℂ) n = (((n : ℝ) ^ (-σ) * chiFive n : ℝ) : ℂ)
```
### theorem `LSeries_chiFive_eq`
```lean
theorem LSeries_chiFive_eq {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) : LSeries (fun m : ℕ => chiFiveChar m) (σ : ℂ) = (abelSeries σ : ℂ)
```
### theorem `LFunction_tendsto`
```lean
theorem LFunction_tendsto : Tendsto (fun σ : ℝ => DirichletCharacter.LFunction chiFiveChar (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (DirichletCharacter.LFunction chiFiveChar 1))
```
### theorem `abelSeries_tendsto_one`
```lean
theorem abelSeries_tendsto_one : Tendsto abelSeries (𝓝[>] (1 : ℝ)) (𝓝 (abelSeries 1))
```
### theorem `LFunction_chiFive_one`
_**`L(1, χ₅) = (2/√5) log φ`** for Mathlib's analytically continued Dirichlet L-function (Mathar, Table 22; OEIS A086466)._
```lean
theorem LFunction_chiFive_one : DirichletCharacter.LFunction chiFiveChar 1 = ((2 / Real.sqrt 5 * Real.log phi : ℝ) : ℂ)
```
### theorem `LFunction_chiFive_one'`
_The same value in the form of Mathar's Table 22: `2 log((1+√5)/2)/√5`._
```lean
theorem LFunction_chiFive_one' : DirichletCharacter.LFunction chiFiveChar 1 = ((2 * Real.log ((1 + Real.sqrt 5) / 2) / Real.sqrt 5 : ℝ) : ℂ)
```
### theorem `LFunction_chiFive_one_eq_LOneChiFive`
_`LFunction χ₅ 1` coincides with the limit of the partial sums `LOneChiFive`._
```lean
theorem LFunction_chiFive_one_eq_LOneChiFive : DirichletCharacter.LFunction chiFiveChar 1 = (LOneChiFive : ℂ)
```

## EulerianGrothendieck/ComplexArcsineDisk.lean
### def `sqrtOneSub`
```lean
def sqrtOneSub (z : ℂ) : ℂ
```
### def `H0`
_The holomorphic branch of `arcsin` near `D_B`._
```lean
def H0 (z : ℂ) : ℂ
```
### def `diskB`
_`D_B = {z : |z - i| ≤ 1/2}`._
```lean
def diskB : Set ℂ
```
### theorem `sqrtOneSub_sq`
```lean
theorem sqrtOneSub_sq (z : ℂ) : sqrtOneSub z ^ 2 = 1 - z ^ 2
```
### theorem `cpow_half_re_nonneg`
```lean
theorem cpow_half_re_nonneg (w : ℂ) : 0 ≤ (w ^ (1/2 : ℂ)).re
```
### theorem `one_sub_sq_re`
```lean
theorem one_sub_sq_re (z : ℂ) : (1 - z ^ 2).re = 1 - z.re ^ 2 + z.im ^ 2
```
### theorem `one_sub_sq_im`
```lean
theorem one_sub_sq_im (z : ℂ) : (1 - z ^ 2).im = -(2 * z.re * z.im)
```
### theorem `one_sub_sq_mem_slitPlane`
```lean
theorem one_sub_sq_mem_slitPlane {z : ℂ} (hz : 0 < z.im) : 1 - z ^ 2 ∈ slitPlane
```
### theorem `sqrtOneSub_ne_zero`
```lean
theorem sqrtOneSub_ne_zero {z : ℂ} (hz : 0 < z.im) : sqrtOneSub z ≠ 0
```
### theorem `branch_product`
_`(i z + s)(s - i z) = 1` with `s = (1 - z²)^{1/2}`._
```lean
theorem branch_product (z : ℂ) : (I * z + sqrtOneSub z) * (sqrtOneSub z - I * z) = 1
```
### theorem `branch_mem_slitPlane`
_`i z + (1 - z²)^{1/2}` lies in the slit plane, for every `z`._
```lean
theorem branch_mem_slitPlane (z : ℂ) : I * z + sqrtOneSub z ∈ slitPlane
```
### theorem `branch_ne_zero`
```lean
theorem branch_ne_zero (z : ℂ) : I * z + sqrtOneSub z ≠ 0
```
### theorem `sin_H0`
_`H0` inverts the sine: `sin (H0 z) = z` (for every `z`; in particular on `D_B`)._
```lean
theorem sin_H0 (z : ℂ) : Complex.sin (H0 z) = z
```
### theorem `hasDerivAt_H0`
_`H0'(z) = (1 - z²)^{-1/2}` on the open upper half-plane._
```lean
theorem hasDerivAt_H0 {z : ℂ} (hz : 0 < z.im) : HasDerivAt H0 (1 / sqrtOneSub z) z
```
### theorem `diskB_im`
```lean
theorem diskB_im {z : ℂ} (hz : z ∈ diskB) : 1/2 ≤ z.im
```
### theorem `diskB_coords`
```lean
theorem diskB_coords {z : ℂ} (hz : z ∈ diskB) : z.re ^ 2 + (z.im - 1) ^ 2 ≤ 1/4
```
### theorem `norm_one_sub_sq_ge`
_`|1 - z²| ≥ 5/4` on `D_B` (manuscript (eg:eq:lipschitz))._
```lean
theorem norm_one_sub_sq_ge {z : ℂ} (hz : z ∈ diskB) : 5/4 ≤ ‖1 - z ^ 2‖
```
### theorem `norm_sqrtOneSub_sq`
```lean
theorem norm_sqrtOneSub_sq (z : ℂ) : ‖sqrtOneSub z‖ ^ 2 = ‖1 - z ^ 2‖
```
### theorem `sqrt5_div_two_eq`
```lean
theorem sqrt5_div_two_eq : Real.sqrt 5 / 2 = Real.sqrt (5/4)
```
### theorem `norm_deriv_le`
```lean
theorem norm_deriv_le {z : ℂ} (hz : z ∈ diskB) : ‖1 / sqrtOneSub z‖ ≤ 2 / Real.sqrt 5
```
### theorem `half_I_mem`
```lean
theorem half_I_mem : (I / 2 : ℂ) ∈ diskB
```
### theorem `sqrtOneSub_half_I`
```lean
theorem sqrtOneSub_half_I : sqrtOneSub (I / 2) = (Real.sqrt 5 / 2 : ℝ)
```
### theorem `norm_deriv_half_I`
```lean
theorem norm_deriv_half_I : ‖1 / sqrtOneSub (I / 2)‖ = 2 / Real.sqrt 5
```
### theorem `deriv_H0`
```lean
theorem deriv_H0 {z : ℂ} (hz : z ∈ diskB) : deriv H0 z = 1 / sqrtOneSub z
```
### theorem `sup_norm_deriv_H0`
_**`sup_{z ∈ D_B} |H0'(z)| = 2/√5`**, attained at `z = i/2`._
```lean
theorem sup_norm_deriv_H0 : IsGreatest ((fun z => ‖deriv H0 z‖) '' diskB) (2 / Real.sqrt 5)
```
### theorem `sSup_norm_deriv_H0`
```lean
theorem sSup_norm_deriv_H0 : sSup ((fun z => ‖deriv H0 z‖) '' diskB) = 2 / Real.sqrt 5
```
### theorem `H0_lipschitz`
_Lipschitz upper bound on the convex disc `D_B`, by the mean value inequality._
```lean
theorem H0_lipschitz {z w : ℂ} (hz : z ∈ diskB) (hw : w ∈ diskB) : ‖H0 z - H0 w‖ ≤ 2 / Real.sqrt 5 * ‖z - w‖
```
### theorem `H0_lipschitz_sharp`
_**Sharpness**: every Lipschitz constant of `H0` on `D_B` is at least `2/√5`._
```lean
theorem H0_lipschitz_sharp {L : ℝ} (hL : ∀ z ∈ diskB, ∀ w ∈ diskB, ‖H0 z - H0 w‖ ≤ L * ‖z - w‖) : 2 / Real.sqrt 5 ≤ L
```
### theorem `H0_lipschitz_constant`
_The sharp Lipschitz constant: `2/√5` is the least `L` with `|H0 z - H0 w| ≤ L|z - w|` on `D_B`._
```lean
theorem H0_lipschitz_constant : IsLeast {L : ℝ | ∀ z ∈ diskB, ∀ w ∈ diskB, ‖H0 z - H0 w‖ ≤ L * ‖z - w‖} (2 / Real.sqrt 5)
```

## EulerianGrothendieck/GaussianFockBridge.lean
### def `rE`
_The manuscript's entire function `r_E(z) = ∫_{-1/2}^{1/2} e^{itz} dt`._
```lean
def rE (z : ℂ) : ℂ
```
### theorem `rE_eq_sin_div`
_`r_E(z) = sin(z/2)/(z/2)` for `z ≠ 0`: the manuscript's Eulerian sine-cardinal profile._
```lean
theorem rE_eq_sin_div {z : ℂ} (hz : z ≠ 0) : rE z = Complex.sin (z / 2) / (z / 2)
```
### theorem `rE_zero`
```lean
theorem rE_zero : rE 0 = 1
```
### def `fockDensity`
_The Gaussian density `(α/π) e^{-α|z|^2}` of the Fock weight `μ_α`._
```lean
def fockDensity (α : ℝ) (z : ℂ) : ℝ
```
### theorem `fockDensity_nonneg`
```lean
theorem fockDensity_nonneg {α : ℝ} (hα : 0 ≤ α) (z : ℂ) : 0 ≤ fockDensity α z
```
### theorem `continuous_fockDensity`
```lean
theorem continuous_fockDensity (α : ℝ) : Continuous (fockDensity α)
```
### theorem `measurable_mk`
```lean
theorem measurable_mk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
```
### theorem `integral_complex_eq_prod`
_Integrals over `ℂ` are integrals over `ℝ × ℝ` in the coordinates `(Re z, Im z)`._
```lean
theorem integral_complex_eq_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) : ∫ z, f z = ∫ p : ℝ × ℝ, f (⟨p.1, p.2⟩ : ℂ)
```
### theorem `integrable_complex_iff_prod`
```lean
theorem integrable_complex_iff_prod {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) : Integrable f ↔ Integrable (fun p : ℝ × ℝ => f (⟨p.1, p.2⟩ : ℂ))
```
### theorem `mk_norm_sq`
```lean
theorem mk_norm_sq (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2
```
### theorem `conj_mk`
```lean
theorem conj_mk (x y : ℝ) : conj (⟨x, y⟩ : ℂ) = (x:ℂ) - (y:ℂ) * I
```
### theorem `mk_eq`
```lean
theorem mk_eq (x y : ℝ) : (⟨x, y⟩ : ℂ) = (x:ℂ) + (y:ℂ) * I
```
### theorem `pairing_integrand_factor`
_Pointwise factorisation of the Gaussian pairing integrand in real coordinates._
```lean
theorem pairing_integrand_factor (α s t x y : ℝ) : cexp (I * (⟨x, y⟩ : ℂ) * s - I * conj (⟨x, y⟩ : ℂ) * t) * (fockDensity α ⟨x, y⟩ : ℂ) = ((α / Real.pi : ℝ) : ℂ) * (cexp (-(α:ℂ) * (x:ℂ) ^ 2 + (I * ((s:ℂ) - t)) * x + 0) * cexp (-(α:ℂ) * (y:ℂ) ^ 2 + (-((s:ℂ) + t)) * y + 0))
```
### theorem `gaussian_pairing`
_The Gaussian pairing: `∫_ℂ e^{i z s - i \bar z t} dμ_α(z) = e^{st/α}` for real `s, t`._
```lean
theorem gaussian_pairing {α : ℝ} (hα : 0 < α) (s t : ℝ) : ∫ z : ℂ, cexp (I * z * s - I * conj z * t) * (fockDensity α z : ℂ) = cexp ((s:ℂ) * (t:ℂ) / (α:ℂ))
```
### theorem `uniform_charFun`
_Characteristic function of one centred uniform variable, at complex argument._
```lean
theorem uniform_charFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ} (hU : Measurable U) (hlaw : μ.map U = V033.UniformSum.uniformLaw) (z : ℂ) : ∫ ω, cexp (I * z * (U ω : ℂ)) ∂μ = rE z
```
### theorem `sum_charFun`
_`E e^{i z S_M} = r_E(z)^M` for every complex `z`._
```lean
theorem sum_charFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (z : ℂ) (M : ℕ) : ∫ ω, cexp (I * z * ((∑ i ∈ range M, U i ω : ℝ) : ℂ)) ∂μ = rE z ^ M
```
### theorem `norm_sq_rE_pow`
_The squared modulus `|r_E(z)^M|^2` as a product-law expectation._
```lean
theorem norm_sq_rE_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (z : ℂ) (M : ℕ) : ((‖rE z ^ M‖ ^ 2 : ℝ) : ℂ) = ∫ xy, cexp (I * z * ((∑ i ∈ range M, U i xy.1 : ℝ) : ℂ) - I * conj z * ((∑ i ∈ range M, U i xy.2 : ℝ) : ℂ)) ∂μ.prod μ
```
### theorem `norm_rE_le`
_The bound `‖r_E(z)‖ ≤ e^{|Im z|/2}`._
```lean
theorem norm_rE_le (z : ℂ) : ‖rE z‖ ≤ Real.exp (|z.im| / 2)
```
### theorem `integrable_exp_neg_mul_sq_add_mul`
_One-dimensional integrability of `e^{-α y^2 + c y}`._
```lean
theorem integrable_exp_neg_mul_sq_add_mul {α : ℝ} (hα : 0 < α) (c : ℝ) : Integrable (fun y : ℝ => Real.exp (-α * y ^ 2 + c * y))
```
### theorem `integrable_exp_abs_im_mul_fockDensity`
_Integrability of `e^{C |Im z|}` against the Fock density._
```lean
theorem integrable_exp_abs_im_mul_fockDensity {α : ℝ} (hα : 0 < α) (C : ℝ) : Integrable (fun z : ℂ => Real.exp (C * |z.im|) * fockDensity α z)
```
### theorem `gaussian_fubini`
_Fubini for the Gaussian pairing of two bounded real random variables._
```lean
theorem gaussian_fubini {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν] {X Y : Ω' → ℝ} (hX : Measurable X) (hY : Measurable Y) (B : ℝ) (hXB : ∀ᵐ ω ∂ν, |X ω| ≤ B) (hYB : ∀ᵐ ω ∂ν, |Y ω| ≤ B) {α : ℝ} (hα : 0 < α) : ∫ z : ℂ, (∫ ω, cexp (I * z * (X ω : ℂ) - I * conj z * (Y ω : ℂ)) ∂ν) * (fockDensity α z : ℂ) = ∫ ω, cexp ((X ω : ℂ) * (Y ω : ℂ) / (α:ℂ)) ∂ν
```
### theorem `fock_norm_eq_probability_integral`
_**Theorem 9.2, first equality.**  For every `α > 0` and every `M`, `∫_ℂ |r_E(z)^M|^2 (α/π) e^{-α|z|^2} dA(z) = E exp(S_M T_M / α)`, with `T_M` the independent copy carried by the second factor of `μ.prod μ`._
```lean
theorem fock_norm_eq_probability_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) {α : ℝ} (hα : 0 < α) : ∫ z : ℂ, ‖rE z ^ M‖ ^ 2 * fockDensity α z = ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α) ∂μ.prod μ
```
### theorem `fock_norm_eq_moment_series`
_**Theorem 9.2, second equality**: the same norm equals the moment series `∑_k (μ_{2k}^{[M]})^2 / ((2k)! α^{2k})`, with `μ_n^{[M]} = E S_M^n`._
```lean
theorem fock_norm_eq_moment_series {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) {α : ℝ} (hα : 0 < α) : ∫ z : ℂ, ‖rE z ^ M‖ ^ 2 * fockDensity α z = ∑' k : ℕ, (∫ ω, (∑ i ∈ range M, U i ω) ^ (2*k) ∂μ) ^ 2 / (((2*k).factorial : ℝ) * α ^ (2*k))
```
### theorem `fock_norm_scaled_eq_uniformNormSeries`
_At the scale `α = c M` used throughout the asymptotic theory, the Fock norm is the certified series `uniformNormSeries M (1/(12c))`._
```lean
theorem fock_norm_scaled_eq_uniformNormSeries {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) {c : ℝ} (hc : 0 < c) (M : ℕ) (hM : M ≠ 0) : ∫ z : ℂ, ‖rE z ^ M‖ ^ 2 * fockDensity (c * M) z = uniformNormSeries M (1/(12*c))
```

## EulerianGrothendieck/FockVacuumProjection.lean
### def `fockMeasure`
_The Fock weight `dμ_α(z) = (α/π) e^{-α|z|²} dA(z)`._
```lean
def fockMeasure (α : ℝ) : Measure ℂ
```
### theorem `measurable_fockDensity_nnreal`
```lean
theorem measurable_fockDensity_nnreal (α : ℝ) : Measurable (fun z => Real.toNNReal (fockDensity α z))
```
### theorem `integral_fockMeasure`
```lean
theorem integral_fockMeasure {α : ℝ} (hα : 0 ≤ α) (g : ℂ → ℂ) : ∫ z, g z ∂fockMeasure α = ∫ z, (fockDensity α z : ℂ) * g z
```
### theorem `integral_fockMeasure_real`
```lean
theorem integral_fockMeasure_real {α : ℝ} (hα : 0 ≤ α) (g : ℂ → ℝ) : ∫ z, g z ∂fockMeasure α = ∫ z, g z * fockDensity α z
```
### theorem `integrable_fockDensity`
```lean
theorem integrable_fockDensity {α : ℝ} (hα : 0 < α) : Integrable (fockDensity α)
```
### theorem `integral_fockDensity`
```lean
theorem integral_fockDensity {α : ℝ} (hα : 0 < α) : ∫ z, fockDensity α z = 1
```
### theorem `fockMeasure_univ`
```lean
theorem fockMeasure_univ {α : ℝ} (hα : 0 < α) : fockMeasure α Set.univ = 1
```
### theorem `continuous_rE`
```lean
theorem continuous_rE : Continuous rE
```
### theorem `norm_rE_pow_sq_le`
```lean
theorem norm_rE_pow_sq_le (z : ℂ) (M : ℕ) : ‖rE z ^ M‖ ^ 2 ≤ Real.exp (M * |z.im|)
```
### theorem `memLp_rE_pow`
_`r_E^M ∈ L²(μ_α)`._
```lean
theorem memLp_rE_pow {α : ℝ} (hα : 0 < α) (M : ℕ) : MemLp (fun z => rE z ^ M) 2 (fockMeasure α)
```
### def `vacuum`
_The vacuum vector: the constant function `1` of `L²(μ_α)`._
```lean
def vacuum (α : ℝ) : Lp ℂ 2 (fockMeasure α)
```
### def `fockState`
_The Fock state `r_E^M` as an element of `L²(μ_α)` (for `α ≤ 0` a junk value)._
```lean
def fockState (α : ℝ) (M : ℕ) : Lp ℂ 2 (fockMeasure α)
```
### theorem `fockState_coe`
```lean
theorem fockState_coe {α : ℝ} (hα : 0 < α) (M : ℕ) : (fockState α M : ℂ → ℂ) =ᵐ[fockMeasure α] fun z => rE z ^ M
```
### theorem `vacuum_coe`
```lean
theorem vacuum_coe (α : ℝ) : (vacuum α : ℂ → ℂ) =ᵐ[fockMeasure α] fun _ => (1:ℂ)
```
### theorem `norm_vacuum`
```lean
theorem norm_vacuum {α : ℝ} (hα : 0 < α) : ‖vacuum α‖ = 1
```
### theorem `inner_vacuum_fockState`
_`⟪1, r_E^M⟫_{μ_α} = 1`._
```lean
theorem inner_vacuum_fockState {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) {α : ℝ} (hα : 0 < α) : inner ℂ (vacuum α) (fockState α M) = 1
```
### theorem `fockState_norm_sq`
_`‖r_E^M‖²_{μ_α} = E exp(S_M T_M/α)`._
```lean
theorem fockState_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) {α : ℝ} (hα : 0 < α) : ‖fockState α M‖ ^ 2 = ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α) ∂μ.prod μ
```
### def `normalizedFockState`
_The normalised state `ψ = r_E^M/‖r_E^M‖`._
```lean
def normalizedFockState (α : ℝ) (M : ℕ) : Lp ℂ 2 (fockMeasure α)
```
### theorem `fock_vacuum_probability`
_**Theorem 9.2, vacuum probability.**  The squared norm of the projection of the normalised state onto the vacuum line is `1/N_{E,M}(α)`, `N_{E,M}(α) = E exp(S_M T_M/α)`._
```lean
theorem fock_vacuum_probability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) {α : ℝ} (hα : 0 < α) : ‖normalizedFockState α M‖ = 1 ∧ ‖inner ℂ (vacuum α) (normalizedFockState α M)‖ ^ 2 = 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α) ∂μ.prod μ ∧ ‖(ℂ ∙ vacuum α).starProjection (normalizedFockState α M)‖ ^ 2 = 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α) ∂μ.prod μ
```
### def `fockVacuumProbability`
_The Fock vacuum probability `p_{E,M}(α) = ‖P_vac ψ‖²`, defined intrinsically in `L²(μ_α)`._
```lean
def fockVacuumProbability (α : ℝ) (M : ℕ) : ℝ
```
### theorem `fock_vacuum_all_orders`
_At the scale `α = c M` with `c > 1/12`, the intrinsic Fock vacuum probability satisfies the certified all-order expansion (constant independent of `M`)._
```lean
theorem fock_vacuum_all_orders {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : 1/12 < c) (R : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 → |fockVacuumProbability (c * M) M - ∑ r ∈ range (R+1), uniformVacuumCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1)
```
### theorem `fock_norm_all_orders`
_Likewise for the Fock norm itself._
```lean
theorem fock_norm_all_orders {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : 1/12 < c) (R : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 → |‖fockState (c * M) M‖ ^ 2 - ∑ r ∈ range (R+1), uniformNormCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1)
```

## EulerianGrothendieck/CriticalSubcriticalVacuum.lean
### theorem `uniform_exponential_integral_hasSum`
_`HasSum` form of the exact series, valid for every real `t` and every `M ≥ 1`._
```lean
theorem uniform_exponential_integral_hasSum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) (hM : M ≠ 0) (t : ℝ) : HasSum (fun k => binomialWeight t k * (uniformMomentRatio M k) ^ 2) (∫ xy, Real.exp (t * (standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2)) ∂μ.prod μ)
```
### def `have`
```lean
def have hZ : Measurable Z
```
### def `have`
```lean
def have hB : 0 ≤ B
```
### theorem `raw_uniform_kernel_hasSum`
_The same identity at the raw scale `α = c M`, for every `c ≠ 0`._
```lean
theorem raw_uniform_kernel_hasSum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : c ≠ 0) (M : ℕ) (hM : M ≠ 0) : HasSum (fun k => binomialWeight (1/(12*c)) k * (uniformMomentRatio M k) ^ 2) (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ)
```
### theorem `centralCoefficient_ge`
```lean
theorem centralCoefficient_ge (k : ℕ) : 1 / (2 * ((k:ℝ) + 1)) ≤ centralCoefficient k
```
### theorem `centralCoefficient_partial_unbounded`
_The partial sums of `binom(2k,k)/4^k` are unbounded._
```lean
theorem centralCoefficient_partial_unbounded : Tendsto (fun n => ∑ k ∈ range n, centralCoefficient k) atTop atTop
```
### theorem `binomialWeight_ge_central`
```lean
theorem binomialWeight_ge_central (t : ℝ) (ht : 1 ≤ t) (k : ℕ) : centralCoefficient k ≤ binomialWeight t k
```
### theorem `uniformMomentRatio_tendsto_one`
```lean
theorem uniformMomentRatio_tendsto_one (k : ℕ) : Tendsto (fun M : ℕ => uniformMomentRatio M k) atTop (nhds 1)
```
### theorem `uniform_norm_lower_bound_divergence`
_Divergence of the exact series at fixed `t ≥ 1`, by finite partial sums._
```lean
theorem uniform_norm_lower_bound_divergence (N : ℕ → ℝ) (t : ℝ) (ht : 1 ≤ t) (hN : ∀ M : ℕ, M ≠ 0 → HasSum (fun k => binomialWeight t k * (uniformMomentRatio M k) ^ 2) (N M)) : Tendsto N atTop atTop
```
### theorem `critical_subcritical_norm_tendsto_atTop`
_**Theorem 9.6, branch `0 < c ≤ 1/12`**: `N_M(c) = E exp(S_M T_M/(cM)) → +∞`._
```lean
theorem critical_subcritical_norm_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc0 : 0 < c) (hc : c ≤ 1/12) : Tendsto (fun M : ℕ => ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ) atTop atTop
```
### theorem `critical_subcritical_vacuum_tendsto_zero`
_**Theorem 9.6, branch `0 < c ≤ 1/12`**: the vacuum probability `1/N_M(c) → 0`._
```lean
theorem critical_subcritical_vacuum_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc0 : 0 < c) (hc : c ≤ 1/12) : Tendsto (fun M : ℕ => 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ) atTop (nhds 0)
```

## EulerianGrothendieck/UniformParameterVacuum.lean
### theorem `polyAbsEval_trunc`
```lean
theorem polyAbsEval_trunc (f : PowerSeries ℝ) (n : ℕ) : polyAbsEval (PowerSeries.trunc n f) 1 = ∑ r ∈ range n, |PowerSeries.coeff r f|
```
### theorem `polyAbsEval_add_le`
```lean
theorem polyAbsEval_add_le (p q : ℝ[X]) : polyAbsEval (p + q) 1 ≤ polyAbsEval p 1 + polyAbsEval q 1
```
### theorem `polyAbsEval_neg`
```lean
theorem polyAbsEval_neg (p : ℝ[X]) (h : ℝ) : polyAbsEval (-p) h = polyAbsEval p h
```
### theorem `polyAbsEval_eq_sum_support`
```lean
theorem polyAbsEval_eq_sum_support (p : ℝ[X]) : polyAbsEval p 1 = ∑ j ∈ p.support, |p.coeff j|
```
### theorem `polyAbsEval_mul_le`
```lean
theorem polyAbsEval_mul_le (p q : ℝ[X]) : polyAbsEval (p * q) 1 ≤ polyAbsEval p 1 * polyAbsEval q 1
```
### theorem `inverseSeriesCoefficient_bound`
_Uniform growth bound for the coefficients of the inverse power series._
```lean
theorem inverseSeriesCoefficient_bound (b : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A) (R : ℕ) (hb0 : 1 ≤ |b 0|) (hb : ∀ j, j ≤ R → |b j| ≤ A) : ∀ r, r ≤ R → |inverseSeriesCoefficient b r| ≤ (A + 1) ^ r
```
### theorem `reciprocal_uniform_remainder`
_General parameter-uniform all-order inversion.  The hypotheses are a uniform lower bound `N ≥ 1`, `|b_0| ≥ 1`, a uniform bound for the first `R+1` coefficients and a uniform remainder for `N` itself; nothing about `1/N` is assumed._
```lean
theorem reciprocal_uniform_remainder {ι : Type*} (N : ι → ℕ → ℝ) (b : ι → ℕ → ℝ) (R : ℕ) (A : ℝ) (hA : 0 ≤ A) (hN : ∀ i M, M ≠ 0 → 1 ≤ N i M) (hb0 : ∀ i, 1 ≤ |b i 0|) (hb : ∀ i j, j ≤ R → |b i j| ≤ A) (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ i M, M ≠ 0 → |N i M - ∑ r ∈ range (R+1), b i r/(M:ℝ)^r| ≤ C/(M:ℝ)^(R+1)) : ∃ K : ℝ, 0 ≤ K ∧ ∀ i M, M ≠ 0 → |1/(N i M) - ∑ r ∈ range (R+1), inverseSeriesCoefficient (b i) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1)
```
### theorem `uniformNormCoefficient_uniform_bound`
_Uniform bound for the norm coefficients `A_r(t)`, `0 < t ≤ T < 1`._
```lean
theorem uniformNormCoefficient_uniform_bound (T : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (r : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 < t → t ≤ T → |uniformNormCoefficient t r| ≤ A
```
### theorem `uniformVacuumSeries_uniform_parameters`
_**Uniform vacuum remainder in the normalised variable** `t = 1/(12c)`, `0 < t ≤ T < 1`._
```lean
theorem uniformVacuumSeries_uniform_parameters (T : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (R : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ T → ∀ M : ℕ, M ≠ 0 → |1/(uniformNormSeries M t) - ∑ r ∈ range (R+1), uniformVacuumCoefficient t r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1)
```
### theorem `raw_uniform_vacuum_uniform_parameters`
_**Task I.**  For every `c0 > 1/12` and `R`, a single constant `K(c0,R)` bounds the reciprocal remainder of the actual probability integral for all `c ≥ c0` and `M ≥ 1`._
```lean
theorem raw_uniform_vacuum_uniform_parameters {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c0 : ℝ) (hc0 : 1/12 < c0) (R : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, c0 ≤ c → ∀ M : ℕ, M ≠ 0 → |1/(∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/ (c*(M:ℝ))) ∂μ.prod μ) - ∑ r ∈ range (R+1), uniformVacuumCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1)
```

## EulerianGrothendieck/CatalanLipschitzDirichlet.lean
### def `catalanB`
_The binomial generating function `B(x) = ∑ binom(2n,n) xⁿ`, as a formal power series._
```lean
def catalanB : PowerSeries ℝ
```
### def `theta`
_The Euler operator `Θ = x d/dx` on formal power series._
```lean
def theta (f : PowerSeries ℝ) : PowerSeries ℝ
```
### def `evalSeries`
_Evaluation of a power series by its coefficient series._
```lean
def evalSeries (f : PowerSeries ℝ) (x : ℝ) : ℝ
```
### theorem `coeff_theta`
```lean
theorem coeff_theta (f : PowerSeries ℝ) (n : ℕ) : PowerSeries.coeff n (theta f) = n * PowerSeries.coeff n f
```
### theorem `coeff_catalanB`
```lean
theorem coeff_catalanB (n : ℕ) : PowerSeries.coeff n catalanB = (n.centralBinom : ℝ)
```
### theorem `central_term`
```lean
theorem central_term (n : ℕ) (x : ℝ) : (n.centralBinom : ℝ) * x ^ n = centralCoefficient n * (4 * x) ^ n
```
### theorem `sqrt_four_fifths`
```lean
theorem sqrt_four_fifths : Real.sqrt (1 - 1/5) = 2 / Real.sqrt 5
```
### theorem `catalanB_hasSum`
```lean
theorem catalanB_hasSum : HasSum (fun n => PowerSeries.coeff n catalanB * (1/20 : ℝ) ^ n) (Real.sqrt 5 / 2)
```
### theorem `catalanB_value`
_**`B(1/20) = √5/2`**._
```lean
theorem catalanB_value : evalSeries catalanB (1/20) = Real.sqrt 5 / 2
```
### theorem `catalanTheta_value`
_**`[(Θ² - Θ)B](1/20) = 3√5/128`**._
```lean
theorem catalanTheta_value : evalSeries (theta (theta catalanB) - theta catalanB) (1/20) = 3 * Real.sqrt 5 / 128
```
### def `cL`
_The arithmetic scale `c_L = √5/12`._
```lean
def cL : ℝ
```
### theorem `cL_eq`
```lean
theorem cL_eq : cL = evalSeries catalanB (1/20) / 6
```
### theorem `catalan_lipschitz_dirichlet_bridge`
_**Proposition 10.1, boxed identity**: `B(1/20) = (sup_{z∈D_B}|H0'(z)|)⁻¹ = log φ / L(1,χ₅) = √5/2`._
```lean
theorem catalan_lipschitz_dirichlet_bridge : evalSeries catalanB (1/20) = (sSup ((fun z => ‖deriv H0 z‖) '' diskB))⁻¹ ∧ (sSup ((fun z => ‖deriv H0 z‖) '' diskB))⁻¹ = Real.log phi / LOneChiFive ∧ Real.log phi / LOneChiFive = Real.sqrt 5 / 2
```
### theorem `uniformVacuumCoefficient_zero`
```lean
theorem uniformVacuumCoefficient_zero (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : uniformVacuumCoefficient t 0 = Real.sqrt (1 - t ^ 2)
```
### theorem `vacuum_limit_cL`
_**`p_∞(c_L) = 2/√5 = 1/B(1/20)`**: the actual vacuum probability `1/N_M(c_L)` converges._
```lean
theorem vacuum_limit_cL {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) : Tendsto (fun M : ℕ => 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (cL * (M:ℝ))) ∂μ.prod μ) atTop (𝓝 (1 / evalSeries catalanB (1/20)))
```
### theorem `fock_vacuum_limit_cL`
_The same limit for the intrinsic Fock vacuum probability `p_{E,M}(c_L M)`._
```lean
theorem fock_vacuum_limit_cL {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) : Tendsto (fun M : ℕ => fockVacuumProbability (cL * M) M) atTop (𝓝 (1 / evalSeries catalanB (1/20)))
```

## EulerianGrothendieck/FockCorollaries.lean
### theorem `fockVacuumProbability_eq`
```lean
theorem fockVacuumProbability_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) {c : ℝ} (hc : 0 < c) (M : ℕ) (hM : M ≠ 0) : fockVacuumProbability (c * M) M = 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ
```
### def `vacuumLimit`
_The limiting vacuum curve `p_∞(c)`._
```lean
def vacuumLimit (c : ℝ) : ℝ
```
### theorem `fock_vacuum_threshold_limit`
_**Theorem 9.6** for the intrinsic Fock vacuum probability, for every `c > 0`._
```lean
theorem fock_vacuum_threshold_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : 0 < c) : Tendsto (fun M : ℕ => fockVacuumProbability (c * M) M) atTop (𝓝 (vacuumLimit c))
```
### theorem `fock_vacuum_uniform_parameters`
_**Task I for the Fock vacuum probability**: uniform in `c ≥ c0 > 1/12`._
```lean
theorem fock_vacuum_uniform_parameters {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c0 : ℝ) (hc0 : 1/12 < c0) (R : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, c0 ≤ c → ∀ M : ℕ, M ≠ 0 → |fockVacuumProbability (c * M) M - ∑ r ∈ range (R+1), uniformVacuumCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1)
```

## EulerianGrothendieck/BilinearScalarBridge.lean
### def `bilinearScalarValues`
_The values `|a^T A b|` for `a, b` in the closed unit polydisc._
```lean
def bilinearScalarValues {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Set ℝ
```
### def `bilinearScalarNorm`
_`g_ℂ(A) = sup_{|a_i|,|b_j| ≤ 1} |a^T A b|`._
```lean
def bilinearScalarNorm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : ℝ
```
### theorem `coordinate_unimodular_step`
_Coordinatewise step: the convex function `u ↦ ‖T u‖²` does not decrease when one coordinate in the closed disc is moved to a suitable point of the unit circle._
```lean
theorem coordinate_unimodular_step (T : FourSpace →ₗ[ℂ] FourSpace) (u : FourSpace) (j : Fin 4) (hj : ‖u j‖ ≤ 1) : ∃ u' : FourSpace, ‖u' j‖ = 1 ∧ (∀ i, i ≠ j → u' i = u i) ∧ ‖T u‖ ^ 2 ≤ ‖T u'‖ ^ 2
```
### theorem `exists_torus_ge`
_Every point of the closed polydisc is dominated by a point of the torus._
```lean
theorem exists_torus_ge (T : FourSpace →ₗ[ℂ] FourSpace) (u : FourSpace) (hu : ∀ i, ‖u i‖ ≤ 1) : ∃ t : FourSpace, IsTorusPoint t ∧ ‖T u‖ ^ 2 ≤ ‖T t‖ ^ 2
```
### theorem `polydisk_projection_le`
_On the polydisc, `‖K u‖²` is bounded by the torus maximum `projectionScalarNorm`._
```lean
theorem polydisk_projection_le (U : Submodule ℂ FourSpace) (u : FourSpace) (hu : ∀ i, ‖u i‖ ≤ 1) : ‖U.starProjection u‖ ^ 2 ≤ projectionScalarNorm U
```
### theorem `bilinear_eq_inner`
_`a^T A b` is the Euclidean inner product of `conj a` with `A b`._
```lean
theorem bilinear_eq_inner (A : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4 → ℂ) : a ⬝ᵥ (A *ᵥ b) = inner ℂ (WithLp.toLp 2 (star a) : FourSpace) (A.toEuclideanLin (WithLp.toLp 2 b : FourSpace))
```
### theorem `explicit_bilinear_value_le`
```lean
theorem explicit_bilinear_value_le (e : ℝ) (z : ℂ) (a b : Fin 4 → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ j, ‖b j‖ ≤ 1) : ‖a ⬝ᵥ (explicitFrameProjector e z *ᵥ b)‖ ≤ projectionScalarNorm (frameSubspace e z)
```
### theorem `explicit_bilinearScalarValues_bddAbove`
```lean
theorem explicit_bilinearScalarValues_bddAbove (e : ℝ) (z : ℂ) : BddAbove (bilinearScalarValues (explicitFrameProjector e z))
```
### theorem `torus_value_mem_bilinear`
_The torus quadratic value `u^* P u = ‖P u‖²` is a bilinear value with `a = conj u`, `b = u`._
```lean
theorem torus_value_mem_bilinear (e : ℝ) (z : ℂ) (u : FourSpace) (hu : IsTorusPoint u) : ‖(frameSubspace e z).starProjection u‖ ^ 2 ∈ bilinearScalarValues (explicitFrameProjector e z)
```
### theorem `bilinearScalarNorm_explicit`
_**`g_ℂ(P) = max_{|u_j|=1} u^* P u`** for the explicit projector `P = V^*(VV^*)^{-1}V`._
```lean
theorem bilinearScalarNorm_explicit (e : ℝ) (z : ℂ) : bilinearScalarNorm (explicitFrameProjector e z) = explicitFrameScalarNorm e z
```
### theorem `bilinearScalarNorm_explicit_attained`
_The supremum defining `g_ℂ(P)` is a maximum._
```lean
theorem bilinearScalarNorm_explicit_attained (e : ℝ) (z : ℂ) : ∃ a b : Fin 4 → ℂ, (∀ i, ‖a i‖ ≤ 1) ∧ (∀ j, ‖b j‖ ≤ 1) ∧ bilinearScalarNorm (explicitFrameProjector e z) = ‖a ⬝ᵥ (explicitFrameProjector e z *ᵥ b)‖
```

## EulerianGrothendieck/VectorOptimum.lean
### def `RowNormalized`
_Every row has Euclidean norm at most one._
```lean
def RowNormalized {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : Prop
```
### def `bilinearVectorValues`
```lean
def bilinearVectorValues {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : Set ℝ
```
### def `bilinearVectorNorm`
_`q_ℂ(P) = sup_{n, A, B row-normalised} |Tr(B^* P A)|`._
```lean
def bilinearVectorNorm {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : ℝ
```
### def `matrixColumn`
_The `k`-th column of a `4 × n` matrix as a vector of `ℂ^4`._
```lean
def matrixColumn {n : ℕ} (A : Matrix (Fin 4) (Fin n) ℂ) (k : Fin n) : FourSpace
```
### theorem `trace_eq_sum_inner`
```lean
theorem trace_eq_sum_inner {n : ℕ} (P : Matrix (Fin 4) (Fin 4) ℂ) (A B : Matrix (Fin 4) (Fin n) ℂ) : (B.conjTranspose * P * A).trace = ∑ k, inner ℂ (matrixColumn B k) (P.toEuclideanLin (matrixColumn A k))
```
### theorem `norm_starProjection_le'`
```lean
theorem norm_starProjection_le' (U : Submodule ℂ FourSpace) (u : FourSpace) : ‖U.starProjection u‖ ≤ ‖u‖
```
### theorem `matrixColumn_norm_sq_sum`
```lean
theorem matrixColumn_norm_sq_sum {n : ℕ} (A : Matrix (Fin 4) (Fin n) ℂ) : ∑ k, ‖matrixColumn A k‖ ^ 2 = ∑ i, ∑ k, ‖A i k‖ ^ 2
```
### theorem `rowNormalized_sum_le`
```lean
theorem rowNormalized_sum_le {n : ℕ} {A : Matrix (Fin 4) (Fin n) ℂ} (hA : RowNormalized A) : ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 4
```
### theorem `explicit_vector_value_le`
_`|Tr(B^* P A)| ≤ 4` for row-normalised `A, B`, since `P` is an orthogonal projection._
```lean
theorem explicit_vector_value_le (e : ℝ) (z : ℂ) {n : ℕ} (A B : Matrix (Fin 4) (Fin n) ℂ) (hA : RowNormalized A) (hB : RowNormalized B) : ‖(B.conjTranspose * explicitFrameProjector e z * A).trace‖ ≤ 4
```
### theorem `explicitFrameProjector_mul_frameMatrix`
_`P V^* = V^*` for `P = V^*(VV^*)^{-1}V`; in the code `V^*` is `frameMatrix e z`._
```lean
theorem explicitFrameProjector_mul_frameMatrix (e : ℝ) (z : ℂ) : explicitFrameProjector e z * frameMatrix e z = frameMatrix e z
```
### theorem `frameMatrix_row_norm_sq`
```lean
theorem frameMatrix_row_norm_sq (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) (i : Fin 4) : ∑ k, ‖frameMatrix e z i k‖ ^ 2 = 1
```
### theorem `frameMatrix_rowNormalized`
```lean
theorem frameMatrix_rowNormalized (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) : RowNormalized (frameMatrix e z)
```
### theorem `frameMatrix_trace_value`
_`Tr(V P V^*) = Tr K = 4`._
```lean
theorem frameMatrix_trace_value (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) : ((frameMatrix e z).conjTranspose * explicitFrameProjector e z * frameMatrix e z).trace = 4
```
### theorem `bilinearVectorNorm_explicit`
_**`q_ℂ(P) = 4`**._
```lean
theorem bilinearVectorNorm_explicit (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) : bilinearVectorNorm (explicitFrameProjector e z) = 4
```
### theorem `one_le_explicitFrameScalarNorm`
_A crude lower bound `g(P) ≥ 1`, from the range vector `(1,0,e,e)`._
```lean
theorem one_le_explicitFrameScalarNorm (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) : 1 ≤ explicitFrameScalarNorm e z
```
### theorem `explicitFrameScalarNorm_pos`
```lean
theorem explicitFrameScalarNorm_pos (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) : 0 < explicitFrameScalarNorm e z
```
### def `bilinearRatio`
_The optimal ratio `𝒬 = q_ℂ(P)/g_ℂ(P)` for the specified coefficient matrix._
```lean
def bilinearRatio (e : ℝ) (z : ℂ) : ℝ
```
### theorem `bilinearRatio_explicit`
_**`q_ℂ(P)/g_ℂ(P) = 4/g(P)`**._
```lean
theorem bilinearRatio_explicit (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) : bilinearRatio e z = 4 / explicitFrameScalarNorm e z
```
### theorem `bilinearRatio_eulerian`
_At the Eulerian phase the bilinear ratio is the certified `frameGrothendieckRatio`._
```lean
theorem bilinearRatio_eulerian (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : bilinearRatio (Real.sqrt p) eulerianPhase = frameGrothendieckRatio p
```
### theorem `criticalVacuum_mem`
```lean
theorem criticalVacuum_mem (h : ℝ) (hh : 0 < h) : 0 ≤ criticalVacuum h ∧ criticalVacuum h ≤ 1
```
### theorem `bilinear_ratio_critical_law`
_The certified critical law, for the bilinear ratio `q_ℂ(P)/g_ℂ(P)` itself._
```lean
theorem bilinear_ratio_critical_law : Filter.Tendsto (fun h => (bilinearRatio (Real.sqrt (criticalVacuum h)) eulerianPhase - 1) / Real.sqrt h) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt 6 / (Real.pi ^ 2 + 1)))
```
### def `SatisfiesComplexGrothendieck`
_The finite complex Grothendieck inequality with constant `K`, for matrices of every size. This is an independent definition: it does not mention the matrix `P` or its ratio._
```lean
def SatisfiesComplexGrothendieck (K : ℝ) : Prop
```
### def `complexGrothendieckConstant`
_`K_G^ℂ`, the infimum of the admissible constants.  (Grothendieck's theorem, i.e. that admissible constants exist, is classical and is not formalised here.)_
```lean
def complexGrothendieckConstant : ℝ
```
### theorem `bilinearRatio_le_of_grothendieck`
_`𝒬(p) ≤ K` for every admissible Grothendieck constant `K`._
```lean
theorem bilinearRatio_le_of_grothendieck (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) {K : ℝ} (hK : SatisfiesComplexGrothendieck K) : bilinearRatio e z ≤ K
```
### theorem `bilinearRatio_le_complexGrothendieckConstant`
_`𝒬(p) ≤ K_G^ℂ`, under the (classical, unformalised) existence of an admissible constant._
```lean
theorem bilinearRatio_le_complexGrothendieckConstant (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) (hex : ∃ K, SatisfiesComplexGrothendieck K) : bilinearRatio e z ≤ complexGrothendieckConstant
```

## EulerianGrothendieck/ExposedCorrelation.lean
### def `correlationElliptope`
_The complex correlation elliptope of order four._
```lean
def correlationElliptope : Set (Matrix (Fin 4) (Fin 4) ℂ)
```
### def `∧`
```lean
def ∧ ∀ i, X i i = 1} /-- `K = V^*V = W W^*`. -/
def frameGram (e : ℝ) (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ
```
### theorem `normSq_frame_coordinate`
```lean
theorem normSq_frame_coordinate (e s : ℝ) (a b : ℂ) : Complex.normSq ((e:ℂ) * a + (s:ℂ) * b) = e^2 * Complex.normSq a + s^2 * Complex.normSq b + 2 * e * s * (a * conj b).re
```
### theorem `frameVector_coords`
_The four coordinates of a vector of `ran V^*`._
```lean
theorem frameVector_coords (e : ℝ) (z a b : ℂ) : frameVector e z a b 0 = a ∧ frameVector e z a b 1 = b ∧ frameVector e z a b 2 = (e:ℂ) * a + (Real.sqrt (1 - e^2):ℂ) * b ∧ frameVector e z a b 3 = (e:ℂ) * a + (Real.sqrt (1 - e^2):ℂ) * star z * b
```
### theorem `explicitFrameScalarNorm_lt_four`
_**Strictness**: `g(P) < 4` when `0 < p < 1` and `sin ϑ ≠ 0`._
```lean
theorem explicitFrameScalarNorm_lt_four (e : ℝ) (z : ℂ) (he0 : 0 < e) (he1 : e < 1) (hz : ‖z‖ = 1) (hzi : z.im ≠ 0) : explicitFrameScalarNorm e z < 4
```
### theorem `bilinearRatio_gt_one`
_`𝒬(p) = q_ℂ(P)/g_ℂ(P) > 1` under the same hypotheses._
```lean
theorem bilinearRatio_gt_one (e : ℝ) (z : ℂ) (he0 : 0 < e) (he1 : e < 1) (hz : ‖z‖ = 1) (hzi : z.im ≠ 0) : 1 < bilinearRatio e z
```
### theorem `frameGram_inv_hermitian`
```lean
theorem frameGram_inv_hermitian (e : ℝ) (z : ℂ) : (((frameMatrix e z)ᴴ * frameMatrix e z)⁻¹)ᴴ = ((frameMatrix e z)ᴴ * frameMatrix e z)⁻¹
```
### theorem `explicitFrameProjector_idem`
```lean
theorem explicitFrameProjector_idem (e : ℝ) (z : ℂ) : explicitFrameProjector e z * explicitFrameProjector e z = explicitFrameProjector e z
```
### theorem `explicitFrameProjector_hermitian`
```lean
theorem explicitFrameProjector_hermitian (e : ℝ) (z : ℂ) : (explicitFrameProjector e z)ᴴ = explicitFrameProjector e z
```
### theorem `frameGram_trace_P`
```lean
theorem frameGram_trace_P (e : ℝ) (z : ℂ) : explicitFrameProjector e z * frameGram e z = frameGram e z
```
### theorem `frameGram_diag`
```lean
theorem frameGram_diag (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) (i : Fin 4) : frameGram e z i i = 1
```
### theorem `frameGram_mem_elliptope`
```lean
theorem frameGram_mem_elliptope (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) : frameGram e z ∈ correlationElliptope
```
### theorem `frameMatrix_rank`
```lean
theorem frameMatrix_rank (e : ℝ) (z : ℂ) : (frameMatrix e z).rank = 2
```
### theorem `frameGram_rank`
_`K` has rank two._
```lean
theorem frameGram_rank (e : ℝ) (z : ℂ) : (frameGram e z).rank = 2
```
### theorem `trace_P_le`
```lean
theorem trace_P_le (e : ℝ) (z : ℂ) {X : Matrix (Fin 4) (Fin 4) ℂ} (hX : X.PosSemidef) : (explicitFrameProjector e z * X).trace.re ≤ X.trace.re ∧ ((explicitFrameProjector e z * X).trace.re = X.trace.re → X * (1 - explicitFrameProjector e z) = 0)
```
### def `have`
```lean
def have hQQ : (1 - P) * (1 - P) = 1 - P
```
### theorem `exposure_offdiag`
```lean
theorem exposure_offdiag (e s : ℝ) (z w : ℂ) (hes : e * s ≠ 0) (hzi : z.im ≠ 0) (h2 : (e:ℂ) * s * (w + conj w) = 0) (h3 : (e:ℂ) * s * (z * w + conj z * conj w) = 0) : w = 0
```
### theorem `gram_entry`
_Diagonal entries of `W H W^*` for a `4×2` matrix `W` and a `2×2` matrix `H`._
```lean
theorem gram_entry (W : Matrix (Fin 4) (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4) : (W * H * Wᴴ) i i = W i 0 * H 0 0 * conj (W i 0) + W i 0 * H 0 1 * conj (W i 1) + W i 1 * H 1 0 * conj (W i 0) + W i 1 * H 1 1 * conj (W i 1)
```
### theorem `frameMatrix_entries`
```lean
theorem frameMatrix_entries (e : ℝ) (z : ℂ) : frameMatrix e z 0 0 = 1 ∧ frameMatrix e z 0 1 = 0 ∧ frameMatrix e z 1 0 = 0 ∧ frameMatrix e z 1 1 = 1 ∧ frameMatrix e z 2 0 = (e:ℂ) ∧ frameMatrix e z 2 1 = (Real.sqrt (1 - e^2):ℂ) ∧ frameMatrix e z 3 0 = (e:ℂ) ∧ frameMatrix e z 3 1 = (Real.sqrt (1 - e^2):ℂ) * conj z
```
### theorem `frameGram_exposed`
_**Exposure**: on the elliptope, `Re Tr(P X) ≤ 4`, with equality exactly at `X = K`._
```lean
theorem frameGram_exposed (e : ℝ) (z : ℂ) (he0 : 0 < e) (he1 : e < 1) (hz : ‖z‖ = 1) (hzi : z.im ≠ 0) : (∀ X ∈ correlationElliptope, (explicitFrameProjector e z * X).trace.re ≤ 4) ∧ (explicitFrameProjector e z * frameGram e z).trace.re = 4 ∧ (∀ X ∈ correlationElliptope, (explicitFrameProjector e z * X).trace.re = 4 → X = frameGram e z)
```

## EulerianGrothendieck/EndpointDecompositions.lean
### def `endpointVector0`
```lean
def endpointVector0 (z : ℂ) (σ : ℂ) : Fin 4 → ℂ
```
### def `endpointVector1`
```lean
def endpointVector1 (σ : ℂ) : Fin 4 → ℂ
```
### def `rankOneCorrelation`
_A unimodular rank-one correlation `u u^*`._
```lean
def rankOneCorrelation (u : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ
```
### theorem `rankOneCorrelation_mem`
```lean
theorem rankOneCorrelation_mem (u : Fin 4 → ℂ) (hu : ∀ i, ‖u i‖ = 1) : rankOneCorrelation u ∈ correlationElliptope
```
### theorem `frameGram_endpoint_zero`
```lean
theorem frameGram_endpoint_zero (z : ℂ) : frameGram 0 z = (1/2 : ℂ) • (rankOneCorrelation (endpointVector0 z 1) + rankOneCorrelation (endpointVector0 z (-1)))
```
### theorem `frameGram_endpoint_one`
```lean
theorem frameGram_endpoint_one (z : ℂ) : frameGram 1 z = (1/2 : ℂ) • (rankOneCorrelation (endpointVector1 1) + rankOneCorrelation (endpointVector1 (-1)))
```
### theorem `endpointVector0_unimodular`
```lean
theorem endpointVector0_unimodular (z : ℂ) (hz : ‖z‖ = 1) (σ : ℂ) (hσ : ‖σ‖ = 1) : ∀ i, ‖endpointVector0 z σ i‖ = 1
```
### theorem `endpointVector1_unimodular`
```lean
theorem endpointVector1_unimodular (σ : ℂ) (hσ : ‖σ‖ = 1) : ∀ i, ‖endpointVector1 σ i‖ = 1
```
### theorem `projectionScalarNorm_eq_four_of_mem`
_A torus point in the range of the projection gives the value `4`._
```lean
theorem projectionScalarNorm_eq_four_of_mem (U : Submodule ℂ FourSpace) (u : FourSpace) (hu : IsTorusPoint u) (hmem : u ∈ U) : projectionScalarNorm U = 4
```
### theorem `explicitFrameScalarNorm_endpoint_zero`
_`g(P) = 4` at `p = 0`._
```lean
theorem explicitFrameScalarNorm_endpoint_zero (z : ℂ) (hz : ‖z‖ = 1) : explicitFrameScalarNorm 0 z = 4
```
### theorem `explicitFrameScalarNorm_endpoint_one`
_`g(P) = 4` at `p = 1`._
```lean
theorem explicitFrameScalarNorm_endpoint_one (z : ℂ) : explicitFrameScalarNorm 1 z = 4
```
### theorem `endpoint_vectors_in_range`
_The phase vectors of the endpoint decompositions lie in `ran P`._
```lean
theorem endpoint_vectors_in_range (z : ℂ) (σ : ℂ) : (WithLp.toLp 2 (endpointVector0 z σ) : FourSpace) ∈ frameSubspace 0 z ∧ (WithLp.toLp 2 (endpointVector1 σ) : FourSpace) ∈ frameSubspace 1 z
```

## EulerianGrothendieck/BernoulliCumulantIdentification.lean
### def `realBernoulliSeries`
_The real Bernoulli power series `∑ B_n xⁿ/n!` (`B₁ = -1/2`)._
```lean
def realBernoulliSeries : PowerSeries ℝ
```
### theorem `coeff_realBernoulliSeries`
```lean
theorem coeff_realBernoulliSeries (n : ℕ) : coeff n realBernoulliSeries = (bernoulli n : ℝ) / (n ! : ℝ)
```
### theorem `rescale_C'`
```lean
theorem rescale_C' (a r : ℝ) : rescale a (C r) = C r
```
### def `evenBernoulliSeries`
_`G = e^x · β(2x)`._
```lean
def evenBernoulliSeries : PowerSeries ℝ
```
### def `sinhSeries`
_`S = e^x - e^{-x}`._
```lean
def sinhSeries : PowerSeries ℝ
```
### theorem `rescale_two_exp_sub_one`
```lean
theorem rescale_two_exp_sub_one : rescale (2:ℝ) (exp ℝ) - 1 = exp ℝ * sinhSeries
```
### theorem `evenBernoulli_mul_sinh`
```lean
theorem evenBernoulli_mul_sinh : evenBernoulliSeries * sinhSeries = C (2:ℝ) * X
```
### theorem `sinhSeries_ne_zero`
```lean
theorem sinhSeries_ne_zero : sinhSeries ≠ 0
```
### theorem `rescale_neg_sinh`
```lean
theorem rescale_neg_sinh : rescale (-1:ℝ) sinhSeries = -sinhSeries
```
### theorem `evenBernoulli_even`
```lean
theorem evenBernoulli_even : rescale (-1:ℝ) evenBernoulliSeries = evenBernoulliSeries
```
### theorem `coeff_evenBernoulli`
```lean
theorem coeff_evenBernoulli (N : ℕ) : coeff N evenBernoulliSeries = ∑ m ∈ range (N+1), (2:ℝ) ^ m * (bernoulli m : ℝ) / ((m ! : ℝ) * ((N - m) ! : ℝ))
```
### theorem `odd_bernoulli_identity`
_**`∑_{m ≤ N} 2^m B_m /(m!(N-m)!) = 0` for odd `N`.**_
```lean
theorem odd_bernoulli_identity (N : ℕ) (hN : Odd N) : ∑ m ∈ range (N+1), (2:ℝ) ^ m * (bernoulli m : ℝ) / ((m ! : ℝ) * ((N - m) ! : ℝ)) = 0
```
### theorem `bernoulli_odd_zero`
```lean
theorem bernoulli_odd_zero (n : ℕ) (hodd : Odd n) (hn : 1 < n) : bernoulli n = 0
```
### theorem `sum_range_two_mul`
```lean
theorem sum_range_two_mul (f : ℕ → ℝ) (n : ℕ) : ∑ m ∈ range (2 * n), f m = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1))
```
### theorem `even_bernoulli_sum`
_The even-index Bernoulli sum extracted from the odd identity at `N = 2r+3`._
```lean
theorem even_bernoulli_sum (r : ℕ) : ∑ k ∈ range (r+1), (4:ℝ) ^ (k+1) * (bernoulli (2*k+2) : ℝ) / (((2*k+2) ! : ℝ) * ((2*r+1-2*k) ! : ℝ)) = (2*r+2 : ℝ) / ((2*r+3) ! : ℝ)
```
### def `bernoulliCumulant`
_The candidate logarithmic-derivative coefficients `B_{2n+2}/(2(2n+2)!)`._
```lean
def bernoulliCumulant (n : ℕ) : ℝ
```
### theorem `evenEGF_coeff_closed`
```lean
theorem evenEGF_coeff_closed (r : ℕ) : coeff r V033.UniformSum.evenEGF = 1 / ((4:ℝ) ^ r * ((2*r+1) ! : ℝ))
```
### theorem `bernoulliCumulant_convolution`
_The coefficient identity `∑_{k ≤ r} C_k E_{r-k} = (r+1) E_{r+1}`._
```lean
theorem bernoulliCumulant_convolution (r : ℕ) : ∑ k ∈ range (r+1), bernoulliCumulant k * coeff (r - k) V033.UniformSum.evenEGF = (r + 1 : ℝ) * coeff (r+1) V033.UniformSum.evenEGF
```
### theorem `cumulantCoefficient_bernoulli`
_**`coeff_n(cumulantSeries) = B_{2n+2}/(2(2n+2)!)`** for every `n`._
```lean
theorem cumulantCoefficient_bernoulli (n : ℕ) : V033.UniformSum.cumulantCoefficient n = bernoulliCumulant n
```
### theorem `standardUniformCumulant_bernoulli`
_**`standardUniformCumulant n = 3^{n+1} 2^{2n+1} B_{2n+2}/(2n+2)!`** for every `n`._
```lean
theorem standardUniformCumulant_bernoulli (n : ℕ) : standardUniformCumulant n = (3:ℝ) ^ (n+1) * 2 ^ (2*n+1) * (bernoulli (2*n+2) : ℝ) / ((2*n+2) ! : ℝ)
```
### def `uniformLogCoefficient`
_The coefficients `a_j = 3^j 2^{2j-1} B_{2j}/(j (2j)!)` of the manuscript._
```lean
def uniformLogCoefficient (j : ℕ) : ℝ
```
### theorem `standardUniformCumulant_eq_mul_logCoefficient`
_**The link of the manuscript's convention**: `standardUniformCumulant (j-1) = j a_j`._
```lean
theorem standardUniformCumulant_eq_mul_logCoefficient (j : ℕ) (hj : 1 ≤ j) : standardUniformCumulant (j-1) = j * uniformLogCoefficient j
```
### theorem `uniformLogCoefficient_two`
```lean
theorem uniformLogCoefficient_two : uniformLogCoefficient 2 = -1/20
```

## EulerianGrothendieck/ZetaCumulantIdentification.lean
### theorem `uniformLogCoefficient_zeta`
```lean
theorem uniformLogCoefficient_zeta (j : ℕ) (hj : 1 ≤ j) : (uniformLogCoefficient j : ℂ) = (-1) ^ (j-1) * 3 ^ j * riemannZeta (2 * j) / (j * (Real.pi : ℂ) ^ (2 * j))
```
### theorem `standardUniformCumulant_zeta`
_`standardUniformCumulant (j-1) = (-1)^{j-1} 3^j ζ(2j)/π^{2j}` for every `j ≥ 1`._
```lean
theorem standardUniformCumulant_zeta (j : ℕ) (hj : 1 ≤ j) : (standardUniformCumulant (j-1) : ℂ) = (-1) ^ (j-1) * 3 ^ j * riemannZeta (2 * j) / (Real.pi : ℂ) ^ (2 * j)
```

## EulerianGrothendieck/PrintedAllOrderMajorant.lean
### theorem `bernoulli_zeta_bound`
_`|2^{2m-1} π^{2m} B_{2m}/(2m)!| = ζ(2m) ≤ π²/6` for `m ≥ 1`._
```lean
theorem bernoulli_zeta_bound (m : ℕ) (hm : m ≠ 0) : |(2:ℝ) ^ (2*m-1) * π ^ (2*m) * (_root_.bernoulli (2*m) : ℝ) / ((2*m) ! : ℝ)| ≤ π ^ 2 / 6
```
### theorem `standardUniformCumulant_sharp_bound`
_**`|κ_j| ≤ (1/2)(1/3)^j`** for the standardised uniform cumulants._
```lean
theorem standardUniformCumulant_sharp_bound (j : ℕ) : |standardUniformCumulant j| ≤ (1/2) * (1/3:ℝ) ^ j
```
### theorem `ratioRecurrenceCoefficient_sharp_bound`
```lean
theorem ratioRecurrenceCoefficient_sharp_bound (n j : ℕ) : |ratioRecurrenceCoefficient n j| ≤ (2 * (n:ℝ) / 3) ^ j
```
### theorem `coeff_recurrence_term`
```lean
theorem coeff_recurrence_term (n r j : ℕ) : (C (ratioRecurrenceCoefficient n j) * X ^ j * uniformRatioPolynomial (n - j)).coeff r = if j ≤ r then ratioRecurrenceCoefficient n j * (uniformRatioPolynomial (n - j)).coeff (r - j) else 0
```
### theorem `uniformRatio_sharp_coefficient_bound`
_**`|g_r(k)| ≤ e (8k²)^r`** for every `k` and `r` (eg:eq:majorant)._
```lean
theorem uniformRatio_sharp_coefficient_bound (k r : ℕ) : |(uniformRatioPolynomial k).coeff r| ≤ Real.exp 1 * (8 * (k:ℝ) ^ 2) ^ r
```
### theorem `uniformSquared_sharp_coefficient_bound`
_**`|q_r(k)| ≤ (r+1) e² (8k²)^r`** (eg:eq:majorant-q)._
```lean
theorem uniformSquared_sharp_coefficient_bound (k r : ℕ) : |(uniformSquaredPolynomial k).coeff r| ≤ Real.exp 1 ^ 2 * (r + 1) * (8 * (k:ℝ) ^ 2) ^ r
```
### def `printedNormConstant`
_The printed constant `C^{(N)}_{t,R}` of (eg:eq:CN)._
```lean
def printedNormConstant (t : ℝ) (R : ℕ) : ℝ
```
### def `printedTerm`
```lean
def printedTerm (t : ℝ) (R k : ℕ) : ℝ
```
### theorem `printedNormConstant_eq`
```lean
theorem printedNormConstant_eq (t : ℝ) (R : ℕ) : printedNormConstant t R = ∑' k, printedTerm t R k
```
### theorem `printedTerm_nonneg`
```lean
theorem printedTerm_nonneg (t : ℝ) (R k : ℕ) : 0 ≤ printedTerm t R k
```
### theorem `printedTerm_summable`
```lean
theorem printedTerm_summable (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R : ℕ) : Summable (printedTerm t R)
```
### theorem `printed_all_order_norm_remainder`
_**Theorem (eg:eq:allnorm) with the printed constant (eg:eq:CN)**: for `0 < t < 1`, `R ≥ 0` and `M ≥ 4096`, `|N - ∑_{r ≤ R} A_r(t) M^{-r}| ≤ C^{(N)}_{t,R} M^{-R-1}`._
```lean
theorem printed_all_order_norm_remainder (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R M : ℕ) (hM : 4096 ≤ M) : |uniformNormSeries M t - ∑ r ∈ range (R+1), uniformNormCoefficient t r / (M:ℝ) ^ r| ≤ printedNormConstant t R / (M:ℝ) ^ (R+1)
```

## EulerianGrothendieck/GeneralPhaseOptimization.lean
### def `phaseLambda`
_`λ` in terms of the half-angle coordinates `C = cos(ϑ/2)`, `S = sin(ϑ/2)`._
```lean
def phaseLambda (C S : ℝ) : ℝ
```
### theorem `limitingObjective_halfPhase_identity`
```lean
theorem limitingObjective_halfPhase_identity (C S u v : ℝ) (y : ℂ) (hCS : C^2+S^2=1) : limitingObjective (halfPhase C S) u v y = u^2 + 3*(v + 2*C*(C*y.re-S*y.im)/3)^2 + (2/3:ℝ)*C^2*(C*y.re-S*y.im)^2 + 2*S^2*(S*y.re+C*y.im)^2
```
### theorem `limitingObjective_general_lower`
```lean
theorem limitingObjective_general_lower (C S u v : ℝ) (y : ℂ) (hCS : C^2+S^2=1) (hy : ‖y‖=1) : phaseLambda C S ≤ limitingObjective (halfPhase C S) u v y
```
### theorem `limitingObjective_general_trial`
_Trial points on both branches of the minimum._
```lean
theorem limitingObjective_general_trial (C S : ℝ) (hCS : C^2+S^2=1) : ∃ v : ℝ, ∃ y : ℂ, |v| ≤ 4 ∧ ‖y‖ = 1 ∧ limitingObjective (halfPhase C S) 0 v y = phaseLambda C S
```
### theorem `phaseLambda_le_two`
```lean
theorem phaseLambda_le_two (C S : ℝ) (hCS : C^2+S^2=1) : phaseLambda C S ≤ 2
```
### theorem `general_frameDistance_global_lower`
```lean
theorem general_frameDistance_global_lower (C S : ℝ) (hCS : C^2+S^2=1) (e : ℝ) (a b : ℂ) (he : 0 < e) (he1 : e ≤ 1/12) : phaseLambda C S * e^2 - 2000*e^3 ≤ frameDistance e (halfPhase C S) a b
```
### theorem `general_frameDistance_trial_upper`
```lean
theorem general_frameDistance_trial_upper (C S : ℝ) (hCS : C^2+S^2=1) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1/12) : ∃ a b : ℂ, frameDistance e (halfPhase C S) a b ≤ phaseLambda C S * e^2 + 2000*e^3
```
### theorem `general_frameInfimum_remainder`
_The global infimum for an arbitrary phase, with a uniform cubic remainder._
```lean
theorem general_frameInfimum_remainder (C S : ℝ) (hCS : C^2+S^2=1) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1/12) : |frameInfimum e (halfPhase C S) - phaseLambda C S * e^2| ≤ 2000*e^3
```
### theorem `exp_I_eq_halfPhase`
```lean
theorem exp_I_eq_halfPhase (θ : ℝ) : Complex.exp (θ * Complex.I) = halfPhase (Real.cos (θ/2)) (Real.sin (θ/2))
```
### def `lambdaPhase`
_`λ(ϑ) = min((2/3)cos²(ϑ/2), 2 sin²(ϑ/2))`._
```lean
def lambdaPhase (θ : ℝ) : ℝ
```
### theorem `general_phase_loss`
_**Theorem 9.15, arbitrary phase**: `|4 - g(P(p,ϑ)) - λ(ϑ) p| ≤ 2000 p^{3/2}` for `0 < p ≤ 1/144`, uniformly in the real phase `ϑ`._
```lean
theorem general_phase_loss (θ : ℝ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1/144) : |(4 - explicitFrameScalarNorm (Real.sqrt p) (Complex.exp (θ * Complex.I))) - lambdaPhase θ * p| ≤ 2000 * p * Real.sqrt p
```
### theorem `general_phase_loss_limit`
_First-order law for every fixed phase: `(4 - g(P(p,ϑ)))/p → λ(ϑ)` as `p ↓ 0`._
```lean
theorem general_phase_loss_limit (θ : ℝ) : Tendsto (fun p => (4 - explicitFrameScalarNorm (Real.sqrt p) (Complex.exp (θ * Complex.I))) / p) (𝓝[>] 0) (𝓝 (lambdaPhase θ))
```

## EulerianGrothendieck/OccupancySharpRemainder.lean
### def `occ`
_Occupancy of box `j`._
```lean
def occ (f : Fin k → Fin M) (j : Fin M) : ℕ
```
### def `expect`
_Expectation under the uniform law on assignments `Fin k → Fin M`._
```lean
def expect (M k : ℕ) (X : (Fin k → Fin M) → ℝ) : ℝ
```
### def `egf`
```lean
def egf (w : ℕ → ℝ) : PowerSeries ℝ
```
### theorem `derivative_finset_prod`
```lean
theorem derivative_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → PowerSeries ℝ) : derivative ℝ (∏ i ∈ s, F i) = ∑ i ∈ s, ∏ j ∈ s, (if j = i then derivative ℝ (F j) else F j)
```
### theorem `occ_cons`
```lean
theorem occ_cons (y : Fin M) (f : Fin k → Fin M) (j : Fin M) : occ (Fin.cons y f : Fin (k+1) → Fin M) j = occ f j + (if y = j then 1 else 0)
```
### theorem `coeff_egf_shift`
```lean
theorem coeff_egf_shift (w : ℕ → ℝ) : egf (fun r => w (r + 1)) = derivative ℝ (egf w)
```
### theorem `sum_prod_occ`
_`∑_f ∏_j w_j(N_j(f)) = k! [x^k] ∏_j (∑_r w_j(r) x^r/r!)`._
```lean
theorem sum_prod_occ (k : ℕ) (w : Fin M → ℕ → ℝ) : ∑ f : Fin k → Fin M, ∏ j, w j (occ f j) = (k ! : ℝ) * coeff k (∏ j, egf (w j))
```
### theorem `uniformMomentRatio_occupancy`
_**Occupancy representation**: `R_{M,k} = E ∏_j ρ_{N_j}`._
```lean
theorem uniformMomentRatio_occupancy (M k : ℕ) (hM : M ≠ 0) : uniformMomentRatio M k = expect M k (fun f => ∏ j, momentFactor (occ f j))
```
### def `coll`
_Indicator that the ordered pair `p` of balls collides._
```lean
def coll (f : Fin k → Fin M) (p : Fin k × Fin k) : ℝ
```
### def `offDiag`
```lean
def offDiag (k : ℕ) : Finset (Fin k × Fin k)
```
### theorem `mem_offDiag'`
```lean
theorem mem_offDiag' {p : Fin k × Fin k} : p ∈ offDiag k ↔ p.1 ≠ p.2
```
### def `orderedCollisions`
_Number of colliding ordered pairs of distinct balls._
```lean
def orderedCollisions (f : Fin k → Fin M) : ℝ
```
### def `collisions`
_`L = ∑_j binom(N_j, 2)`, as a real number._
```lean
def collisions (f : Fin k → Fin M) : ℝ
```
### theorem `card_offDiag`
```lean
theorem card_offDiag (k : ℕ) : ((offDiag k).card : ℝ) = k * ((k:ℝ) - 1)
```
### theorem `sum_coll_all`
```lean
theorem sum_coll_all (f : Fin k → Fin M) : ∑ p : Fin k × Fin k, coll f p = ∑ j, (occ f j : ℝ) ^ 2
```
### theorem `sum_occ`
```lean
theorem sum_occ (f : Fin k → Fin M) : ∑ j, (occ f j : ℝ) = k
```
### theorem `collisions_eq`
```lean
theorem collisions_eq (f : Fin k → Fin M) : collisions f = orderedCollisions f / 2
```
### def `splitAt`
_Splitting off coordinate `d`._
```lean
def splitAt (d : Fin k) : (Fin k → Fin M) ≃ Fin M × ({j // j ≠ d} → Fin M)
```
### theorem `update_eq_splitAt`
```lean
theorem update_eq_splitAt (d : Fin k) (f : Fin k → Fin M) (y : Fin M) : Function.update f d y = (splitAt d).symm (y, ((splitAt d) f).2)
```
### theorem `sum_update`
_`∑_f ∑_y g(f[d ↦ y]) = M ∑_f g(f)`._
```lean
theorem sum_update (d : Fin k) (g : (Fin k → Fin M) → ℝ) : ∑ f, ∑ y, g (Function.update f d y) = (M:ℝ) * ∑ f, g f
```
### theorem `expect_coll`
```lean
theorem expect_coll (hM : M ≠ 0) {p : Fin k × Fin k} (hp : p.1 ≠ p.2) : expect M k (fun f => coll f p) = 1 / M
```
### theorem `coll_mul_self`
```lean
theorem coll_mul_self (f : Fin k → Fin M) (p : Fin k × Fin k) : coll f p * coll f p = coll f p
```
### theorem `coll_swap`
```lean
theorem coll_swap (f : Fin k → Fin M) (p : Fin k × Fin k) : coll f p.swap = coll f p
```
### theorem `expect_coll_mul`
_Two different pairs (not equal up to order) collide jointly with probability `1/M²`._
```lean
theorem expect_coll_mul (hM : M ≠ 0) {p q : Fin k × Fin k} (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) (hpq : q ≠ p) (hpq' : q ≠ p.swap) : expect M k (fun f => coll f p * coll f q) = 1 / (M:ℝ) ^ 2
```
### theorem `expect_add_mul`
```lean
theorem expect_add_mul (X Y : (Fin k → Fin M) → ℝ) (a b : ℝ) : expect M k (fun f => a * X f + b * Y f) = a * expect M k X + b * expect M k Y
```
### theorem `expect_sum`
```lean
theorem expect_sum {ι : Type*} (s : Finset ι) (X : ι → (Fin k → Fin M) → ℝ) : expect M k (fun f => ∑ i ∈ s, X i f) = ∑ i ∈ s, expect M k (X i)
```
### theorem `expect_mono`
```lean
theorem expect_mono {X Y : (Fin k → Fin M) → ℝ} (h : ∀ f, X f ≤ Y f) : expect M k X ≤ expect M k Y
```
### theorem `expect_const`
```lean
theorem expect_const (hM : M ≠ 0) (c : ℝ) : expect M k (fun _ => c) = c
```
### theorem `expect_orderedCollisions`
```lean
theorem expect_orderedCollisions (hM : M ≠ 0) : expect M k orderedCollisions = k * ((k:ℝ) - 1) / M
```
### theorem `filter_pair`
```lean
theorem filter_pair (p : Fin k × Fin k) (hp : p.1 ≠ p.2) : (offDiag k).filter (fun q => q = p ∨ q = p.swap) = {p, p.swap}
```
### theorem `expect_orderedCollisions_sq`
```lean
theorem expect_orderedCollisions_sq (hM : M ≠ 0) : expect M k (fun f => orderedCollisions f * orderedCollisions f) = k * ((k:ℝ) - 1) * (2 / M + (k * ((k:ℝ) - 1) - 2) / (M:ℝ) ^ 2)
```
### theorem `expect_collisions`
_`E L = L_k/M` with `L_k = k(k-1)/2`._
```lean
theorem expect_collisions (hM : M ≠ 0) : expect M k collisions = (k * ((k:ℝ) - 1) / 2) / M
```
### theorem `expect_collisions_falling`
_`E L(L-1) = L_k(L_k-1)/M²`._
```lean
theorem expect_collisions_falling (hM : M ≠ 0) : expect M k (fun f => collisions f * (collisions f - 1)) = (k * ((k:ℝ) - 1) / 2) * (k * ((k:ℝ) - 1) / 2 - 1) / (M:ℝ) ^ 2
```
### theorem `momentFactor_le_three_fifths`
```lean
theorem momentFactor_le_three_fifths (n : ℕ) (hn : 2 ≤ n) : momentFactor n ≤ 3/5
```
### theorem `one_sub_momentFactor_le`
```lean
theorem one_sub_momentFactor_le (n : ℕ) : 1 - momentFactor n ≤ (2/5) * ((n:ℝ) * ((n:ℝ) - 1) / 2)
```
### theorem `one_sub_prod_le`
```lean
theorem one_sub_prod_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i)
```
### theorem `occupancy_pointwise`
```lean
theorem occupancy_pointwise (f : Fin k → Fin M) : 0 ≤ (∏ j, momentFactor (occ f j)) - 1 + (2/5) * collisions f ∧ (∏ j, momentFactor (occ f j)) - 1 + (2/5) * collisions f ≤ collisions f * (collisions f - 1)
```
### theorem `occupancy_moment_bound`
_**Lemma 9.3**: `0 ≤ R_{M,k} - (1 - d_k/M) ≤ L_k(L_k-1)/M²`, `d_k = k(k-1)/5`, `L_k = k(k-1)/2`, for every `M ≥ 1` and `k ≥ 0`._
```lean
theorem occupancy_moment_bound (M k : ℕ) (hM : M ≠ 0) : 0 ≤ uniformMomentRatio M k - (1 - (k * ((k:ℝ) - 1) / 5) / M) ∧ uniformMomentRatio M k - (1 - (k * ((k:ℝ) - 1) / 5) / M) ≤ (k * ((k:ℝ) - 1) / 2) * (k * ((k:ℝ) - 1) / 2 - 1) / (M:ℝ) ^ 2
```
### theorem `occupancy_square_bound`
_**Lemma 9.4**: `0 ≤ R_{M,k}² - (1 - 2d_k/M) ≤ 27 k²(k-1)²/(50 M²)`._
```lean
theorem occupancy_square_bound (M k : ℕ) (hM : M ≠ 0) : 0 ≤ uniformMomentRatio M k ^ 2 - (1 - 2 * (k * ((k:ℝ) - 1) / 5) / M) ∧ uniformMomentRatio M k ^ 2 - (1 - 2 * (k * ((k:ℝ) - 1) / 5) / M) ≤ 27 / (50 * (M:ℝ) ^ 2) * ((k:ℝ) ^ 2 * ((k:ℝ) - 1) ^ 2)
```

## EulerianGrothendieck/ExplicitNormRemainder.lean
### def `remF`
```lean
def remF (s : ℝ) : ℝ
```
### def `remA`
```lean
def remA (s : ℝ) : ℝ
```
### def `remB`
```lean
def remB (s : ℝ) : ℝ
```
### theorem `centralFactorialMoment_closed`
```lean
theorem centralFactorialMoment_closed (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : centralFactorialMoment s 2 = 3/4 * s ^ 2 / ((1 - s) ^ 2 * Real.sqrt (1 - s)) ∧ centralFactorialMoment s 3 = 15/8 * s ^ 3 / ((1 - s) ^ 3 * Real.sqrt (1 - s)) ∧ centralFactorialMoment s 4 = 105/16 * s ^ 4 / ((1 - s) ^ 4 * Real.sqrt (1 - s))
```
### theorem `fallingReal_two`
```lean
theorem fallingReal_two (x : ℝ) : fallingReal 2 x = x * (x - 1)
```
### theorem `fallingReal_three`
```lean
theorem fallingReal_three (x : ℝ) : fallingReal 3 x = x * (x - 1) * (x - 2)
```
### theorem `fallingReal_four`
```lean
theorem fallingReal_four (x : ℝ) : fallingReal 4 x = x * (x - 1) * (x - 2) * (x - 3)
```
### theorem `binomialWeight_eq_central`
```lean
theorem binomialWeight_eq_central (t : ℝ) (k : ℕ) : binomialWeight t k = centralCoefficient k * (t ^ 2) ^ k
```
### theorem `weighted_falling_hasSum`
```lean
theorem weighted_falling_hasSum (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (q : ℕ) : HasSum (fun k : ℕ => binomialWeight t k * fallingReal q k) (centralFactorialMoment (t^2) q)
```
### theorem `explicit_norm_remainder_aux`
_**Theorem 9.5** (explicit form): `0 ≤ N - F(s) + A(s)/M ≤ B(s)/M²` for every `M ≥ 1`, with `s = (1/(12c))²`._
```lean
theorem explicit_norm_remainder_aux {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : 1/12 < c) (M : ℕ) (hM : M ≠ 0) : 0 ≤ (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ) - remF ((1/(12*c))^2) + remA ((1/(12*c))^2) / M ∧ (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ) - remF ((1/(12*c))^2) + remA ((1/(12*c))^2) / M ≤ remB ((1/(12*c))^2) / (M:ℝ) ^ 2
```
### theorem `explicit_norm_remainder`
_**Theorem 9.5**: `0 ≤ N - F(s) + A(s)/M ≤ B(s)/M²` for every `M ≥ 1`._
```lean
theorem explicit_norm_remainder {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : 1/12 < c) (M : ℕ) (hM : M ≠ 0) : let N
```
### theorem `explicit_vacuum_remainder_aux`
_The printed inversion estimate `|1/N - (1/F + A/(F²M))| ≤ (B + A²)/(F²M²)` (explicit form)._
```lean
theorem explicit_vacuum_remainder_aux {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : 1/12 < c) (M : ℕ) (hM : M ≠ 0) : |1 / (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ) - (1 / remF ((1/(12*c))^2) + remA ((1/(12*c))^2) / (remF ((1/(12*c))^2) ^ 2 * M))| ≤ (remB ((1/(12*c))^2) + remA ((1/(12*c))^2) ^ 2) / (remF ((1/(12*c))^2) ^ 2 * (M:ℝ) ^ 2)
```
### theorem `explicit_vacuum_remainder`
_The printed inversion estimate `|1/N - (1/F + A/(F²M))| ≤ (B + A²)/(F²M²)`._
```lean
theorem explicit_vacuum_remainder {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : 1/12 < c) (M : ℕ) (hM : M ≠ 0) : let N
```
