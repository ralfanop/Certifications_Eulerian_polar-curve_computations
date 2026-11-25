import Mathlib
import Manuscript16.V166HolonomyPair
import Manuscript16.ReactiveHolonomyV166
import Manuscript16.HolonomyEulerProduct20261124

/-!
# M16 v16.6 §14.5 `eq:hol-det`: local uniform convergence of the paired holonomy product

`V166HolonomyPair` (merged) proves `|pairRatio a φ n - 1| ≤ pairConstant a φ / n²` for `n ≥ 1`.
`HolonomyEulerProduct20261124` (merged, #596) evaluates, for each fixed `a > 0` and real `φ`,
the limit of the partial products by Euler's sine product. The step left open in
`docs/manuscript16/V166_HOLONOMY_PAIRED_CONVERGENCE_20261119.md` and in the certification
scope of v16.6 is the uniformity in the parameters: "for `a` and `φ` varying in compact subsets
of `a > 0` and `φ` real ... local uniform convergence and nonvanishing". This file proves it,
with the parameter `p = (a, φ) ∈ ℝ × ℝ` and `posHalf = {p | 0 < p.1}`:

* `paired_product_tendstoUniformlyOn`: on every compact `K ⊆ posHalf`, the partial products
  `∏_{n=1}^{N} pairRatio a φ n` converge uniformly to
  `pairedLimit (a, φ) = a² (sin²(πφ) + sinh²(πa)) / ((φ²+a²) sinh²(πa))`;
* `paired_product_tendstoLocallyUniformlyOn`: the same convergence is locally uniform on the
  open half-plane `posHalf`;
* `holonomy_det_tendstoUniformlyOn`, `holonomy_det_tendstoLocallyUniformlyOn`: with the unpaired
  `n = 0` factor `(φ²+a²)/a²`, uniform convergence on compacts of `posHalf` (and locally uniform
  convergence on `posHalf`) to `productClosed (πa) (cos 2πφ) = (cosh 2πa - cos 2πφ)/(cosh 2πa - 1)`;
* `pairedLimit_pos`: the limit of the paired product is strictly positive on `posHalf`
  (nonvanishing); the limit with the `n = 0` factor is `≥ 1` by `holonomy_det_limit_ge_one`.

Input used, not re-proved: the uniform Weierstrass test for products of the form
`∏ (1 + fₙ)` on a compact set (`Summable.hasProdUniformlyOn_nat_one_add`, Mathlib), and Euler's
sine product through the merged `HolonomyEulerProduct20261124`. These are statements about real
functions of the two real parameters; no operator determinant, trace-class membership or spectral
identification of `∏ pairRatio` is asserted.
-/

open Filter Topology

namespace Manuscript16.HolonomyUniformConvergence20261124

open Manuscript16.V166HolonomyPair Manuscript16.ReactiveHolonomy
  Manuscript16.HolonomyEulerProduct20261124

/-- The open parameter half-plane `{(a, φ) | a > 0}`. -/
def posHalf : Set (ℝ × ℝ) := {p | 0 < p.1}

theorem isOpen_posHalf : IsOpen posHalf :=
  isOpen_lt continuous_const continuous_fst

/-- The deviation `pairRatio a φ (n+1) - 1` as a function of `p = (a, φ)`. -/
noncomputable def pairDev (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  pairRatio p.1 p.2 ((n : ℝ) + 1) - 1

/-- The Euler limit of the paired product. -/
noncomputable def pairedLimit (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 * (Real.sin (Real.pi * p.2) ^ 2 + Real.sinh (Real.pi * p.1) ^ 2) /
    ((p.2 ^ 2 + p.1 ^ 2) * Real.sinh (Real.pi * p.1) ^ 2)

theorem continuous_pairDev (n : ℕ) : Continuous (pairDev n) := by
  unfold pairDev pairRatio
  refine Continuous.sub (Continuous.div (by fun_prop) (by fun_prop) (fun p => ?_)) continuous_const
  positivity

theorem continuous_pairConstant : Continuous (fun p : ℝ × ℝ => pairConstant p.1 p.2) := by
  unfold pairConstant
  fun_prop

/-- Uniform majorant on a compact set: `|pairRatio a φ (n+1) - 1| ≤ C / (n+1)²`. -/
theorem pairDev_uniform_bound {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ‖pairDev n p‖ ≤ C / ((n : ℝ) + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_pairConstant.continuousOn
  refine ⟨|C|, abs_nonneg C, fun n p hp => ?_⟩
  have hb := pair_deviation_bound p.1 p.2 ((n : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hc : pairConstant p.1 p.2 ≤ |C| :=
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC p hp).trans (le_abs_self C))
  rw [Real.norm_eq_abs]
  unfold pairDev
  exact hb.trans (div_le_div_of_nonneg_right hc (by positivity))

theorem summable_inv_succ_sq (C : ℝ) :
    Summable (fun n : ℕ => C / ((n : ℝ) + 1) ^ 2) := by
  have hp : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    convert hp using 1
    funext n
    rw [abs_of_nonneg (by positivity), Real.rpow_two]
  simpa only [div_eq_mul_inv, one_mul] using hs.mul_left C

/-- Uniform convergence of the paired partial products on every compact `K ⊆ posHalf`. -/
theorem paired_product_tendstoUniformlyOn {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKpos : K ⊆ posHalf) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ) => ∏ j ∈ Finset.range N, pairRatio p.1 p.2 ((j : ℝ) + 1))
      pairedLimit atTop K := by
  obtain ⟨C, -, hC⟩ := pairDev_uniform_bound hK
  have hprod := Summable.hasProdUniformlyOn_nat_one_add (f := pairDev) hK
    (summable_inv_succ_sq C) (Eventually.of_forall fun n p hp => hC n p hp)
    (fun n => (continuous_pairDev n).continuousOn)
  have hunif := hprod.tendstoUniformlyOn_finsetRange
  have hfun : (fun N (p : ℝ × ℝ) => ∏ i ∈ Finset.range N, (1 + pairDev i p)) =
      (fun N (p : ℝ × ℝ) => ∏ j ∈ Finset.range N, pairRatio p.1 p.2 ((j : ℝ) + 1)) := by
    funext N p
    refine Finset.prod_congr rfl (fun j _ => ?_)
    unfold pairDev
    ring
  rw [hfun] at hunif
  refine hunif.congr_right (fun p hp => ?_)
  exact tendsto_nhds_unique (hunif.tendsto_at hp) (paired_product_tendsto p.1 p.2 (hKpos hp))

/-- Locally uniform convergence of the paired partial products on the open half-plane. -/
theorem paired_product_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun N (p : ℝ × ℝ) => ∏ j ∈ Finset.range N, pairRatio p.1 p.2 ((j : ℝ) + 1))
      pairedLimit atTop posHalf :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_posHalf).mpr
    (fun _ hKpos hK => paired_product_tendstoUniformlyOn hK hKpos)

/-- Nonvanishing: the limit of the paired product is strictly positive for `a > 0`. -/
theorem pairedLimit_pos {p : ℝ × ℝ} (hp : p ∈ posHalf) : 0 < pairedLimit p := by
  have ha : 0 < p.1 := hp
  have hsinh : 0 < Real.sinh (Real.pi * p.1) := Real.sinh_pos_iff.mpr (by positivity)
  unfold pairedLimit
  positivity

/-- The unpaired `n = 0` factor `(φ²+a²)/a²` times the Euler limit is the closed form
`productClosed (πa) (cos 2πφ)`. -/
theorem pairedLimit_mul_eq (p : ℝ × ℝ) (hp : p ∈ posHalf) :
    (p.2 ^ 2 + p.1 ^ 2) / p.1 ^ 2 * pairedLimit p =
      productClosed (Real.pi * p.1) (Real.cos (2 * Real.pi * p.2)) :=
  tendsto_nhds_unique ((paired_product_tendsto p.1 p.2 hp).const_mul _)
    (holonomy_det_tendsto p.1 p.2 hp)

/-- **`eq:hol-det`, uniform form.** On every compact `K ⊆ posHalf`, the symmetric partial
products with the unpaired factor `(φ²+a²)/a²` converge uniformly to
`productClosed (πa) (cos 2πφ) = (cosh 2πa - cos 2πφ)/(cosh 2πa - 1)`. -/
theorem holonomy_det_tendstoUniformlyOn {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKpos : K ⊆ posHalf) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ) => (p.2 ^ 2 + p.1 ^ 2) / p.1 ^ 2 *
        ∏ j ∈ Finset.range N, pairRatio p.1 p.2 ((j : ℝ) + 1))
      (fun p => productClosed (Real.pi * p.1) (Real.cos (2 * Real.pi * p.2))) atTop K := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.2 ^ 2 + p.1 ^ 2) / p.1 ^ 2) K := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun p hp => ?_)
    have ha : 0 < p.1 := hKpos hp
    positivity
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  have hM1 : 0 < |M| + 1 := by positivity
  have hu := paired_product_tendstoUniformlyOn hK hKpos
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu (ε / (|M| + 1)) (div_pos hε hM1)] with N hN p hp
  rw [← pairedLimit_mul_eq p (hKpos hp), Real.dist_eq, ← mul_sub, abs_mul]
  have hg : |(p.2 ^ 2 + p.1 ^ 2) / p.1 ^ 2| ≤ |M| + 1 :=
    ((Real.norm_eq_abs _ ▸ hM p hp).trans (le_abs_self M)).trans (by linarith)
  have hd : |pairedLimit p - ∏ j ∈ Finset.range N, pairRatio p.1 p.2 ((j : ℝ) + 1)| <
      ε / (|M| + 1) := by
    simpa [Real.dist_eq] using hN p hp
  calc |(p.2 ^ 2 + p.1 ^ 2) / p.1 ^ 2| *
        |pairedLimit p - ∏ j ∈ Finset.range N, pairRatio p.1 p.2 ((j : ℝ) + 1)|
      ≤ (|M| + 1) *
        |pairedLimit p - ∏ j ∈ Finset.range N, pairRatio p.1 p.2 ((j : ℝ) + 1)| :=
        mul_le_mul_of_nonneg_right hg (abs_nonneg _)
    _ < (|M| + 1) * (ε / (|M| + 1)) := mul_lt_mul_of_pos_left hd hM1
    _ = ε := by field_simp

/-- **`eq:hol-det`, locally uniform form** on the open half-plane `a > 0`. -/
theorem holonomy_det_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun N (p : ℝ × ℝ) => (p.2 ^ 2 + p.1 ^ 2) / p.1 ^ 2 *
        ∏ j ∈ Finset.range N, pairRatio p.1 p.2 ((j : ℝ) + 1))
      (fun p => productClosed (Real.pi * p.1) (Real.cos (2 * Real.pi * p.2))) atTop posHalf :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_posHalf).mpr
    (fun _ hKpos hK => holonomy_det_tendstoUniformlyOn hK hKpos)

end Manuscript16.HolonomyUniformConvergence20261124

#print axioms Manuscript16.HolonomyUniformConvergence20261124.isOpen_posHalf
#print axioms Manuscript16.HolonomyUniformConvergence20261124.continuous_pairDev
#print axioms Manuscript16.HolonomyUniformConvergence20261124.continuous_pairConstant
#print axioms Manuscript16.HolonomyUniformConvergence20261124.pairDev_uniform_bound
#print axioms Manuscript16.HolonomyUniformConvergence20261124.summable_inv_succ_sq
#print axioms Manuscript16.HolonomyUniformConvergence20261124.paired_product_tendstoUniformlyOn
#print axioms Manuscript16.HolonomyUniformConvergence20261124.paired_product_tendstoLocallyUniformlyOn
#print axioms Manuscript16.HolonomyUniformConvergence20261124.pairedLimit_pos
#print axioms Manuscript16.HolonomyUniformConvergence20261124.pairedLimit_mul_eq
#print axioms Manuscript16.HolonomyUniformConvergence20261124.holonomy_det_tendstoUniformlyOn
#print axioms Manuscript16.HolonomyUniformConvergence20261124.holonomy_det_tendstoLocallyUniformlyOn
