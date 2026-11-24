import Manuscript16.DiracMaxwellSchattenThreshold20261124

/-!
# M16 §13: Maxwell lower and upper series for every real `p` (`eq:mixed-lower-series-164`, `eq:mixed-upper-series-164`)

`DiracMaxwellSchattenThreshold20261124` (#589) proves `∑ᵢ |wᵢ|ᵖ < ∞ ⇔ p > 3` for the whole
coefficient-space spectral list of `L₀ = W_R ⊕ D₃` (#588). Its divergence half uses the Dirac
shells only; on the Maxwell modes it proves convergence for `p > 3` and nothing for `p ≤ 3`.
The reconciliation ledger `docs/manuscript16/V166_FROZEN_SECTION13_IDENTITY_RECONCILIATION_20261118.md`
records as open: `eq:mixed-lower-series-164` for general `p ≤ 3` (only the nearest-mode series at
`p = 3` is in `main`, `V165SchattenThirdNonsummable`), and the full infinite form of
`eq:mixed-upper-series-164` for the actual integer-index series.

Maxwell modes: `ℓ = l + 2 ≥ 2`, `k ∈ ℤ \ {0, −ℓ}`, multiplicity `2(ℓ² − 1)`,
`|wᵢ| = 1 / (4 |k| |ℓ + k|)` (`maxwellWeight`, `abs_maxwellWeight`). This file proves, on the
actual index type `MaxwellIndex` and for every real `p`:

* nearest mode `k = 1`: `|w| = 1 / (4(ℓ + 1))` (`abs_maxwellWeight_nearest`);
* lower series: the `ℓ`-fiber sum is at least `2(ℓ² − 1) (4(ℓ + 1))^{−p}` whenever it converges
  (`lowerShell_le_fiber_tsum`), and `∑_{ℓ ≥ 2} 2(ℓ² − 1) (4(ℓ + 1))^{−p} < ∞ ⇔ p > 3`
  (`lowerSeries_summable_iff`);
* Maxwell threshold: `∑_{Maxwell} |wᵢ|ᵖ < ∞ ⇔ p > 3` (`maxwell_summable_iff`), i.e. the Maxwell
  part of the diagonal of `L₀⁻¹` alone lies in `ℓᵖ` exactly for `p > 3` (`maxwellWeight_memℓp_iff`);
* upper series: for `p > 1`, every `ℓ` and every fixed multiplicity label, the actual infinite sum
  over `k ∈ ℤ \ {0, −ℓ}` satisfies `∑_k |w_{ℓ,k}|ᵖ ≤ 4 (2ℓ)^{−p} ∑_{j ≥ 1} j^{−p}`
  (`upperSeries_le`), via `∑_{n ∈ ℤ} |n|^{−p} = 2 ∑_{j ≥ 1} j^{−p}` (`zetaZ_eq_two_mul`);
* the Maxwell total is bounded below by the lower series for `p > 3`
  (`lowerSeries_le_maxwell_tsum`).

Scope. Coefficient-space statements only, on the spectral list of #588. The unitary
identification of `ℓ²(MixedIndex)` with `R ⊕ L²(S³; Σ)` and the identification of the Schatten
class `S_p` of a diagonal operator with `ℓᵖ` of its diagonal are published inputs (cited in #588,
#589; Simon 2005, Ch. 2), not formalized; nothing about `S³` is derived. Every `det₄` statement
stays outside this file.
-/

noncomputable section

open scoped ENNReal

namespace Manuscript16.MaxwellLowerUpperSeries20261124

open Manuscript16.V166L2SpectralInverse
open Manuscript16.DiracMaxwellSchattenThreshold20261124

/-! ### Nearest mode `k = 1` -/

/-- The admissible temporal label `k = 1` in the `l`-th Maxwell fiber. -/
def kOne (l : ℕ) : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)} :=
  ⟨1, by constructor <;> omega⟩

/-- `|w| = 1 / (4(ℓ + 1))` at the nearest mode `k = 1`, `ℓ = l + 2`. -/
theorem abs_maxwellWeight_nearest (l : ℕ) (j : Fin (2 * ((l + 2) ^ 2 - 1))) :
    |maxwellWeight ⟨l, (kOne l, j)⟩| = (4 * ((l : ℝ) + 3))⁻¹ := by
  refine (abs_maxwellWeight (⟨l, (kOne l, j)⟩ : MaxwellIndex)).trans ?_
  have h1 : ((⟨l, (kOne l, j)⟩ : MaxwellIndex).2.1.1 : ℤ) = 1 := rfl
  have h2 : ((⟨l, (kOne l, j)⟩ : MaxwellIndex).1 : ℕ) = l := rfl
  rw [h1, h2]
  have h : (0 : ℝ) ≤ (l : ℝ) + 3 := by positivity
  push_cast
  rw [abs_one, one_mul, show (l : ℝ) + 2 + 1 = (l : ℝ) + 3 by ring, abs_of_nonneg h]

/-! ### Lower series -/

/-- The `l`-th term of the lower series: `2(ℓ² − 1) (4(ℓ + 1))^{−p}`, `ℓ = l + 2`. -/
def lowerShell (p : ℝ) (l : ℕ) : ℝ :=
  ((2 * ((l + 2) ^ 2 - 1) : ℕ) : ℝ) * ((4 * ((l : ℝ) + 3))⁻¹) ^ p

theorem lowerShell_nonneg (p : ℝ) (l : ℕ) : 0 ≤ lowerShell p l := by
  unfold lowerShell
  have := Real.rpow_nonneg (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 4 * ((l : ℝ) + 3))) p
  positivity

theorem mult_cast (l : ℕ) :
    ((2 * ((l + 2) ^ 2 - 1) : ℕ) : ℝ) = 2 * (((l : ℝ) + 1) * ((l : ℝ) + 3)) := by
  have h : 1 ≤ (l + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_mul, Nat.cast_sub h]
  push_cast
  ring

/-- The `ℓ`-fiber sum dominates the lower-series term whenever it converges (every real `p`). -/
theorem lowerShell_le_fiber_tsum (p : ℝ) (l : ℕ)
    (hs : Summable (fun y : MaxwellFiber l => |maxwellWeight ⟨l, y⟩| ^ p)) :
    lowerShell p l ≤ ∑' y : MaxwellFiber l, |maxwellWeight ⟨l, y⟩| ^ p := by
  let e : Fin (2 * ((l + 2) ^ 2 - 1)) ↪ MaxwellFiber l :=
    Function.Embedding.sectR (kOne l) (Fin (2 * ((l + 2) ^ 2 - 1)))
  have hsum : ∑ y ∈ Finset.univ.map e, |maxwellWeight ⟨l, y⟩| ^ p = lowerShell p l := by
    rw [Finset.sum_map]
    have hterm : ∀ j : Fin (2 * ((l + 2) ^ 2 - 1)),
        |maxwellWeight ⟨l, e j⟩| ^ p = ((4 * ((l : ℝ) + 3))⁻¹) ^ p := fun j =>
      congrArg (fun t : ℝ => t ^ p) (abs_maxwellWeight_nearest l j)
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  rw [← hsum]
  exact hs.sum_le_tsum _ (fun y _ => Real.rpow_nonneg (abs_nonneg _) p)

/-- `eq:mixed-lower-series-164`: `∑_{ℓ ≥ 2} 2(ℓ² − 1) (4(ℓ + 1))^{−p} < ∞ ⇔ p > 3`, every real `p`. -/
theorem lowerSeries_summable_iff (p : ℝ) : Summable (lowerShell p) ↔ 3 < p := by
  constructor
  · intro h
    by_contra hp
    rw [not_lt] at hp
    have hharm : ¬ Summable (fun l : ℕ => 1 / |(l : ℝ) + 3| ^ (1 : ℝ)) := fun hh =>
      (lt_irrefl (1 : ℝ)) ((Real.summable_one_div_nat_add_rpow 3 1).mp hh)
    apply hharm
    refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) (h.mul_left 96)
    set x : ℝ := 4 * ((l : ℝ) + 3) with hx
    have hx1 : (1 : ℝ) ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    have hx0 : (0 : ℝ) < x := by linarith
    have hxp : x ^ p ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hp
    have hinv : (x ^ (3 : ℝ))⁻¹ ≤ (x ^ p)⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hx0 p) hxp
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have habs : |(l : ℝ) + 3| ^ (1 : ℝ) = (l : ℝ) + 3 := by
      rw [Real.rpow_one, abs_of_nonneg (by positivity)]
    rw [habs]
    unfold lowerShell
    rw [mult_cast, Real.inv_rpow hx0.le]
    have hx3 : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast x 3
    rw [hx3] at hinv
    have hkey : 1 / ((l : ℝ) + 3) ≤ 96 * (2 * (((l : ℝ) + 1) * ((l : ℝ) + 3)) * (x ^ (3 : ℕ))⁻¹) := by
      rw [hx]
      have hd : (0 : ℝ) < (l : ℝ) + 3 := by positivity
      rw [div_le_iff₀ hd]
      have hpow : (4 * ((l : ℝ) + 3)) ^ (3 : ℕ) = 64 * ((l : ℝ) + 3) ^ 3 := by ring
      rw [hpow]
      field_simp
      nlinarith
    calc 1 / ((l : ℝ) + 3) ≤ 96 * (2 * (((l : ℝ) + 1) * ((l : ℝ) + 3)) * (x ^ (3 : ℕ))⁻¹) := hkey
      _ ≤ 96 * (2 * (((l : ℝ) + 1) * ((l : ℝ) + 3)) * (x ^ p)⁻¹) := by gcongr
  · intro hp
    have hs : Summable (fun l : ℕ => ((l : ℝ) + 3) ^ ((2 : ℝ) - p)) := by
      have h := (summable_nat_add_iff 3).2
        (Real.summable_nat_rpow.2 (by linarith : (2 : ℝ) - p < -1))
      simpa only [Nat.cast_add, Nat.cast_ofNat] using h
    refine Summable.of_nonneg_of_le (fun l => lowerShell_nonneg p l) (fun l => ?_)
      (hs.mul_left (2 * (4 ^ p)⁻¹))
    set y : ℝ := (l : ℝ) + 3 with hy
    have hy0 : 0 < y := by rw [hy]; positivity
    have hm : 2 * (((l : ℝ) + 1) * ((l : ℝ) + 3)) ≤ 2 * y ^ 2 := by
      rw [hy]; nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    unfold lowerShell
    rw [mult_cast]
    have hB : 0 ≤ ((4 * y)⁻¹) ^ p := Real.rpow_nonneg (by positivity) p
    calc 2 * (((l : ℝ) + 1) * ((l : ℝ) + 3)) * ((4 * y)⁻¹) ^ p
        ≤ 2 * y ^ 2 * ((4 * y)⁻¹) ^ p := by gcongr
      _ = 2 * (4 ^ p)⁻¹ * y ^ ((2 : ℝ) - p) := by
          rw [Real.rpow_sub hy0, Real.rpow_two, Real.inv_rpow (by positivity),
            Real.mul_rpow (by norm_num) hy0.le]
          have h4p : (0 : ℝ) < 4 ^ p := Real.rpow_pos_of_pos (by norm_num) p
          have hyp : (0 : ℝ) < y ^ p := Real.rpow_pos_of_pos hy0 p
          field_simp

/-- If the Maxwell part of the spectral list is `p`-summable, so is the lower series. -/
theorem lowerSeries_summable_of_maxwell (p : ℝ)
    (h : Summable (fun i : MaxwellIndex => |maxwellWeight i| ^ p)) :
    Summable (lowerShell p) := by
  have hsig := (summable_sigma_of_nonneg
    (f := fun i : MaxwellIndex => |maxwellWeight i| ^ p)
    (fun i => Real.rpow_nonneg (abs_nonneg _) p)).1 h
  exact Summable.of_nonneg_of_le (fun l => lowerShell_nonneg p l)
    (fun l => lowerShell_le_fiber_tsum p l (hsig.1 l)) hsig.2

/-- Maxwell threshold: `∑_{Maxwell} |wᵢ|ᵖ < ∞ ⇔ p > 3`, every real `p`. -/
theorem maxwell_summable_iff (p : ℝ) :
    Summable (fun i : MaxwellIndex => |maxwellWeight i| ^ p) ↔ 3 < p :=
  ⟨fun h => (lowerSeries_summable_iff p).1 (lowerSeries_summable_of_maxwell p h),
    maxwell_summable p⟩

/-- The Maxwell part of the diagonal of `L₀⁻¹` lies in `ℓᵖ` exactly for `p > 3`. -/
theorem maxwellWeight_memℓp_iff (p : ℝ) (hp : 0 < p) :
    Memℓp (fun i : MaxwellIndex => (maxwellWeight i : ℂ)) (ENNReal.ofReal p) ↔ 3 < p := by
  have hp' : 0 < (ENNReal.ofReal p).toReal := by rwa [ENNReal.toReal_ofReal hp.le]
  rw [memℓp_gen_iff hp', ENNReal.toReal_ofReal hp.le]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact maxwell_summable_iff p

/-- For `p > 3` the Maxwell total is bounded below by the lower series. -/
theorem lowerSeries_le_maxwell_tsum (p : ℝ) (hp : 3 < p) :
    ∑' l : ℕ, lowerShell p l ≤ ∑' i : MaxwellIndex, |maxwellWeight i| ^ p := by
  have h := maxwell_summable p hp
  have hsig := (summable_sigma_of_nonneg
    (f := fun i : MaxwellIndex => |maxwellWeight i| ^ p)
    (fun i => Real.rpow_nonneg (abs_nonneg _) p)).1 h
  calc ∑' l : ℕ, lowerShell p l
      ≤ ∑' l : ℕ, ∑' y : MaxwellFiber l, |maxwellWeight ⟨l, y⟩| ^ p :=
        Summable.tsum_le_tsum (fun l => lowerShell_le_fiber_tsum p l (hsig.1 l))
          ((lowerSeries_summable_iff p).2 hp) hsig.2
    _ = ∑' i : MaxwellIndex, |maxwellWeight i| ^ p := (h.tsum_sigma' hsig.1).symm

/-! ### Upper series -/

/-- `∑_{n ∈ ℤ} |n|^{−p} = 2 ∑_{j ≥ 1} j^{−p}` for `p > 1`. -/
theorem zetaZ_eq_two_mul (p : ℝ) (hp : 1 < p) :
    zetaZ p = 2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ (-p) := by
  set f : ℤ → ℝ := fun m => |(m : ℝ)| ^ (-p) with hf
  have hpos : ∀ n : ℕ, f ((n : ℤ) + 1) = ((n : ℝ) + 1) ^ (-p) := fun n => by
    simp only [hf]
    push_cast
    rw [abs_of_nonneg (by positivity)]
  have hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) = ((n : ℝ) + 1) ^ (-p) := fun n => by
    simp only [hf]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : -p < -1))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hs1 : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := hs.congr (fun n => (hpos n).symm)
  have hs2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := hs.congr (fun n => (hneg n).symm)
  have h0 : f 0 = 0 := by
    simp only [hf, Int.cast_zero, abs_zero]
    exact Real.zero_rpow (by linarith)
  have hsplit := tsum_of_add_one_of_neg_add_one hs1 hs2
  change ∑' n : ℤ, f n = _
  rw [hsplit, h0, add_zero, tsum_congr hpos, tsum_congr hneg]
  ring

/-- `eq:mixed-upper-series-164`, infinite form on the actual index set: for `p > 1`, every
`ℓ = l + 2` and every multiplicity label `j`, the sum over all admissible `k ∈ ℤ \ {0, −ℓ}`
converges and `∑_k |w_{ℓ,k}|ᵖ ≤ 4 (2ℓ)^{−p} ∑_{j ≥ 1} j^{−p}`. -/
theorem upperSeries_le (p : ℝ) (hp : 1 < p) (l : ℕ) (j : Fin (2 * ((l + 2) ^ 2 - 1))) :
    Summable (fun k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)} =>
        |maxwellWeight ⟨l, (k, j)⟩| ^ p) ∧
      ∑' k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)}, |maxwellWeight ⟨l, (k, j)⟩| ^ p ≤
        4 * ((2 * ((l : ℝ) + 2))⁻¹) ^ p * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) := by
  have hZ := maxwellMajorant_summable p hp l
  have hG : Summable (fun k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)} => maxwellMajorant p l k.1) :=
    hZ.subtype _
  have hle : ∀ k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)},
      |maxwellWeight ⟨l, (k, j)⟩| ^ p ≤ maxwellMajorant p l k.1 := fun k =>
    maxwell_le_majorant p (by linarith) ⟨l, (k, j)⟩
  have hs : Summable (fun k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)} =>
      |maxwellWeight ⟨l, (k, j)⟩| ^ p) :=
    Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (abs_nonneg _) p) hle hG
  refine ⟨hs, ?_⟩
  have hsub : ∑' k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)}, maxwellMajorant p l k.1 ≤
      ∑' n : ℤ, maxwellMajorant p l n :=
    Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun n _ => maxwellMajorant_nonneg p l n) (fun _ => le_rfl) hG hZ
  calc ∑' k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)}, |maxwellWeight ⟨l, (k, j)⟩| ^ p
      ≤ ∑' k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)}, maxwellMajorant p l k.1 :=
        Summable.tsum_le_tsum hle hs hG
    _ ≤ ∑' n : ℤ, maxwellMajorant p l n := hsub
    _ = ((2 * ((l : ℝ) + 2))⁻¹) ^ p * (2 * zetaZ p) := maxwellMajorant_tsum p hp l
    _ = 4 * ((2 * ((l : ℝ) + 2))⁻¹) ^ p * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) := by
        rw [zetaZ_eq_two_mul p hp]
        ring

end Manuscript16.MaxwellLowerUpperSeries20261124

#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.kOne
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.abs_maxwellWeight_nearest
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.lowerShell_nonneg
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.mult_cast
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.lowerShell_le_fiber_tsum
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.lowerSeries_summable_iff
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.lowerSeries_summable_of_maxwell
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.maxwell_summable_iff
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.maxwellWeight_memℓp_iff
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.lowerSeries_le_maxwell_tsum
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.zetaZ_eq_two_mul
#print axioms Manuscript16.MaxwellLowerUpperSeries20261124.upperSeries_le
