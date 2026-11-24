import Manuscript16.DiracMaxwellCoefficientModel20261124

/-!
# M16 §13: sharp Schatten threshold of the coefficient-space `L₀⁻¹` (`eq:mixed-schatten-164`)

`DiracMaxwellCoefficientModel20261124` realizes `L₀ = W_R ⊕ D₃` on `X = ℓ²(MixedIndex, ℂ)` and
proves that its ambient inverse is the diagonal operator `R₀ = diag(w)`, `w = mixedWeight`, the
inverse eigenvalues with their multiplicities:

* Maxwell modes `(ℓ, m) = (l + 2, l + 2 + 2k)`, `k ∈ ℤ \ {0, −ℓ}`, multiplicity `2(ℓ² − 1)`,
  `|wᵢ| = 1 / (4 |k| |ℓ + k|)`;
* Dirac modes `±(n + 3/2)`, multiplicity `(n + 1)(n + 2)` for each sign, `|wᵢ| = 1 / (n + 3/2)`.

This file proves, for every real `p`,

  `∑ᵢ |wᵢ|ᵖ < ∞  ⇔  p > 3`   (`mixedWeight_summable_iff`),

equivalently `w ∈ ℓᵖ ⇔ p > 3` for `p > 0` (`mixedWeight_memℓp_iff`, `L0_resolvent_weights_memℓp_iff`).

* Convergence for `p > 3`. Dirac: the `n`-th shell is `2(n+1)(n+2)(n + 3/2)^{−p} ≤ 2(n+1)^{2−p}`.
  Maxwell: since `|k| + |ℓ + k| ≥ ℓ`, `1/(4|k||ℓ+k|) ≤ (2ℓ)⁻¹ max(|k|⁻¹, |ℓ+k|⁻¹)`, hence the
  `ℓ`-shell is at most `2ℓ² (2ℓ)^{−p} · 2 ∑_{n ∈ ℤ} |n|^{−p}`, summable in `ℓ` for `p > 3`.
* Divergence for `p ≤ 3`: already the Dirac shells dominate `(32/45) n⁻¹` (harmonic series).

Scope. The identification of the Schatten class `S_p` of a diagonal operator with `ℓᵖ` of its
diagonal (its singular values are the moduli `|wᵢ|`), and the two-sided ideal property of `S_p`
used to pass from `L₀⁻¹` to `L⁻¹ = L₀⁻¹ (I + E L₀⁻¹)⁻¹`, are classical published results cited
(Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS 2005, Ch. 2); Mathlib at the pinned
commit has no Schatten classes and they are NOT formalized here. Nothing about `S³` is derived:
the spectral list is the coefficient-space model of #588. Every `det₄` statement stays open.
-/

noncomputable section

open scoped ENNReal

namespace Manuscript16.DiracMaxwellSchattenThreshold20261124

open Manuscript16.V166L2SpectralInverse Manuscript16.DiracMaxwellCoefficientModel20261124
open Manuscript16.DiracMaxwellGraphSpace20261124

/-! ### Dirac shells -/

theorem abs_diracWeight (i : DiracIndex) : |diracWeight i| = ((i.1 : ℝ) + 3 / 2)⁻¹ := by
  have hpos : (0 : ℝ) < (i.1 : ℝ) + 3 / 2 := by positivity
  unfold diracWeight
  split_ifs
  · exact abs_of_pos (inv_pos.2 hpos)
  · rw [abs_neg]
    exact abs_of_pos (inv_pos.2 hpos)

/-- The `n`-th Dirac shell: both signs, multiplicity `(n + 1)(n + 2)` each. -/
theorem dirac_shell_tsum (p : ℝ) (n : ℕ) :
    ∑' y : Bool × Fin ((n + 1) * (n + 2)), |diracWeight ⟨n, y⟩| ^ p =
      2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) * (((n : ℝ) + 3 / 2) ^ p)⁻¹ := by
  have hterm : ∀ y : Bool × Fin ((n + 1) * (n + 2)),
      |diracWeight ⟨n, y⟩| ^ p = (((n : ℝ) + 3 / 2)⁻¹) ^ p := fun y =>
    congrArg (fun t : ℝ => t ^ p) (abs_diracWeight ⟨n, y⟩)
  rw [tsum_fintype, Finset.sum_congr rfl (fun y _ => hterm y)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Real.inv_rpow (by positivity)]
  push_cast
  ring

theorem dirac_summable_iff (p : ℝ) :
    Summable (fun i : DiracIndex => |diracWeight i| ^ p) ↔ 3 < p := by
  have hsig : Summable (fun i : DiracIndex => |diracWeight i| ^ p) ↔
      ((∀ n : ℕ, Summable fun y : Bool × Fin ((n + 1) * (n + 2)) => |diracWeight ⟨n, y⟩| ^ p) ∧
        Summable fun n : ℕ =>
          ∑' y : Bool × Fin ((n + 1) * (n + 2)), |diracWeight ⟨n, y⟩| ^ p) :=
    summable_sigma_of_nonneg (fun i => Real.rpow_nonneg (abs_nonneg _) p)
  rw [hsig]
  simp only [dirac_shell_tsum]
  constructor
  · rintro ⟨-, h⟩
    by_contra hp
    rw [not_lt] at hp
    apply Real.not_summable_natCast_inv
    refine Summable.of_nonneg_of_le (fun n => inv_nonneg.2 (Nat.cast_nonneg n))
      (fun n => ?_) (h.mul_left (45 / 32))
    set x : ℝ := (n : ℝ) + 3 / 2 with hx
    have hx1 : (1 : ℝ) ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hxp : x ^ p ≤ x ^ 3 := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by exact_mod_cast hp)
    have hinv : (x ^ 3)⁻¹ ≤ (x ^ p)⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos (by linarith) p) hxp
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp only [Nat.cast_zero, inv_zero]
      positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
      have hkey : (n : ℝ)⁻¹ ≤ 45 / 32 * (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2))) * (x ^ 3)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), hx]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hn1) (sub_nonneg.2 hn1))
          (sub_nonneg.2 hn1), sq_nonneg ((n : ℝ) - 1)]
      calc (n : ℝ)⁻¹ ≤ 45 / 32 * (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2))) * (x ^ 3)⁻¹ := hkey
        _ ≤ 45 / 32 * (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2))) * (x ^ p)⁻¹ := by gcongr
        _ = 45 / 32 * (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) * (x ^ p)⁻¹) := by ring
  · intro hp
    refine ⟨fun n => Summable.of_finite, ?_⟩
    have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ ((2 : ℝ) - p)) := by
      have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : (2 : ℝ) - p < -1))
      simpa only [Nat.cast_add, Nat.cast_one] using h
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs.mul_left 2)
    set x : ℝ := (n : ℝ) + 3 / 2 with hx
    have hxpos : 0 < x := by rw [hx]; positivity
    have h1 : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ x ^ 2 := by rw [hx]; nlinarith
    have h2 : x ^ ((2 : ℝ) - p) = x ^ 2 * (x ^ p)⁻¹ := by
      rw [Real.rpow_sub hxpos, Real.rpow_two, div_eq_mul_inv]
    have h3 : x ^ ((2 : ℝ) - p) ≤ ((n : ℝ) + 1) ^ ((2 : ℝ) - p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [hx]; linarith) (by linarith)
    have hxp : 0 ≤ (x ^ p)⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hxpos.le p)
    calc 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) * (x ^ p)⁻¹ ≤ 2 * x ^ 2 * (x ^ p)⁻¹ := by gcongr
      _ = 2 * x ^ ((2 : ℝ) - p) := by rw [h2]; ring
      _ ≤ 2 * ((n : ℝ) + 1) ^ ((2 : ℝ) - p) := by gcongr

/-! ### Maxwell shells -/

/-- Elementary bound: if `a, c ≥ 1` and `L ≤ a + c`, then
`(4ac)^{−p} ≤ (2L)^{−p} (a^{−p} + c^{−p})` for `p ≥ 0`. -/
theorem shell_bound (a c L p : ℝ) (ha : 1 ≤ a) (hc : 1 ≤ c) (hL0 : 0 < L) (hL : L ≤ a + c)
    (hp : 0 ≤ p) :
    ((4 * (a * c))⁻¹) ^ p ≤ ((2 * L)⁻¹) ^ p * (a ^ (-p) + c ^ (-p)) := by
  have ha0 : 0 < a := by linarith
  have hc0 : 0 < c := by linarith
  have hmax : (4 * (a * c))⁻¹ ≤ (2 * L)⁻¹ * max a⁻¹ c⁻¹ := by
    rcases le_total a c with h | h
    · calc (4 * (a * c))⁻¹ ≤ (2 * L * a)⁻¹ :=
            inv_anti₀ (by positivity) (by nlinarith)
        _ = (2 * L)⁻¹ * a⁻¹ := by rw [mul_inv]
        _ ≤ (2 * L)⁻¹ * max a⁻¹ c⁻¹ := by gcongr; exact le_max_left _ _
    · calc (4 * (a * c))⁻¹ ≤ (2 * L * c)⁻¹ :=
            inv_anti₀ (by positivity) (by nlinarith)
        _ = (2 * L)⁻¹ * c⁻¹ := by rw [mul_inv]
        _ ≤ (2 * L)⁻¹ * max a⁻¹ c⁻¹ := by gcongr; exact le_max_right _ _
  have hm0 : 0 ≤ max a⁻¹ c⁻¹ := le_max_of_le_left (inv_nonneg.2 ha0.le)
  have hsum : (max a⁻¹ c⁻¹) ^ p ≤ a ^ (-p) + c ^ (-p) := by
    rw [Real.rpow_neg ha0.le, Real.rpow_neg hc0.le, ← Real.inv_rpow ha0.le,
      ← Real.inv_rpow hc0.le]
    have h1 : 0 ≤ a⁻¹ ^ p := Real.rpow_nonneg (inv_nonneg.2 ha0.le) p
    have h2 : 0 ≤ c⁻¹ ^ p := Real.rpow_nonneg (inv_nonneg.2 hc0.le) p
    rcases max_choice a⁻¹ c⁻¹ with h | h <;> rw [h] <;> linarith
  calc ((4 * (a * c))⁻¹) ^ p ≤ ((2 * L)⁻¹ * max a⁻¹ c⁻¹) ^ p :=
        Real.rpow_le_rpow (by positivity) hmax hp
    _ = ((2 * L)⁻¹) ^ p * (max a⁻¹ c⁻¹) ^ p :=
        Real.mul_rpow (inv_nonneg.2 (by positivity)) hm0
    _ ≤ ((2 * L)⁻¹) ^ p * (a ^ (-p) + c ^ (-p)) := by
        gcongr

theorem abs_maxwellWeight (i : MaxwellIndex) :
    |maxwellWeight i| =
      (4 * (|(i.2.1.1 : ℝ)| * |(((i.1 : ℤ) + 2 + i.2.1.1 : ℤ) : ℝ)|))⁻¹ := by
  unfold maxwellWeight
  rw [abs_inv, abs_mul, abs_mul, mul_assoc]
  norm_num

/-- Dominating function on the `l`-th Maxwell shell, indexed by `n ∈ ℤ`. -/
def maxwellMajorant (p : ℝ) (l : ℕ) (n : ℤ) : ℝ :=
  ((2 * ((l : ℝ) + 2))⁻¹) ^ p * (|(n : ℝ)| ^ (-p) + |(((l : ℤ) + 2 + n : ℤ) : ℝ)| ^ (-p))

theorem maxwellMajorant_nonneg (p : ℝ) (l : ℕ) (n : ℤ) : 0 ≤ maxwellMajorant p l n := by
  unfold maxwellMajorant
  have : (0 : ℝ) ≤ (2 * ((l : ℝ) + 2))⁻¹ := by positivity
  have h1 := Real.rpow_nonneg this p
  have h2 := Real.rpow_nonneg (abs_nonneg (n : ℝ)) (-p)
  have h3 := Real.rpow_nonneg (abs_nonneg ((((l : ℤ) + 2 + n : ℤ) : ℝ))) (-p)
  positivity

theorem maxwell_le_majorant (p : ℝ) (hp : 0 ≤ p) (i : MaxwellIndex) :
    |maxwellWeight i| ^ p ≤ maxwellMajorant p i.1 i.2.1.1 := by
  rw [abs_maxwellWeight]
  unfold maxwellMajorant
  have ha : (1 : ℝ) ≤ |(i.2.1.1 : ℝ)| := by exact_mod_cast Int.one_le_abs i.2.1.2.1
  have hz : (i.1 : ℤ) + 2 + i.2.1.1 ≠ 0 := by
    intro h
    apply i.2.1.2.2
    omega
  have hc : (1 : ℝ) ≤ |(((i.1 : ℤ) + 2 + i.2.1.1 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  have hL : (i.1 : ℝ) + 2 ≤ |(i.2.1.1 : ℝ)| + |(((i.1 : ℤ) + 2 + i.2.1.1 : ℤ) : ℝ)| := by
    push_cast
    linarith [le_abs_self ((i.1 : ℝ) + 2 + (i.2.1.1 : ℝ)), neg_abs_le (i.2.1.1 : ℝ)]
  exact shell_bound _ _ _ p ha hc (by positivity) hL hp

/-- `S(p) = ∑_{n ∈ ℤ} |n|^{−p}` (the `n = 0` term is `0`). -/
def zetaZ (p : ℝ) : ℝ := ∑' n : ℤ, |(n : ℝ)| ^ (-p)

theorem shifted_summable (p : ℝ) (hp : 1 < p) (l : ℕ) :
    Summable (fun n : ℤ => |(((l : ℤ) + 2 + n : ℤ) : ℝ)| ^ (-p)) :=
  (Real.summable_abs_int_rpow hp).comp_injective (add_right_injective ((l : ℤ) + 2))

theorem shifted_tsum (p : ℝ) (l : ℕ) :
    ∑' n : ℤ, |(((l : ℤ) + 2 + n : ℤ) : ℝ)| ^ (-p) = zetaZ p :=
  Equiv.tsum_eq (Equiv.addLeft ((l : ℤ) + 2)) (fun n : ℤ => |(n : ℝ)| ^ (-p))

theorem maxwellMajorant_summable (p : ℝ) (hp : 1 < p) (l : ℕ) :
    Summable (maxwellMajorant p l) :=
  ((Real.summable_abs_int_rpow hp).add (shifted_summable p hp l)).mul_left _

theorem maxwellMajorant_tsum (p : ℝ) (hp : 1 < p) (l : ℕ) :
    ∑' n : ℤ, maxwellMajorant p l n = ((2 * ((l : ℝ) + 2))⁻¹) ^ p * (2 * zetaZ p) := by
  unfold maxwellMajorant
  rw [tsum_mul_left, (Real.summable_abs_int_rpow hp).tsum_add (shifted_summable p hp l),
    shifted_tsum]
  change _ * (zetaZ p + zetaZ p) = _
  ring

/-- Abbreviation for the `l`-th Maxwell fiber. -/
abbrev MaxwellFiber (l : ℕ) :=
  {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)} × Fin (2 * ((l + 2) ^ 2 - 1))

theorem maxwell_fiber_summable (p : ℝ) (hp : 1 < p) (l : ℕ) :
    Summable (fun y : MaxwellFiber l => |maxwellWeight ⟨l, y⟩| ^ p) := by
  have hG : Summable (fun k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)} => maxwellMajorant p l k.1) :=
    (maxwellMajorant_summable p hp l).subtype _
  have hdom : Summable (fun y : MaxwellFiber l =>
      maxwellMajorant p l y.1.1 * (fun _ : Fin (2 * ((l + 2) ^ 2 - 1)) => (1 : ℝ)) y.2) :=
    hG.mul_of_nonneg Summable.of_finite (fun k => maxwellMajorant_nonneg p l k.1)
      (fun _ => zero_le_one)
  refine Summable.of_nonneg_of_le (fun y => Real.rpow_nonneg (abs_nonneg _) p) (fun y => ?_) hdom
  simpa only [mul_one] using maxwell_le_majorant p (by linarith) ⟨l, y⟩

theorem maxwell_fiber_tsum_le (p : ℝ) (hp : 1 < p) (l : ℕ) :
    ∑' y : MaxwellFiber l, |maxwellWeight ⟨l, y⟩| ^ p ≤
      ((2 * ((l + 2) ^ 2 - 1) : ℕ) : ℝ) * (((2 * ((l : ℝ) + 2))⁻¹) ^ p * (2 * zetaZ p)) := by
  have hZ := maxwellMajorant_summable p hp l
  have hG : Summable (fun k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)} => maxwellMajorant p l k.1) :=
    hZ.subtype _
  have hGn : Summable (fun k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)} =>
      ‖maxwellMajorant p l k.1‖) := by
    simpa only [Real.norm_eq_abs] using hG.abs
  have h1n : Summable (fun _ : Fin (2 * ((l + 2) ^ 2 - 1)) => ‖(1 : ℝ)‖) := Summable.of_finite
  have hprod := tsum_mul_tsum_of_summable_norm hGn h1n
  have hdom : Summable (fun y : MaxwellFiber l =>
      maxwellMajorant p l y.1.1 * (fun _ : Fin (2 * ((l + 2) ^ 2 - 1)) => (1 : ℝ)) y.2) :=
    hG.mul_of_nonneg Summable.of_finite (fun k => maxwellMajorant_nonneg p l k.1)
      (fun _ => zero_le_one)
  have hsub : ∑' k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)}, maxwellMajorant p l k.1 ≤
      ∑' n : ℤ, maxwellMajorant p l n :=
    Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun n _ => maxwellMajorant_nonneg p l n) (fun _ => le_rfl) hG hZ
  have hone : ∑' _ : Fin (2 * ((l + 2) ^ 2 - 1)), (1 : ℝ) =
      ((2 * ((l + 2) ^ 2 - 1) : ℕ) : ℝ) := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  calc ∑' y : MaxwellFiber l, |maxwellWeight ⟨l, y⟩| ^ p
      ≤ ∑' y : MaxwellFiber l,
          maxwellMajorant p l y.1.1 * (fun _ : Fin (2 * ((l + 2) ^ 2 - 1)) => (1 : ℝ)) y.2 := by
        refine Summable.tsum_le_tsum (fun y => ?_) (maxwell_fiber_summable p hp l) hdom
        simpa only [mul_one] using maxwell_le_majorant p (by linarith) ⟨l, y⟩
    _ = (∑' k : {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ) + 2)}, maxwellMajorant p l k.1) *
          ∑' _ : Fin (2 * ((l + 2) ^ 2 - 1)), (1 : ℝ) := hprod.symm
    _ ≤ (∑' n : ℤ, maxwellMajorant p l n) * ∑' _ : Fin (2 * ((l + 2) ^ 2 - 1)), (1 : ℝ) := by
        gcongr
    _ = ((2 * ((l + 2) ^ 2 - 1) : ℕ) : ℝ) * (((2 * ((l : ℝ) + 2))⁻¹) ^ p * (2 * zetaZ p)) := by
        rw [maxwellMajorant_tsum p hp l, hone, mul_comm]

theorem maxwell_summable (p : ℝ) (hp : 3 < p) :
    Summable (fun i : MaxwellIndex => |maxwellWeight i| ^ p) := by
  have hp1 : 1 < p := by linarith
  have hsig : Summable (fun i : MaxwellIndex => |maxwellWeight i| ^ p) ↔
      ((∀ l : ℕ, Summable fun y : MaxwellFiber l => |maxwellWeight ⟨l, y⟩| ^ p) ∧
        Summable fun l : ℕ => ∑' y : MaxwellFiber l, |maxwellWeight ⟨l, y⟩| ^ p) :=
    summable_sigma_of_nonneg (fun i => Real.rpow_nonneg (abs_nonneg _) p)
  rw [hsig]
  refine ⟨fun l => maxwell_fiber_summable p hp1 l, ?_⟩
  have hS : 0 ≤ zetaZ p := tsum_nonneg (fun n => Real.rpow_nonneg (abs_nonneg _) _)
  have hs : Summable (fun l : ℕ => ((l : ℝ) + 2) ^ ((2 : ℝ) - p)) := by
    have h := (summable_nat_add_iff 2).2 (Real.summable_nat_rpow.2 (by linarith : (2 : ℝ) - p < -1))
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  refine Summable.of_nonneg_of_le
    (fun l => tsum_nonneg (fun y => Real.rpow_nonneg (abs_nonneg _) p))
    (fun l => (maxwell_fiber_tsum_le p hp1 l).trans ?_) (hs.mul_left (4 * zetaZ p * (2 ^ p)⁻¹))
  set y : ℝ := (l : ℝ) + 2 with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hm : ((2 * ((l + 2) ^ 2 - 1) : ℕ) : ℝ) ≤ 2 * y ^ 2 := by
    have h : 2 * ((l + 2) ^ 2 - 1) ≤ 2 * (l + 2) ^ 2 := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
    calc ((2 * ((l + 2) ^ 2 - 1) : ℕ) : ℝ) ≤ ((2 * (l + 2) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * y ^ 2 := by rw [hy]; push_cast; ring
  have hB : 0 ≤ ((2 * y)⁻¹) ^ p * (2 * zetaZ p) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) p) (by positivity)
  calc ((2 * ((l + 2) ^ 2 - 1) : ℕ) : ℝ) * (((2 * y)⁻¹) ^ p * (2 * zetaZ p))
      ≤ 2 * y ^ 2 * (((2 * y)⁻¹) ^ p * (2 * zetaZ p)) := by gcongr
    _ = 4 * zetaZ p * (2 ^ p)⁻¹ * y ^ ((2 : ℝ) - p) := by
        rw [Real.rpow_sub hy0, Real.rpow_two, Real.inv_rpow (by positivity),
          Real.mul_rpow (by norm_num) hy0.le]
        have h2p : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos (by norm_num) p
        have hyp : (0 : ℝ) < y ^ p := Real.rpow_pos_of_pos hy0 p
        field_simp
        ring

/-! ### The mixed spectral list -/

theorem norm_mixedWeight_inl (i : MaxwellIndex) :
    ‖mixedWeight (Sum.inl i)‖ = |maxwellWeight i| := by
  change ‖(maxwellWeight i : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem norm_mixedWeight_inr (i : DiracIndex) :
    ‖mixedWeight (Sum.inr i)‖ = |diracWeight i| := by
  change ‖(diracWeight i : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `eq:mixed-schatten-164`, coefficient form: `∑ᵢ |wᵢ|ᵖ < ∞ ⇔ p > 3`, for every real `p`. -/
theorem mixedWeight_summable_iff (p : ℝ) :
    Summable (fun i : MixedIndex => ‖mixedWeight i‖ ^ p) ↔ 3 < p := by
  constructor
  · intro h
    have hr := h.comp_injective Sum.inr_injective
    have hfun : ((fun i : MixedIndex => ‖mixedWeight i‖ ^ p) ∘ Sum.inr) =
        fun i : DiracIndex => |diracWeight i| ^ p := by
      funext i
      simp only [Function.comp_apply, norm_mixedWeight_inr]
    rw [hfun] at hr
    exact (dirac_summable_iff p).1 hr
  · intro hp
    apply Summable.sum
    · have hfun : ((fun i : MixedIndex => ‖mixedWeight i‖ ^ p) ∘ Sum.inl) =
          fun i : MaxwellIndex => |maxwellWeight i| ^ p := by
        funext i
        simp only [Function.comp_apply, norm_mixedWeight_inl]
      rw [hfun]
      exact maxwell_summable p hp
    · have hfun : ((fun i : MixedIndex => ‖mixedWeight i‖ ^ p) ∘ Sum.inr) =
          fun i : DiracIndex => |diracWeight i| ^ p := by
        funext i
        simp only [Function.comp_apply, norm_mixedWeight_inr]
      rw [hfun]
      exact (dirac_summable_iff p).2 hp

/-- `w ∈ ℓᵖ ⇔ p > 3` for every real `p > 0`. -/
theorem mixedWeight_memℓp_iff (p : ℝ) (hp : 0 < p) :
    Memℓp mixedWeight (ENNReal.ofReal p) ↔ 3 < p := by
  have hp' : 0 < (ENNReal.ofReal p).toReal := by rwa [ENNReal.toReal_ofReal hp.le]
  rw [memℓp_gen_iff hp', ENNReal.toReal_ofReal hp.le]
  exact mixedWeight_summable_iff p

/-- The ambient inverse of the coefficient-space `L₀ = W_R ⊕ D₃` is `diag(w)`, and `w ∈ ℓᵖ`
exactly for `p > 3`. With the classical identification `diag(w) ∈ S_p ⇔ w ∈ ℓᵖ` (cited, not
formalized) this is `L₀⁻¹ ∈ S_p ⇔ p > 3`. -/
theorem L0_resolvent_weights_memℓp_iff (p : ℝ) (hp : 0 < p) :
    ambientResolvent L0 L0_isClosed L0_injective L0_surjective =
        diagonal mixedWeight (2 / 3) (by norm_num) mixedWeight_bound ∧
      (Memℓp mixedWeight (ENNReal.ofReal p) ↔ 3 < p) :=
  ⟨L0_ambientResolvent, mixedWeight_memℓp_iff p hp⟩

end Manuscript16.DiracMaxwellSchattenThreshold20261124

#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.abs_diracWeight
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.dirac_shell_tsum
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.dirac_summable_iff
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.shell_bound
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.abs_maxwellWeight
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.maxwellMajorant_nonneg
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.maxwell_le_majorant
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.shifted_summable
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.shifted_tsum
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.maxwellMajorant_summable
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.maxwellMajorant_tsum
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.maxwell_fiber_summable
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.maxwell_fiber_tsum_le
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.maxwell_summable
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.norm_mixedWeight_inl
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.norm_mixedWeight_inr
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.mixedWeight_summable_iff
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.mixedWeight_memℓp_iff
#print axioms Manuscript16.DiracMaxwellSchattenThreshold20261124.L0_resolvent_weights_memℓp_iff
