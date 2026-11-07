import Mathlib

/-!
# Manuscript 14, Theorem 4.2: the Eulerian distribution in a magnetic field

This module kernel-checks Theorem 4.2 of manuscript 14 ("Eulerian Fourier profiles at the
special point i/√2"), previously certified only numerically (pull request 40), apart from the
classical inputs stated below.

* (i) `logB_hasDerivAt`, `logB_mean`: with `B(u) = (u - 1)/log u` and `u = e^H`,
  `u ∂_u log B(u) = d/dH log((e^H - 1)/H) = e^H/(e^H - 1) - 1/H = [1 + L(H/2)]/2`;
  `meanField_hasDerivAt`: its derivative is `L'(H/2)/4`, `L'(y) = 1/y² - 1/sinh² y`;
  `quasiPower_mean`: the factor `B(u)^{n+1}` gives the mean `(n + 1)[1 + L(H/2)]/2`;
  `tilt_mean`, `tilt_variance`: for any finite law tilted by `u^k = e^{kH}`, the mean is
  `d/dH log Z` and the variance is the derivative of the mean, `(u ∂_u)² log A_n(u)`.
* (ii) `cnt_descent`, `cnt_adjacent`, `cnt_disjoint`: in a uniform permutation of `n` letters,
  `P(D_i) = 1/2`, `P(D_i ∧ D_{i+1}) = 1/6`, and `P(D_i ∧ D_j) = 1/4` for `|i - j| ≥ 2`;
  `spin_corr_adjacent`, `spin_corr_disjoint`: `E[s_i s_{i+1}] = -1/3`, `E[s_i s_j] = 0`;
  `descent_mean`, `descent_variance`: `E[∑ D_i] = (n - 1)/2` and `Var[∑ D_i] = (n + 1)/12`;
  `descent_kernel`: `1/(1 - e^z) = [1 - L(z/2)]/2 - 1/z`, the generating function of the
  descent kernel of Borodin–Diaconis–Fulman.
* (iii) `ising_factor`, `ising_field`: if `A_n(u) = u ∏_j (u - α_j)/(1 - α_j)` with all
  `α_j < 0`, the tilted law of `k - 1` has generating function `∏_j (1 - q_j + q_j t)`,
  `q_j = u/(u - α_j) = e^{h_j}/(e^{h_j} + e^{-h_j})`, `h_j = [H - log(-α_j)]/2`: independent
  Ising spins in the fields `h_j`.
* (iv) `field_profile`, `partition_H0`, `inversion_field_axis`, `doubling_meets_inversion`:
  `e^{-H/2} B(e^H) = sinh(H/2)/(H/2)`, which at `H₀ = -1/√2` is `sinh(a)/a = r_E(z₀)`; the
  modular inversion acts on the field axis as `H ↦ 1/H` with fixed point `H = -1`, and meets the
  doubling `H ↦ 2H` exactly at `H₀`, with `H₁ = 2H₀ = 1/H₀ = -√2`.

Classical inputs (not formalised): the quasi-power asymptotics `A_n(u) = B(u)^{n+1}[1 + O(2^{-n})]`
(Flajolet–Sedgewick), the real, simple, negative zeros of `A_n` (Frobenius), and the theorem of
Borodin–Diaconis–Fulman that the descent process is determinantal with kernel `1/(1 - e^z)`.
-/

open Finset
open scoped Nat Classical

noncomputable section

namespace Manuscript14Theorem42

/-! ## (i) The mean field of the quasi-power -/

/-- The Langevin function. -/
def L (y : ℝ) : ℝ := Real.cosh y / Real.sinh y - 1 / y

/-- Its derivative. -/
def L' (y : ℝ) : ℝ := 1 / y ^ 2 - 1 / Real.sinh y ^ 2

theorem sinh_ne_zero {y : ℝ} (hy : y ≠ 0) : Real.sinh y ≠ 0 := fun h => hy (Real.sinh_eq_zero.mp h)

theorem exp_sub_one_div_pos {H : ℝ} (hH : H ≠ 0) : 0 < (Real.exp H - 1) / H := by
  rcases lt_or_gt_of_ne hH with h | h
  · apply div_pos_of_neg_of_neg _ h
    linarith [Real.exp_lt_one.mpr h]
  · apply div_pos _ h
    linarith [Real.one_lt_exp.mpr h]

/-- `e^H/(e^H - 1) - 1/H = [1 + L(H/2)]/2`. -/
theorem mean_field_eq {H : ℝ} (hH : H ≠ 0) :
    Real.exp H / (Real.exp H - 1) - 1 / H = (1 + L (H / 2)) / 2 := by
  have hH2 : H / 2 ≠ 0 := by positivity
  have hs := sinh_ne_zero hH2
  set t := Real.exp (H / 2) with ht
  have htpos : 0 < t := Real.exp_pos _
  have he : Real.exp H = t ^ 2 := by
    rw [ht, sq, ← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (-(H / 2)) = t⁻¹ := by rw [Real.exp_neg]
  have hsinh : Real.sinh (H / 2) = (t - t⁻¹) / 2 := by rw [Real.sinh_eq, hneg]
  have hcosh : Real.cosh (H / 2) = (t + t⁻¹) / 2 := by rw [Real.cosh_eq, hneg]
  have ht1 : t ^ 2 - 1 ≠ 0 := by
    intro h
    apply hs
    rw [hsinh]
    have ht0 : t ≠ 0 := htpos.ne'
    rw [div_eq_zero_iff, sub_eq_zero]
    left
    field_simp
    linear_combination h
  unfold L
  rw [he, hsinh, hcosh]
  have ht0 : t ≠ 0 := htpos.ne'
  have hd : t - t⁻¹ ≠ 0 := by
    intro h
    apply ht1
    field_simp at h
    linear_combination h
  have hd2 : t * t - 1 ≠ 0 := by
    intro h
    apply ht1
    linear_combination h
  first
    | (field_simp; ring1)
    | field_simp

/-- **Theorem 4.2 (i)**: `d/dH log B(e^H) = e^H/(e^H - 1) - 1/H = [1 + L(H/2)]/2`. -/
theorem logB_hasDerivAt {H : ℝ} (hH : H ≠ 0) :
    HasDerivAt (fun H => Real.log ((Real.exp H - 1) / H)) ((1 + L (H / 2)) / 2) H := by
  have hf : HasDerivAt (fun H => (Real.exp H - 1) / H)
      (((Real.exp H) * H - (Real.exp H - 1) * 1) / H ^ 2) H :=
    ((Real.hasDerivAt_exp H).sub_const 1).div (hasDerivAt_id H) hH
  have h := hf.log (exp_sub_one_div_pos hH).ne'
  rw [← mean_field_eq hH]
  convert h using 1
  have he : Real.exp H - 1 ≠ 0 := by
    intro h0
    have := exp_sub_one_div_pos hH
    rw [h0, zero_div] at this
    exact lt_irrefl _ this
  first
    | (field_simp; ring1)
    | field_simp

/-- **Theorem 4.2 (i)**: the mean `(n + 1)[1 + L(H/2)]/2` of the quasi-power `B(u)^{n+1}`. -/
theorem quasiPower_mean (n : ℕ) {H : ℝ} (hH : H ≠ 0) :
    HasDerivAt (fun H => ((n : ℝ) + 1) * Real.log ((Real.exp H - 1) / H))
      (((n : ℝ) + 1) * ((1 + L (H / 2)) / 2)) H :=
  (logB_hasDerivAt hH).const_mul _

theorem L_hasDerivAt {y : ℝ} (hy : y ≠ 0) : HasDerivAt L (L' y) y := by
  have hs := sinh_ne_zero hy
  have h1 : HasDerivAt (fun y => Real.cosh y / Real.sinh y)
      ((Real.sinh y * Real.sinh y - Real.cosh y * Real.cosh y) / Real.sinh y ^ 2) y :=
    (Real.hasDerivAt_cosh y).div (Real.hasDerivAt_sinh y) hs
  have h2 : HasDerivAt (fun y : ℝ => 1 / y) (-(1 / y ^ 2)) y := by
    have := (hasDerivAt_inv hy)
    simpa [one_div] using this
  have h := h1.sub h2
  unfold L L'
  convert h using 1
  have hc := Real.cosh_sq_sub_sinh_sq y
  have hc' : Real.cosh y * Real.cosh y = 1 + Real.sinh y * Real.sinh y := by
    rw [← sq, ← sq]
    linarith
  rw [hc']
  first
    | (field_simp; ring1)
    | field_simp

/-- **Theorem 4.2 (i)**: the derivative of the mean field is `L'(H/2)/4`. -/
theorem meanField_hasDerivAt {H : ℝ} (hH : H ≠ 0) :
    HasDerivAt (fun H => (1 + L (H / 2)) / 2) (L' (H / 2) / 4) H := by
  have hH2 : H / 2 ≠ 0 := by positivity
  have h := ((L_hasDerivAt hH2).comp H ((hasDerivAt_id H).div_const 2)).const_add 1
  have h' := h.div_const 2
  convert h' using 1 <;> first
    | ring1
    | (funext x; simp [Function.comp_def])
    | rfl

/-- A finite law `p_k` tilted by `e^{kH}`: the partition function `Z(H) = ∑ p_k e^{kH}`. -/
def Z (N : ℕ) (p : ℕ → ℝ) (H : ℝ) : ℝ := ∑ k ∈ range N, p k * Real.exp (k * H)

/-- First moment `∑ k p_k e^{kH}`. -/
def Z1 (N : ℕ) (p : ℕ → ℝ) (H : ℝ) : ℝ := ∑ k ∈ range N, p k * k * Real.exp (k * H)

/-- Second moment `∑ k² p_k e^{kH}`. -/
def Z2 (N : ℕ) (p : ℕ → ℝ) (H : ℝ) : ℝ := ∑ k ∈ range N, p k * k ^ 2 * Real.exp (k * H)

theorem Z_hasDerivAt (N : ℕ) (p : ℕ → ℝ) (H : ℝ) : HasDerivAt (Z N p) (Z1 N p H) H := by
  have hterm : ∀ k ∈ range N, HasDerivAt (fun H : ℝ => p k * Real.exp (k * H))
      (p k * k * Real.exp (k * H)) H := by
    intro k _
    have := (((hasDerivAt_id H).const_mul (k : ℝ)).exp).const_mul (p k)
    simp only [id, mul_one] at this
    convert this using 1
    ring
  unfold Z Z1
  first
    | exact HasDerivAt.fun_sum hterm
    | (convert HasDerivAt.sum hterm using 1; funext y; simp [Finset.sum_apply])

theorem Z1_hasDerivAt (N : ℕ) (p : ℕ → ℝ) (H : ℝ) : HasDerivAt (Z1 N p) (Z2 N p H) H := by
  have hterm : ∀ k ∈ range N, HasDerivAt (fun H : ℝ => p k * k * Real.exp (k * H))
      (p k * k ^ 2 * Real.exp (k * H)) H := by
    intro k _
    have := (((hasDerivAt_id H).const_mul (k : ℝ)).exp).const_mul (p k * k)
    simp only [id, mul_one] at this
    convert this using 1
    ring
  unfold Z1 Z2
  first
    | exact HasDerivAt.fun_sum hterm
    | (convert HasDerivAt.sum hterm using 1; funext y; simp [Finset.sum_apply])

/-- **Theorem 4.2 (i)**: the tilted mean is `d/dH log Z = u ∂_u log A_n(u)`. -/
theorem tilt_mean (N : ℕ) (p : ℕ → ℝ) (H : ℝ) (hZ : 0 < Z N p H) :
    HasDerivAt (fun H => Real.log (Z N p H)) (Z1 N p H / Z N p H) H :=
  (Z_hasDerivAt N p H).log hZ.ne'

/-- **Theorem 4.2 (i)**: the tilted variance `∑ k² p_k e^{kH}/Z - (mean)²` is the derivative of
the mean, `(u ∂_u)² log A_n(u)`. -/
theorem tilt_variance (N : ℕ) (p : ℕ → ℝ) (H : ℝ) (hZ : Z N p H ≠ 0) :
    HasDerivAt (fun H => Z1 N p H / Z N p H)
      (Z2 N p H / Z N p H - (Z1 N p H / Z N p H) ^ 2) H := by
  have h := (Z1_hasDerivAt N p H).div (Z_hasDerivAt N p H) hZ
  convert h using 1
  first
    | (field_simp; ring1)
    | field_simp

/-! ## (ii) The descent spins of a uniform permutation -/

variable {n : ℕ}

/-- The number of permutations of `Fin n` with property `A`. -/
def cnt (A : Equiv.Perm (Fin n) → Prop) : ℕ := ∑ σ : Equiv.Perm (Fin n), if A σ then 1 else 0

theorem cnt_mul_right (A : Equiv.Perm (Fin n) → Prop) (ρ : Equiv.Perm (Fin n)) :
    (∑ σ : Equiv.Perm (Fin n), if A (σ * ρ) then 1 else 0) = cnt A := by
  unfold cnt
  first
    | exact Equiv.sum_comp (Equiv.mulRight ρ) (fun σ => if A σ then 1 else 0)
    | simpa using Equiv.sum_comp (Equiv.mulRight ρ) (fun σ => if A σ then 1 else 0)

/-- If, for every `σ`, exactly one of the right translates `σ ρ_r` has property `A`, then
`k · #A = n!`. -/
theorem cnt_of_partition {k : ℕ} (A : Equiv.Perm (Fin n) → Prop) (ρ : Fin k → Equiv.Perm (Fin n))
    (h : ∀ σ : Equiv.Perm (Fin n), (∑ r : Fin k, if A (σ * ρ r) then 1 else 0) = 1) :
    k * cnt A = n ! := by
  have h1 : (∑ σ : Equiv.Perm (Fin n), ∑ r : Fin k, (if A (σ * ρ r) then 1 else 0 : ℕ)) = n ! := by
    rw [Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun r _ => cnt_mul_right A (ρ r)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  exact h1

theorem cnt_pair (a b : Fin n) (hab : a ≠ b) :
    2 * cnt (fun σ : Equiv.Perm (Fin n) => σ b < σ a) = n ! := by
  apply cnt_of_partition _ ![1, Equiv.swap a b]
  intro σ
  have hne : σ a ≠ σ b := σ.injective.ne hab
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rcases lt_or_gt_of_ne hne with h | h <;> simp [h, lt_asymm h]

theorem cnt_triple (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    6 * cnt (fun σ : Equiv.Perm (Fin n) => σ b < σ a ∧ σ c < σ b) = n ! := by
  apply cnt_of_partition _ ![1, Equiv.swap a b, Equiv.swap b c, Equiv.swap a c,
    Equiv.swap a b * Equiv.swap b c, Equiv.swap b c * Equiv.swap a b]
  intro σ
  have hne1 : σ a ≠ σ b := σ.injective.ne hab
  have hne2 : σ b ≠ σ c := σ.injective.ne hbc
  have hne3 : σ a ≠ σ c := σ.injective.ne hac
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne, hab, hbc, hac, hab.symm, hbc.symm, hac.symm, ne_eq,
    not_false_eq_true]
  rcases lt_or_gt_of_ne hne1 with h1 | h1 <;> rcases lt_or_gt_of_ne hne2 with h2 | h2 <;>
    rcases lt_or_gt_of_ne hne3 with h3 | h3 <;>
    first
      | (exfalso; simp only [Fin.lt_iff_val_lt_val, gt_iff_lt] at h1 h2 h3; omega)
      | simp [h1, h2, h3, lt_asymm h1, lt_asymm h2, lt_asymm h3]

theorem cnt_quad (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    4 * cnt (fun σ : Equiv.Perm (Fin n) => σ b < σ a ∧ σ d < σ c) = n ! := by
  apply cnt_of_partition _ ![1, Equiv.swap a b, Equiv.swap c d, Equiv.swap a b * Equiv.swap c d]
  intro σ
  have hne1 : σ a ≠ σ b := σ.injective.ne hab
  have hne2 : σ c ≠ σ d := σ.injective.ne hcd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne, hab, hcd, hac, had, hbc, hbd, hab.symm, hcd.symm, hac.symm,
    had.symm, hbc.symm, hbd.symm, ne_eq, not_false_eq_true]
  rcases lt_or_gt_of_ne hne1 with h1 | h1 <;> rcases lt_or_gt_of_ne hne2 with h2 | h2 <;>
    simp [h1, h2, lt_asymm h1, lt_asymm h2]

/-- The descent at position `i`: `σ(i) > σ(i+1)` (positions counted from `0`). -/
def D (i : ℕ) (σ : Equiv.Perm (Fin n)) : Prop := ∃ h : i + 1 < n, σ ⟨i + 1, h⟩ < σ ⟨i, by omega⟩

theorem D_eq (i : ℕ) (hi : i + 1 < n) :
    (D i : Equiv.Perm (Fin n) → Prop) = fun σ => σ ⟨i + 1, hi⟩ < σ ⟨i, by omega⟩ := by
  funext σ
  exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨hi, h⟩⟩

/-- **Theorem 4.2 (ii)**: `P(D_i) = 1/2`. -/
theorem cnt_descent (i : ℕ) (hi : i + 1 < n) : 2 * cnt (D i : Equiv.Perm (Fin n) → Prop) = n ! := by
  rw [D_eq i hi]
  exact cnt_pair _ _ (fun h => by simp [Fin.ext_iff] at h)

/-- **Theorem 4.2 (ii)**: `P(D_i ∧ D_{i+1}) = 1/6`. -/
theorem cnt_adjacent (i : ℕ) (hi : i + 2 < n) :
    6 * cnt (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D (i + 1) σ) = n ! := by
  have e : (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D (i + 1) σ) =
      fun σ => σ ⟨i + 1, by omega⟩ < σ ⟨i, by omega⟩ ∧ σ ⟨i + 2, hi⟩ < σ ⟨i + 1, by omega⟩ := by
    funext σ
    rw [D_eq i (by omega), D_eq (i + 1) hi]
  rw [e]
  exact cnt_triple _ _ _ (fun h => by simp [Fin.ext_iff] at h) (fun h => by simp [Fin.ext_iff] at h)
    (fun h => by simp [Fin.ext_iff] at h)

/-- **Theorem 4.2 (ii)**: `P(D_i ∧ D_j) = 1/4` for `j ≥ i + 2`. -/
theorem cnt_disjoint (i j : ℕ) (hij : i + 2 ≤ j) (hj : j + 1 < n) :
    4 * cnt (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D j σ) = n ! := by
  have e : (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D j σ) =
      fun σ => σ ⟨i + 1, by omega⟩ < σ ⟨i, by omega⟩ ∧ σ ⟨j + 1, hj⟩ < σ ⟨j, by omega⟩ := by
    funext σ
    rw [D_eq i (by omega), D_eq j hj]
  rw [e]
  apply cnt_quad <;> intro h <;> simp [Fin.ext_iff] at h <;> omega

theorem cnt_and_comm (A B : Equiv.Perm (Fin n) → Prop) :
    cnt (fun σ => A σ ∧ B σ) = cnt (fun σ => B σ ∧ A σ) := by
  unfold cnt
  apply Finset.sum_congr rfl
  intro σ _
  show (if A σ ∧ B σ then 1 else 0) = (if B σ ∧ A σ then 1 else 0)
  by_cases h : A σ ∧ B σ
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem cast_cnt (A : Equiv.Perm (Fin n) → Prop) :
    (cnt A : ℚ) = ∑ σ : Equiv.Perm (Fin n), if A σ then (1 : ℚ) else 0 := by
  unfold cnt
  push_cast
  try rfl

theorem sum_ite_and (A B : Equiv.Perm (Fin n) → Prop) :
    (∑ σ : Equiv.Perm (Fin n), if A σ ∧ B σ then (1 : ℚ) else 0) =
      (cnt (fun σ => A σ ∧ B σ) : ℚ) := by
  rw [cast_cnt]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : A σ ∧ B σ
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem spin_corr_sum (A B : Equiv.Perm (Fin n) → Prop) :
    (∑ σ : Equiv.Perm (Fin n), (if A σ then (1 : ℚ) else -1) * (if B σ then (1 : ℚ) else -1)) =
      4 * (cnt (fun σ => A σ ∧ B σ) : ℚ) - 2 * (cnt A : ℚ) - 2 * (cnt B : ℚ) + (n ! : ℚ) := by
  have hpt : ∀ σ, (if A σ then (1 : ℚ) else -1) * (if B σ then (1 : ℚ) else -1) =
      4 * (if A σ ∧ B σ then (1 : ℚ) else 0) - 2 * (if A σ then (1 : ℚ) else 0) -
        2 * (if B σ then (1 : ℚ) else 0) + 1 := by
    intro σ
    by_cases hA : A σ <;> by_cases hB : B σ <;> simp [hA, hB] <;> norm_num
  rw [Finset.sum_congr rfl (fun σ _ => hpt σ)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [sum_ite_and, ← cast_cnt, ← cast_cnt]

/-- **Theorem 4.2 (ii)**: `E[s_i s_{i+1}] = -1/3` for the descent spins `s_i = 2 D_i - 1`. -/
theorem spin_corr_adjacent (i : ℕ) (hi : i + 2 < n) :
    (∑ σ : Equiv.Perm (Fin n), (if D i σ then (1 : ℚ) else -1) *
      (if D (i + 1) σ then (1 : ℚ) else -1)) / (n ! : ℚ) = -1 / 3 := by
  have h1 : 2 * (cnt (D i : Equiv.Perm (Fin n) → Prop) : ℚ) = n ! := by
    exact_mod_cast cnt_descent i (by omega)
  have h2 : 2 * (cnt (D (i + 1) : Equiv.Perm (Fin n) → Prop) : ℚ) = n ! := by
    exact_mod_cast cnt_descent (i + 1) (by omega)
  have h3 : 6 * (cnt (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D (i + 1) σ) : ℚ) = n ! := by
    exact_mod_cast cnt_adjacent i hi
  have hN : (n ! : ℚ) ≠ 0 := by positivity
  rw [spin_corr_sum, div_eq_iff hN]
  linarith

/-- **Theorem 4.2 (ii)**: `E[s_i s_j] = 0` for `j ≥ i + 2`. -/
theorem spin_corr_disjoint (i j : ℕ) (hij : i + 2 ≤ j) (hj : j + 1 < n) :
    (∑ σ : Equiv.Perm (Fin n), (if D i σ then (1 : ℚ) else -1) *
      (if D j σ then (1 : ℚ) else -1)) / (n ! : ℚ) = 0 := by
  have h1 : 2 * (cnt (D i : Equiv.Perm (Fin n) → Prop) : ℚ) = n ! := by
    exact_mod_cast cnt_descent i (by omega)
  have h2 : 2 * (cnt (D j : Equiv.Perm (Fin n) → Prop) : ℚ) = n ! := by
    exact_mod_cast cnt_descent j hj
  have h3 : 4 * (cnt (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D j σ) : ℚ) = n ! := by
    exact_mod_cast cnt_disjoint i j hij hj
  have hN : (n ! : ℚ) ≠ 0 := by positivity
  rw [spin_corr_sum, div_eq_iff hN]
  linarith

/-- The pair probabilities `P(D_i ∧ D_j)` for `i, j ≤ n - 2`. -/
def q (i j : ℕ) : ℚ := if i = j then 1 / 2 else if i = j + 1 ∨ j = i + 1 then 1 / 6 else 1 / 4

theorem cnt_pair_q (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) :
    (cnt (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D j σ) : ℚ) = (n ! : ℚ) * q i j := by
  unfold q
  by_cases hij : i = j
  · subst hij
    have h := cnt_descent (n := n) i hi
    have e : (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D i σ) = D i := by
      funext σ
      exact propext and_self_iff
    rw [e, if_pos rfl]
    have h' : 2 * (cnt (D i : Equiv.Perm (Fin n) → Prop) : ℚ) = n ! := by exact_mod_cast h
    linarith
  · rw [if_neg hij]
    by_cases hadj : i = j + 1 ∨ j = i + 1
    · rw [if_pos hadj]
      rcases hadj with h | h
      · subst h
        rw [cnt_and_comm]
        have h' : 6 * (cnt (fun σ : Equiv.Perm (Fin n) => D j σ ∧ D (j + 1) σ) : ℚ) = n ! := by
          exact_mod_cast cnt_adjacent j (by omega)
        linarith
      · subst h
        have h' : 6 * (cnt (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D (i + 1) σ) : ℚ) = n ! := by
          exact_mod_cast cnt_adjacent i (by omega)
        linarith
    · rw [if_neg hadj]
      rcases lt_or_gt_of_ne hij with h | h
      · have h' : 4 * (cnt (fun σ : Equiv.Perm (Fin n) => D i σ ∧ D j σ) : ℚ) = n ! := by
          exact_mod_cast cnt_disjoint i j (by omega) hj
        linarith
      · rw [cnt_and_comm]
        have h' : 4 * (cnt (fun σ : Equiv.Perm (Fin n) => D j σ ∧ D i σ) : ℚ) = n ! := by
          exact_mod_cast cnt_disjoint j i (by omega) hi
        linarith

theorem col_sum (k : ℕ) : ∑ i ∈ range k, q i (k + 1) = (k : ℚ) / 4 := by
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ) / 4)]
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  · intro i hi
    rw [Finset.mem_range] at hi
    unfold q
    split_ifs <;> first | rfl | (exfalso; omega)

theorem row_sum (k : ℕ) : ∑ j ∈ range k, q (k + 1) j = (k : ℚ) / 4 := by
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ) / 4)]
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  · intro j hj
    rw [Finset.mem_range] at hj
    unfold q
    split_ifs <;> first | rfl | (exfalso; omega)

theorem sum_square_succ (f : ℕ → ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1), f i j =
      ∑ i ∈ range m, ∑ j ∈ range m, f i j + ∑ i ∈ range m, f i m + ∑ j ∈ range m, f m j + f m m := by
  have h1 : ∀ i, ∑ j ∈ range (m + 1), f i j = ∑ j ∈ range m, f i j + f i m :=
    fun i => Finset.sum_range_succ (f i) m
  simp_rw [h1]
  rw [Finset.sum_range_succ, Finset.sum_add_distrib]
  ring

theorem double_sum_q (k : ℕ) :
    ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), q i j =
      ((k : ℚ) + 1) ^ 2 / 4 + ((k : ℚ) + 1) / 4 - (k : ℚ) / 6 := by
  induction k with
  | zero =>
    norm_num [q, Finset.sum_range_one]
  | succ k ih =>
    have h1 : q k (k + 1) = 1 / 6 := by
      unfold q
      split_ifs <;> first | rfl | (exfalso; omega)
    have h2 : q (k + 1) k = 1 / 6 := by
      unfold q
      split_ifs <;> first | rfl | (exfalso; omega)
    have h3 : q (k + 1) (k + 1) = 1 / 2 := by
      unfold q
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [sum_square_succ q (k + 1), ih, Finset.sum_range_succ (fun i => q i (k + 1)),
      Finset.sum_range_succ (fun j => q (k + 1) j), col_sum, row_sum, h1, h2, h3]
    push_cast
    ring

/-- The number of descents `∑_{i ≤ n-2} D_i` as a rational. -/
def Ndes (σ : Equiv.Perm (Fin n)) : ℚ := ∑ i ∈ range (n - 1), if D i σ then (1 : ℚ) else 0

theorem ite_mul_ite (P R : Prop) :
    (if P then (1 : ℚ) else 0) * (if R then (1 : ℚ) else 0) = if P ∧ R then (1 : ℚ) else 0 := by
  by_cases hP : P <;> by_cases hR : R <;> simp [hP, hR]

/-- **Theorem 4.2 (ii)**: `E[∑ D_i] = (n - 1)/2`. -/
theorem descent_mean (m : ℕ) :
    (∑ σ : Equiv.Perm (Fin (m + 1)), Ndes σ) / ((m + 1) ! : ℚ) = (m : ℚ) / 2 := by
  have hN : (((m + 1) ! : ℕ) : ℚ) ≠ 0 := by positivity
  have hc : ∀ i ∈ range m, (∑ σ : Equiv.Perm (Fin (m + 1)), if D i σ then (1 : ℚ) else 0) =
      (((m + 1) ! : ℕ) : ℚ) / 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← cast_cnt]
    have h := cnt_descent (n := m + 1) i (by omega)
    have h' : 2 * (cnt (D i : Equiv.Perm (Fin (m + 1)) → Prop) : ℚ) = ((m + 1) ! : ℕ) := by
      exact_mod_cast h
    linarith
  unfold Ndes
  rw [Finset.sum_comm, show m + 1 - 1 = m by omega, Finset.sum_congr rfl hc, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  first
    | (field_simp; ring1)
    | field_simp

/-- **Theorem 4.2 (ii)**: `Var[∑ D_i] = (n + 1)/12` for `n = m + 2 ≥ 2` letters. -/
theorem descent_variance (k : ℕ) :
    (∑ σ : Equiv.Perm (Fin (k + 2)), Ndes σ ^ 2) / ((k + 2) ! : ℚ) -
      ((∑ σ : Equiv.Perm (Fin (k + 2)), Ndes σ) / ((k + 2) ! : ℚ)) ^ 2 =
        ((k : ℚ) + 3) / 12 := by
  have hN : (((k + 2) ! : ℕ) : ℚ) ≠ 0 := by positivity
  have hmean : (∑ σ : Equiv.Perm (Fin (k + 2)), Ndes σ) / ((k + 2) ! : ℚ) = ((k : ℚ) + 1) / 2 := by
    have := descent_mean (k + 1)
    push_cast at this
    exact this
  rw [hmean]
  have hsq : (∑ σ : Equiv.Perm (Fin (k + 2)), Ndes σ ^ 2) =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
        (cnt (fun σ : Equiv.Perm (Fin (k + 2)) => D i σ ∧ D j σ) : ℚ) := by
    unfold Ndes
    rw [show k + 2 - 1 = k + 1 by omega]
    simp_rw [sq, Finset.sum_mul_sum, ite_mul_ite]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact sum_ite_and (D i) (D j)
  rw [hsq]
  have hq : ∀ i ∈ range (k + 1), ∀ j ∈ range (k + 1),
      (cnt (fun σ : Equiv.Perm (Fin (k + 2)) => D i σ ∧ D j σ) : ℚ) =
        (((k + 2) ! : ℕ) : ℚ) * q i j := by
    intro i hi j hj
    rw [Finset.mem_range] at hi hj
    exact cnt_pair_q i j (by omega) (by omega)
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hq i hi j hj))]
  simp_rw [← Finset.mul_sum]
  rw [double_sum_q k, mul_div_cancel_left₀ _ hN]
  ring

/-- **Theorem 4.2 (ii)**, (48): the generating function of the descent kernel,
`1/(1 - e^z) = [1 - L(z/2)]/2 - 1/z`, for `z ≠ 0` with `e^z ≠ 1`. -/
theorem descent_kernel (z : ℂ) (hz : z ≠ 0) (hez : Complex.exp z ≠ 1) :
    1 / (1 - Complex.exp z) =
      (1 - (Complex.cosh (z / 2) / Complex.sinh (z / 2) - 1 / (z / 2))) / 2 - 1 / z := by
  set t := Complex.exp (z / 2) with ht
  have ht0 : t ≠ 0 := Complex.exp_ne_zero _
  have he : Complex.exp z = t ^ 2 := by
    rw [ht, sq, ← Complex.exp_add]
    congr 1
    ring
  have hneg : Complex.exp (-(z / 2)) = t⁻¹ := by rw [Complex.exp_neg]
  have hsinh : Complex.sinh (z / 2) = (t - t⁻¹) / 2 := by
    rw [Complex.sinh, hneg]
  have hcosh : Complex.cosh (z / 2) = (t + t⁻¹) / 2 := by
    rw [Complex.cosh, hneg]
  rw [he] at hez ⊢
  have h1 : 1 - t ^ 2 ≠ 0 := fun h => hez (by linear_combination -h)
  have h3 : t ^ 2 - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  have h4 : t * t - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  have h2 : t - t⁻¹ ≠ 0 := by
    intro h
    apply h3
    field_simp at h
    linear_combination h
  rw [hsinh, hcosh]
  first
    | (field_simp; ring1)
    | field_simp

/-! ## (iii) Independent Ising spins -/

/-- **Theorem 4.2 (iii)**: if `A_n(u)/u = ∏_j (u - α_j)/(1 - α_j)`, the generating function of
the tilted law of `k - 1` factorises into independent two-point laws with `q_j = u/(u - α_j)`. -/
theorem ising_factor {m : ℕ} (α : Fin m → ℝ) (hα : ∀ j, α j < 0) (u t : ℝ) (hu : 0 < u) :
    (∏ j, (t * u - α j) / (1 - α j)) / (∏ j, (u - α j) / (1 - α j)) =
      ∏ j, ((1 - u / (u - α j)) + u / (u - α j) * t) := by
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have h1 : u - α j ≠ 0 := by linarith [hα j]
  have h2 : 1 - α j ≠ 0 := by linarith [hα j]
  first
    | (field_simp; ring1)
    | field_simp

/-- **Theorem 4.2 (iii)**: `q_j = u/(u - α_j) = e^{h_j}/(e^{h_j} + e^{-h_j})` with
`h_j = [H - log(-α_j)]/2` and `u = e^H`: an Ising spin in the field `h_j`. -/
theorem ising_field (α H : ℝ) (hα : α < 0) :
    Real.exp H / (Real.exp H - α) =
      Real.exp ((H - Real.log (-α)) / 2) /
        (Real.exp ((H - Real.log (-α)) / 2) + Real.exp (-((H - Real.log (-α)) / 2))) := by
  have hE2 : Real.exp ((H - Real.log (-α)) / 2) ^ 2 = Real.exp H / (-α) := by
    rw [sq, ← Real.exp_add, show (H - Real.log (-α)) / 2 + (H - Real.log (-α)) / 2 =
      H - Real.log (-α) by ring, Real.exp_sub, Real.exp_log (by linarith)]
  rw [Real.exp_neg]
  set E := Real.exp ((H - Real.log (-α)) / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE0 : E ≠ 0 := hEpos.ne'
  have hu : 0 < Real.exp H := Real.exp_pos H
  have h1 : Real.exp H - α ≠ 0 := by linarith
  have hα' : -α ≠ 0 := by linarith
  have hEi : 0 < E⁻¹ := inv_pos.mpr hEpos
  have hs1 : E + E⁻¹ ≠ 0 := ne_of_gt (by linarith)
  have hs2 : E ^ 2 + 1 ≠ 0 := by positivity
  have e : E / (E + E⁻¹) = E ^ 2 / (E ^ 2 + 1) := by
    rw [div_eq_div_iff hs1 hs2]
    first
      | (field_simp; ring1)
      | field_simp
  rw [e, hE2, div_add_one hα', div_div_div_cancel_right₀ hα']
  all_goals first
    | (congr 1; ring1)
    | congr 1

/-! ## (iv) The special fields -/

/-- `e^{-H/2} B(e^H) = sinh(H/2)/(H/2)`: the profile on the field axis. -/
theorem field_profile {H : ℝ} (hH : H ≠ 0) :
    Real.exp (-(H / 2)) * ((Real.exp H - 1) / H) = Real.sinh (H / 2) / (H / 2) := by
  set t := Real.exp (H / 2) with ht
  have htpos : 0 < t := Real.exp_pos _
  have he : Real.exp H = t ^ 2 := by
    rw [ht, sq, ← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, Real.exp_neg, ← ht, he]
  have ht0 : t ≠ 0 := htpos.ne'
  first
    | (field_simp; ring1)
    | field_simp

/-- **Theorem 4.2 (iv)**: at `H₀ = -1/√2`, `e^{a} B(e^{-2a}) = sinh(a)/a = r_E(z₀)`,
`a = 1/√8`. -/
theorem partition_H0 :
    Real.exp (1 / Real.sqrt 8) * ((Real.exp (-(2 / Real.sqrt 8)) - 1) / (-(2 / Real.sqrt 8))) =
      Real.sinh (1 / Real.sqrt 8) / (1 / Real.sqrt 8) := by
  have h8 : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hH : (-(2 / Real.sqrt 8)) ≠ 0 := by
    have : 0 < 2 / Real.sqrt 8 := by positivity
    linarith
  have h := field_profile hH
  have e1 : -(-(2 / Real.sqrt 8) / 2) = 1 / Real.sqrt 8 := by ring
  have e2 : -(2 / Real.sqrt 8) / 2 = -(1 / Real.sqrt 8) := by ring
  rw [e1, e2, Real.sinh_neg, neg_div_neg_eq] at h
  exact h

/-- `2/√8 = 1/√2`: the field `H₀ = -2a` is `-1/√2`. -/
theorem H0_eq : 2 / Real.sqrt 8 = 1 / Real.sqrt 2 := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [h8]
  first
    | (field_simp; ring1)
    | field_simp
    | (rw [div_mul_eq_div_div, div_self (by norm_num : (2 : ℝ) ≠ 0)])

/-- **Theorem 4.2 (iv)**: the modular inversion on the field axis, `S(it) = i/t`. -/
theorem inversion_field_axis (t : ℝ) (ht : t ≠ 0) :
    -1 / (Complex.I * t) = Complex.I * (1 / t) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [div_eq_iff (mul_ne_zero Complex.I_ne_zero ht')]
  have e : Complex.I * (1 / (t : ℂ)) * (Complex.I * (t : ℂ)) =
      Complex.I * Complex.I * ((t : ℂ) / (t : ℂ)) := by ring
  rw [e, Complex.I_mul_I, div_self ht']
  ring

/-- **Theorem 4.2 (iv)**: on the negative field axis `H ↦ 1/H` fixes only `H = -1`, and
meets the doubling `H ↦ 2H` exactly at `H₀ = -1/√2`; there `H₁ = 2H₀ = 1/H₀ = -√2`. -/
theorem doubling_meets_inversion (H : ℝ) (hH : H < 0) :
    (1 / H = H ↔ H = -1) ∧ (1 / H = 2 * H ↔ H = -(1 / Real.sqrt 2)) := by
  have h0 : H ≠ 0 := hH.ne
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · rw [div_eq_iff h0]
    constructor
    · intro h
      have hf : (H + 1) * (H - 1) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp hf with h1 | h1
      · linarith
      · linarith
    · intro h
      subst h
      norm_num
  · rw [div_eq_iff h0]
    constructor
    · intro h
      have hsq : (H * Real.sqrt 2) ^ 2 = 1 := by
        rw [mul_pow, hs]
        linarith
      have hneg : H * Real.sqrt 2 < 0 := mul_neg_of_neg_of_pos hH h2
      have hf : (H * Real.sqrt 2 + 1) * (H * Real.sqrt 2 - 1) = 0 := by linear_combination hsq
      have hy : H * Real.sqrt 2 = -1 := by
        rcases mul_eq_zero.mp hf with h1 | h1
        · linarith
        · linarith
      have hH' : H = -1 / Real.sqrt 2 := by
        rw [eq_div_iff h2.ne']
        linarith
      rw [hH']
      ring
    · intro h
      subst h
      have e : 2 * -(1 / Real.sqrt 2) * -(1 / Real.sqrt 2) = 2 / Real.sqrt 2 ^ 2 := by
        field_simp
      rw [e, hs]
      norm_num

theorem H1_eq : 2 * (-(1 / Real.sqrt 2)) = 1 / (-(1 / Real.sqrt 2)) ∧
    2 * (-(1 / Real.sqrt 2)) = -Real.sqrt 2 := by
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e0 : 2 * (1 / Real.sqrt 2) = Real.sqrt 2 := by
    rw [mul_one_div, div_eq_iff h2.ne']
    linarith [hs]
  have e1 : 2 * (-(1 / Real.sqrt 2)) = -Real.sqrt 2 := by
    rw [mul_neg, e0]
  refine ⟨?_, e1⟩
  rw [e1, one_div_neg_eq_neg_one_div, one_div_one_div]

/-! ## Axiom audit -/

#print axioms logB_hasDerivAt
#print axioms quasiPower_mean
#print axioms meanField_hasDerivAt
#print axioms tilt_mean
#print axioms tilt_variance
#print axioms cnt_descent
#print axioms cnt_adjacent
#print axioms cnt_disjoint
#print axioms spin_corr_adjacent
#print axioms spin_corr_disjoint
#print axioms descent_mean
#print axioms descent_variance
#print axioms descent_kernel
#print axioms ising_factor
#print axioms ising_field
#print axioms field_profile
#print axioms partition_H0
#print axioms H0_eq
#print axioms inversion_field_axis
#print axioms doubling_meets_inversion
#print axioms H1_eq

end Manuscript14Theorem42
