import EulerianGrothendieck.UniformConvolutions
import Mathlib.Data.Fin.Tuple.Basic

/-! # Task G1, part 1: the multinomial occupancy model and Lemmas 9.3--9.4 with printed constants

`k` labelled balls are thrown independently and uniformly into `M` boxes: the sample space is
`Fin k → Fin M` with the uniform (counting) probability, `occ f j` is the occupancy of box `j`.

* `uniformMomentRatio_occupancy`: `R_{M,k} = E ∏_j ρ_{N_j}`, with `ρ = momentFactor`
  (`ρ_r = 6^r r!/(2r+1)!`);
* `expect_collisions`, `expect_collisions_falling`: for the number `L = ∑_j binom(N_j,2)` of
  colliding unordered pairs, `E L = L_k/M` and `E L(L-1) = L_k(L_k-1)/M²`
  (pairs of distinct pairs, sharing a ball or not, collide with probability `1/M²`);
* `occupancy_moment_bound` (Lemma 9.3): `0 ≤ R_{M,k} - (1 - d_k/M) ≤ L_k(L_k-1)/M²`,
  `d_k = k(k-1)/5`, `L_k = k(k-1)/2`, for every `M ≥ 1`, `k ≥ 0`;
* `occupancy_square_bound` (Lemma 9.4): `0 ≤ R_{M,k}² - (1 - 2d_k/M) ≤ 27 k²(k-1)²/(50 M²)`. -/

noncomputable section
open scoped BigOperators Nat
open Finset PowerSeries
namespace EulerianGrothendieck.Occupancy

variable {M k : ℕ}

/-- Occupancy of box `j`. -/
def occ (f : Fin k → Fin M) (j : Fin M) : ℕ := (univ.filter fun a => f a = j).card

/-- Expectation under the uniform law on assignments `Fin k → Fin M`. -/
def expect (M k : ℕ) (X : (Fin k → Fin M) → ℝ) : ℝ := (∑ f, X f) / (M:ℝ) ^ k

/-! ### Exponential generating functions and the occupancy identity -/

def egf (w : ℕ → ℝ) : PowerSeries ℝ := PowerSeries.mk fun r => w r / (r ! : ℝ)

theorem derivative_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → PowerSeries ℝ) :
    derivative ℝ (∏ i ∈ s, F i) =
      ∑ i ∈ s, ∏ j ∈ s, (if j = i then derivative ℝ (F j) else F j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Derivation.leibniz, ih, Finset.sum_insert has]
    rw [Finset.prod_insert has, if_pos rfl]
    have h1 : ∏ j ∈ s, (if j = a then derivative ℝ (F j) else F j) = ∏ j ∈ s, F j := by
      apply Finset.prod_congr rfl; intro j hj
      rw [if_neg (by rintro rfl; exact has hj)]
    rw [h1, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro i hi
      rw [Finset.prod_insert has, if_neg (by rintro rfl; exact has hi)]

theorem occ_cons (y : Fin M) (f : Fin k → Fin M) (j : Fin M) :
    occ (Fin.cons y f : Fin (k+1) → Fin M) j = occ f j + (if y = j then 1 else 0) := by
  unfold occ
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem coeff_egf_shift (w : ℕ → ℝ) :
    egf (fun r => w (r + 1)) = derivative ℝ (egf w) := by
  ext r
  rw [coeff_derivative]
  simp only [egf, coeff_mk]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- `∑_f ∏_j w_j(N_j(f)) = k! [x^k] ∏_j (∑_r w_j(r) x^r/r!)`. -/
theorem sum_prod_occ (k : ℕ) (w : Fin M → ℕ → ℝ) :
    ∑ f : Fin k → Fin M, ∏ j, w j (occ f j) = (k ! : ℝ) * coeff k (∏ j, egf (w j)) := by
  induction k generalizing w with
  | zero =>
    rw [Fintype.sum_unique, Nat.factorial_zero, Nat.cast_one, one_mul, coeff_zero_eq_constantCoeff,
      map_prod]
    apply Finset.prod_congr rfl; intro j _
    simp [occ, egf, PowerSeries.constantCoeff_mk]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Fin M)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    have hstep : ∀ y : Fin M, ∑ f : Fin k → Fin M, ∏ j, w j (occ (Fin.cons y f : Fin (k+1) → Fin M) j) =
        (k ! : ℝ) * coeff k (∏ j, (if j = y then derivative ℝ (egf (w j)) else egf (w j))) := by
      intro y
      simp_rw [occ_cons]
      rw [ih (fun j r => w j (r + if y = j then 1 else 0))]
      congr 2
      apply Finset.prod_congr rfl; intro j _
      by_cases hj : j = y
      · subst hj; rw [if_pos rfl, if_pos rfl]; exact coeff_egf_shift (w j)
      · rw [if_neg hj]; simp only [if_neg (Ne.symm hj), add_zero]
    simp_rw [hstep]
    rw [← Finset.mul_sum, ← map_sum, ← derivative_finset_prod, coeff_derivative,
      Nat.factorial_succ]
    push_cast
    ring

/-- **Occupancy representation**: `R_{M,k} = E ∏_j ρ_{N_j}`. -/
theorem uniformMomentRatio_occupancy (M k : ℕ) (hM : M ≠ 0) :
    uniformMomentRatio M k = expect M k (fun f => ∏ j, momentFactor (occ f j)) := by
  unfold expect
  rw [sum_prod_occ k (fun _ => momentFactor), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  unfold uniformMomentRatio
  rw [coeffPower_eq_powerSeries]
  have hres : PowerSeries.mk uniformEGFCoefficient = rescale (1/2 : ℝ) (egf momentFactor) := by
    ext r
    rw [coeff_mk, coeff_rescale]
    simp only [egf, coeff_mk]
    rw [uniformEGFCoefficient_factor, gaussianEGFCoefficient, one_div_pow]
    field_simp <;> ring
  rw [hres, ← map_pow, coeff_rescale, one_div_pow]
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  field_simp <;> ring

/-! ### Collisions -/

/-- Indicator that the ordered pair `p` of balls collides. -/
def coll (f : Fin k → Fin M) (p : Fin k × Fin k) : ℝ := if f p.1 = f p.2 then 1 else 0

def offDiag (k : ℕ) : Finset (Fin k × Fin k) := (univ : Finset (Fin k)).offDiag

theorem mem_offDiag' {p : Fin k × Fin k} : p ∈ offDiag k ↔ p.1 ≠ p.2 := by
  simp [offDiag, Finset.mem_offDiag]

/-- Number of colliding ordered pairs of distinct balls. -/
def orderedCollisions (f : Fin k → Fin M) : ℝ := ∑ p ∈ offDiag k, coll f p

/-- `L = ∑_j binom(N_j, 2)`, as a real number. -/
def collisions (f : Fin k → Fin M) : ℝ := ∑ j, (occ f j : ℝ) * ((occ f j : ℝ) - 1) / 2

theorem card_offDiag (k : ℕ) : ((offDiag k).card : ℝ) = k * ((k:ℝ) - 1) := by
  unfold offDiag
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.cast_sub (Nat.le_mul_self k)]
  push_cast; ring

theorem sum_coll_all (f : Fin k → Fin M) :
    ∑ p : Fin k × Fin k, coll f p = ∑ j, (occ f j : ℝ) ^ 2 := by
  have : ∀ p : Fin k × Fin k, coll f p = ∑ j, (if f p.1 = j then (1:ℝ) else 0) *
      (if f p.2 = j then 1 else 0) := by
    intro p
    unfold coll
    rw [Finset.sum_eq_single (f p.1)]
    · by_cases h : f p.1 = f p.2
      · simp [h]
      · simp [h, Ne.symm h]
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  simp_rw [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Fintype.sum_prod_type]
  dsimp only
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [occ, Finset.card_filter, sq, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem sum_occ (f : Fin k → Fin M) : ∑ j, (occ f j : ℝ) = k := by
  have : ∑ j, occ f j = k := by
    unfold occ
    rw [← Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (f a))]
    simp
  exact_mod_cast this

theorem collisions_eq (f : Fin k → Fin M) : collisions f = orderedCollisions f / 2 := by
  have hdiag : ∑ p : Fin k × Fin k, coll f p = orderedCollisions f + k := by
    rw [← Finset.univ_product_univ, ← Finset.diag_union_offDiag,
      Finset.sum_union (Finset.disjoint_diag_offDiag _), orderedCollisions, offDiag, add_comm]
    congr 1
    rw [Finset.sum_congr rfl (fun p hp => by
      rw [Finset.mem_diag] at hp
      simp [coll, hp.2] : ∀ p ∈ (univ : Finset (Fin k)).diag, coll f p = 1)]
    simp
  unfold collisions
  rw [← Finset.sum_div]
  have : ∑ j, (occ f j : ℝ) * ((occ f j : ℝ) - 1) = ∑ j, (occ f j : ℝ) ^ 2 - ∑ j, (occ f j : ℝ) := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [this, ← sum_coll_all, hdiag, sum_occ]
  ring

/-! ### Averaging over one coordinate -/

/-- Splitting off coordinate `d`. -/
def splitAt (d : Fin k) : (Fin k → Fin M) ≃ Fin M × ({j // j ≠ d} → Fin M) where
  toFun f := (f d, fun j => f j.1)
  invFun yr j := if h : j = d then yr.1 else yr.2 ⟨j, h⟩
  left_inv f := by
    funext j; by_cases h : j = d
    · subst h; simp
    · simp [h]
  right_inv yr := by
    obtain ⟨y, r⟩ := yr
    refine Prod.ext (by simp) (funext fun j => ?_)
    simp [j.2]

theorem update_eq_splitAt (d : Fin k) (f : Fin k → Fin M) (y : Fin M) :
    Function.update f d y = (splitAt d).symm (y, ((splitAt d) f).2) := by
  funext j
  by_cases h : j = d
  · subst h; simp [splitAt]
  · simp [splitAt, h, Function.update_of_ne h]

/-- `∑_f ∑_y g(f[d ↦ y]) = M ∑_f g(f)`. -/
theorem sum_update (d : Fin k) (g : (Fin k → Fin M) → ℝ) :
    ∑ f, ∑ y, g (Function.update f d y) = (M:ℝ) * ∑ f, g f := by
  simp_rw [update_eq_splitAt]
  rw [← (splitAt d).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← (splitAt d).symm.sum_comp (g := g), Fintype.sum_prod_type, Finset.sum_comm]

theorem expect_coll (hM : M ≠ 0) {p : Fin k × Fin k} (hp : p.1 ≠ p.2) :
    expect M k (fun f => coll f p) = 1 / M := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  have h := sum_update (M := M) p.2 (fun f : Fin k → Fin M => coll f p)
  have hin : ∀ f : Fin k → Fin M, ∑ y, coll (Function.update f p.2 y) p = 1 := by
    intro f
    simp only [coll, Function.update_self, Function.update_of_ne hp]
    rw [Finset.sum_ite_eq]; simp
  simp only [hin, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  unfold expect
  beta_reduce
  rw [show ∑ f : Fin k → Fin M, coll f p = (M:ℝ) ^ k / M by
    rw [eq_div_iff hm]; push_cast at h; linarith]
  field_simp <;> ring

theorem coll_mul_self (f : Fin k → Fin M) (p : Fin k × Fin k) : coll f p * coll f p = coll f p := by
  unfold coll; split_ifs <;> norm_num

theorem coll_swap (f : Fin k → Fin M) (p : Fin k × Fin k) : coll f p.swap = coll f p := by
  unfold coll; simp [eq_comm]

/-- Two different pairs (not equal up to order) collide jointly with probability `1/M²`. -/
theorem expect_coll_mul (hM : M ≠ 0) {p q : Fin k × Fin k} (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2)
    (hpq : q ≠ p) (hpq' : q ≠ p.swap) :
    expect M k (fun f => coll f p * coll f q) = 1 / (M:ℝ) ^ 2 := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  -- a ball `d` of `q` outside `p`, and the other ball `c` of `q`
  obtain ⟨d, c, hdc, hdp1, hdp2, hcoll⟩ : ∃ d c : Fin k, d ≠ c ∧ d ≠ p.1 ∧ d ≠ p.2 ∧
      ∀ f : Fin k → Fin M, coll f q = if f c = f d then 1 else 0 := by
    by_cases h2 : q.2 = p.1 ∨ q.2 = p.2
    · refine ⟨q.1, q.2, hq, ?_, ?_, fun f => by simp [coll, eq_comm]⟩
      · intro h1
        rcases h2 with h2 | h2
        · exact hq (h1.trans h2.symm)
        · exact hpq (Prod.ext h1 h2)
      · intro h1
        rcases h2 with h2 | h2
        · exact hpq' (Prod.ext h1 h2)
        · exact hq (h1.trans h2.symm)
    · push_neg at h2
      exact ⟨q.2, q.1, Ne.symm hq, h2.1, h2.2, fun f => rfl⟩
  have hin : ∀ f : Fin k → Fin M, ∑ y, coll (Function.update f d y) p *
      coll (Function.update f d y) q = coll f p := by
    intro f
    have h1 : ∀ y, coll (Function.update f d y) p = coll f p := by
      intro y
      simp [coll, Function.update_of_ne (Ne.symm hdp1), Function.update_of_ne (Ne.symm hdp2)]
    have h2 : ∀ y, coll (Function.update f d y) q = if f c = y then 1 else 0 := by
      intro y
      rw [hcoll]
      simp [Function.update_self, Function.update_of_ne (Ne.symm hdc)]
    simp_rw [h1, h2]
    rw [← Finset.mul_sum, Finset.sum_ite_eq]
    simp
  have h := sum_update (M := M) d (fun f : Fin k → Fin M => coll f p * coll f q)
  simp only [hin] at h
  have h0 := expect_coll (k := k) hM hp
  unfold expect at h0 ⊢
  beta_reduce at h0 ⊢
  have hpow : (M:ℝ) ^ k ≠ 0 := pow_ne_zero _ hm
  have hs : ∑ f : Fin k → Fin M, coll f p = (M:ℝ) ^ k / M := by
    rw [div_eq_div_iff hpow hm] at h0
    rw [eq_div_iff hm]; linarith
  have hs2 : ∑ f : Fin k → Fin M, coll f p * coll f q = (M:ℝ) ^ k / M / M := by
    rw [eq_div_iff hm, mul_comm, ← h, hs]
  rw [hs2]
  field_simp <;> ring

/-! ### Expectations of the collision count -/

theorem expect_add_mul (X Y : (Fin k → Fin M) → ℝ) (a b : ℝ) :
    expect M k (fun f => a * X f + b * Y f) = a * expect M k X + b * expect M k Y := by
  unfold expect
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem expect_sum {ι : Type*} (s : Finset ι) (X : ι → (Fin k → Fin M) → ℝ) :
    expect M k (fun f => ∑ i ∈ s, X i f) = ∑ i ∈ s, expect M k (X i) := by
  unfold expect
  rw [Finset.sum_comm, Finset.sum_div]

theorem expect_mono {X Y : (Fin k → Fin M) → ℝ} (h : ∀ f, X f ≤ Y f) :
    expect M k X ≤ expect M k Y := by
  unfold expect
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun f _ => h f)) (by positivity)

theorem expect_const (hM : M ≠ 0) (c : ℝ) : expect M k (fun _ => c) = c := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  unfold expect
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow]
  exact mul_div_cancel_left₀ c (pow_ne_zero k hm)

theorem expect_orderedCollisions (hM : M ≠ 0) :
    expect M k orderedCollisions = k * ((k:ℝ) - 1) / M := by
  unfold orderedCollisions
  rw [expect_sum]
  rw [Finset.sum_congr rfl (fun p hp => expect_coll hM (mem_offDiag'.mp hp)),
    Finset.sum_const, nsmul_eq_mul, card_offDiag]
  ring

theorem filter_pair (p : Fin k × Fin k) (hp : p.1 ≠ p.2) :
    (offDiag k).filter (fun q => q = p ∨ q = p.swap) = {p, p.swap} := by
  ext q
  simp only [Finset.mem_filter, mem_offDiag', Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro (rfl | rfl)
    · exact ⟨hp, Or.inl rfl⟩
    · exact ⟨Ne.symm hp, Or.inr rfl⟩

theorem expect_orderedCollisions_sq (hM : M ≠ 0) :
    expect M k (fun f => orderedCollisions f * orderedCollisions f) =
      k * ((k:ℝ) - 1) * (2 / M + (k * ((k:ℝ) - 1) - 2) / (M:ℝ) ^ 2) := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  unfold orderedCollisions
  simp_rw [Finset.sum_mul_sum]
  rw [expect_sum]
  have hinner : ∀ p ∈ offDiag k, expect M k (fun f => ∑ q ∈ offDiag k, coll f p * coll f q) =
      2 / M + (k * ((k:ℝ) - 1) - 2) / (M:ℝ) ^ 2 := by
    intro p hp
    have hp' := mem_offDiag'.mp hp
    rw [expect_sum]
    have hval : ∀ q ∈ offDiag k, expect M k (fun f => coll f p * coll f q) =
        1 / (M:ℝ) ^ 2 + (if q = p ∨ q = p.swap then 1 / M - 1 / (M:ℝ) ^ 2 else 0) := by
      intro q hq
      have hq' := mem_offDiag'.mp hq
      split_ifs with h
      · rcases h with rfl | rfl
        · simp_rw [coll_mul_self]; rw [expect_coll hM hp']; ring
        · simp_rw [coll_swap, coll_mul_self]; rw [expect_coll hM hp']; ring
      · push_neg at h
        rw [expect_coll_mul hM hp' hq' h.1 h.2]; ring
    rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      card_offDiag, ← Finset.sum_filter, filter_pair p hp', Finset.sum_const,
      Finset.card_pair (by intro h; exact hp' (congrArg Prod.fst h)), nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, card_offDiag]

/-- `E L = L_k/M` with `L_k = k(k-1)/2`. -/
theorem expect_collisions (hM : M ≠ 0) :
    expect M k collisions = (k * ((k:ℝ) - 1) / 2) / M := by
  have : collisions = fun f : Fin k → Fin M => (1/2) * orderedCollisions f + 0 * orderedCollisions f := by
    funext f; rw [collisions_eq]; ring
  rw [this, expect_add_mul, expect_orderedCollisions hM]
  ring

/-- `E L(L-1) = L_k(L_k-1)/M²`. -/
theorem expect_collisions_falling (hM : M ≠ 0) :
    expect M k (fun f => collisions f * (collisions f - 1)) =
      (k * ((k:ℝ) - 1) / 2) * (k * ((k:ℝ) - 1) / 2 - 1) / (M:ℝ) ^ 2 := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  have : (fun f : Fin k → Fin M => collisions f * (collisions f - 1)) =
      fun f => (1/4) * (orderedCollisions f * orderedCollisions f) + (-1/2) * orderedCollisions f := by
    funext f; rw [collisions_eq]; ring
  rw [this, expect_add_mul, expect_orderedCollisions_sq hM, expect_orderedCollisions hM]
  ring

/-! ### The pointwise inequality -/

theorem momentFactor_le_three_fifths (n : ℕ) (hn : 2 ≤ n) : momentFactor n ≤ 3/5 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · omega
      · rw [show (1:ℕ) + 1 = 2 from rfl, momentFactor_two]
    · rw [momentFactor]
      have h1 := ih h
      have h0 := momentFactor_nonneg n
      have : (3 / (2 * (n:ℝ) + 3)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith

theorem one_sub_momentFactor_le (n : ℕ) :
    1 - momentFactor n ≤ (2/5) * ((n:ℝ) * ((n:ℝ) - 1) / 2) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n
    · norm_num [momentFactor]
    · norm_num [momentFactor]
    · rw [momentFactor_two]; norm_num
  · have h0 := momentFactor_nonneg n
    have hn : (3:ℝ) ≤ n := by exact_mod_cast h
    nlinarith

theorem one_sub_prod_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    have hP0 : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have hP1 : ∏ i ∈ s, a i ≤ 1 := Finset.prod_le_one (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hih := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hb0 := h0 b (Finset.mem_insert_self b s)
    have hb1 := h1 b (Finset.mem_insert_self b s)
    nlinarith

theorem occupancy_pointwise (f : Fin k → Fin M) :
    0 ≤ (∏ j, momentFactor (occ f j)) - 1 + (2/5) * collisions f ∧
    (∏ j, momentFactor (occ f j)) - 1 + (2/5) * collisions f ≤ collisions f * (collisions f - 1) := by
  have hρ0 : ∀ j, 0 ≤ momentFactor (occ f j) := fun j => momentFactor_nonneg _
  have hρ1 : ∀ j, momentFactor (occ f j) ≤ 1 := fun j => momentFactor_le_one _
  have hlow := one_sub_prod_le univ (fun j => momentFactor (occ f j)) (fun j _ => hρ0 j)
    (fun j _ => hρ1 j)
  have hsum : ∑ j, (1 - momentFactor (occ f j)) ≤ (2/5) * collisions f := by
    unfold collisions
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => one_sub_momentFactor_le _)
  refine ⟨by linarith, ?_⟩
  have hq : ∀ n : ℕ, (n:ℝ) * ((n:ℝ) - 1) / 2 = 0 ∨ 1 ≤ (n:ℝ) * ((n:ℝ) - 1) / 2 := by
    intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · left; interval_cases n <;> norm_num
    · right; have : (2:ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  by_cases hall : ∀ j, occ f j ≤ 1
  · have hL : collisions f = 0 := by
      unfold collisions
      apply Finset.sum_eq_zero; intro j _
      have := hall j
      interval_cases (occ f j) <;> norm_num
    have hP : ∏ j, momentFactor (occ f j) = 1 := by
      apply Finset.prod_eq_one; intro j _
      have := hall j
      interval_cases (occ f j) <;> norm_num [momentFactor]
    rw [hL, hP]; norm_num
  · push_neg at hall
    obtain ⟨j0, hj0⟩ := hall
    have hP : ∏ j, momentFactor (occ f j) ≤ 3/5 := by
      rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ j0)]
      have h1 := momentFactor_le_three_fifths (occ f j0) hj0
      have h2 : ∏ j ∈ univ.erase j0, momentFactor (occ f j) ≤ 1 :=
        Finset.prod_le_one (fun j _ => hρ0 j) (fun j _ => hρ1 j)
      have h3 : 0 ≤ ∏ j ∈ univ.erase j0, momentFactor (occ f j) :=
        Finset.prod_nonneg (fun j _ => hρ0 j)
      nlinarith [hρ0 j0]
    have hL1 : 1 ≤ collisions f := by
      unfold collisions
      have hterm : 1 ≤ (occ f j0 : ℝ) * ((occ f j0 : ℝ) - 1) / 2 := by
        have : (2:ℝ) ≤ occ f j0 := by exact_mod_cast hj0
        nlinarith
      calc 1 ≤ (occ f j0 : ℝ) * ((occ f j0 : ℝ) - 1) / 2 := hterm
        _ ≤ _ := Finset.single_le_sum (f := fun j => (occ f j : ℝ) * ((occ f j : ℝ) - 1) / 2)
              (fun j _ => by rcases hq (occ f j) with h | h <;> linarith) (Finset.mem_univ j0)
    nlinarith

/-! ### Lemmas 9.3 and 9.4 with the printed constants -/

/-- **Lemma 9.3**: `0 ≤ R_{M,k} - (1 - d_k/M) ≤ L_k(L_k-1)/M²`, `d_k = k(k-1)/5`,
`L_k = k(k-1)/2`, for every `M ≥ 1` and `k ≥ 0`. -/
theorem occupancy_moment_bound (M k : ℕ) (hM : M ≠ 0) :
    0 ≤ uniformMomentRatio M k - (1 - (k * ((k:ℝ) - 1) / 5) / M) ∧
    uniformMomentRatio M k - (1 - (k * ((k:ℝ) - 1) / 5) / M) ≤
      (k * ((k:ℝ) - 1) / 2) * (k * ((k:ℝ) - 1) / 2 - 1) / (M:ℝ) ^ 2 := by
  rw [uniformMomentRatio_occupancy M k hM]
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  have hEL := expect_collisions (k := k) hM
  have hELL := expect_collisions_falling (k := k) hM
  have hrep : expect M k (fun f => ∏ j, momentFactor (occ f j)) - (1 - (k * ((k:ℝ) - 1) / 5) / M) =
      expect M k (fun f => (∏ j, momentFactor (occ f j)) - 1 + (2/5) * collisions f) := by
    have : (fun f : Fin k → Fin M => (∏ j, momentFactor (occ f j)) - 1 + (2/5) * collisions f) =
        fun f => 1 * ((∏ j, momentFactor (occ f j)) + (2/5) * collisions f) + (-1) * 1 := by
      funext f; ring
    rw [this, expect_add_mul, expect_const hM]
    have : (fun f : Fin k → Fin M => (∏ j, momentFactor (occ f j)) + (2/5) * collisions f) =
        fun f => 1 * (∏ j, momentFactor (occ f j)) + (2/5) * collisions f := by funext f; ring
    rw [this, expect_add_mul (Y := collisions), hEL]
    ring
  rw [hrep]
  constructor
  · have := expect_mono (M := M) (k := k) (X := fun _ => (0:ℝ))
      (fun f => (occupancy_pointwise f).1)
    rwa [expect_const hM] at this
  · rw [← hELL]
    exact expect_mono (fun f => (occupancy_pointwise f).2)

/-- **Lemma 9.4**: `0 ≤ R_{M,k}² - (1 - 2d_k/M) ≤ 27 k²(k-1)²/(50 M²)`. -/
theorem occupancy_square_bound (M k : ℕ) (hM : M ≠ 0) :
    0 ≤ uniformMomentRatio M k ^ 2 - (1 - 2 * (k * ((k:ℝ) - 1) / 5) / M) ∧
    uniformMomentRatio M k ^ 2 - (1 - 2 * (k * ((k:ℝ) - 1) / 5) / M) ≤
      27 / (50 * (M:ℝ) ^ 2) * ((k:ℝ) ^ 2 * ((k:ℝ) - 1) ^ 2) := by
  obtain ⟨h0, h1⟩ := occupancy_moment_bound M k hM
  have hR1 := uniformMomentRatio_le_one M k hM
  have hm : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hX : 0 ≤ (k:ℝ) * ((k:ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have : (1:ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = uniformMomentRatio M k := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = k * ((k:ℝ) - 1) / 5 := ⟨_, rfl⟩
  rw [← hR] at h0 h1 hR1 ⊢
  rw [← hd] at h0 h1 ⊢
  have hd0 : 0 ≤ d := by rw [hd]; exact div_nonneg hX (by norm_num)
  have hdM : 0 ≤ d / M := div_nonneg hd0 hm.le
  have hid : R ^ 2 - (1 - 2 * d / M) = (1 - R) ^ 2 + 2 * (R - (1 - d / M)) := by ring
  rw [hid]
  constructor
  · nlinarith [sq_nonneg (1 - R)]
  · have hsq : (1 - R) ^ 2 ≤ (d / M) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hkey : d ^ 2 + 2 * ((k * ((k:ℝ) - 1) / 2) * (k * ((k:ℝ) - 1) / 2 - 1)) ≤
        27 / 50 * ((k:ℝ) ^ 2 * ((k:ℝ) - 1) ^ 2) := by
      rw [hd]; nlinarith [hX]
    calc (1 - R) ^ 2 + 2 * (R - (1 - d / M)) ≤ (d / M) ^ 2 +
          2 * ((k * ((k:ℝ) - 1) / 2) * (k * ((k:ℝ) - 1) / 2 - 1) / (M:ℝ) ^ 2) := by linarith
      _ = (d ^ 2 + 2 * ((k * ((k:ℝ) - 1) / 2) * (k * ((k:ℝ) - 1) / 2 - 1))) / (M:ℝ) ^ 2 := by
          rw [div_pow, ← mul_div_assoc, ← add_div]
      _ ≤ (27 / 50 * ((k:ℝ) ^ 2 * ((k:ℝ) - 1) ^ 2)) / (M:ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hkey (by positivity)
      _ = 27 / (50 * (M:ℝ) ^ 2) * ((k:ℝ) ^ 2 * ((k:ℝ) - 1) ^ 2) := by ring

end EulerianGrothendieck.Occupancy
