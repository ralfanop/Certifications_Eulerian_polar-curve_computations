import EulerianGrothendieck.UniformRatioBounds
import EulerianGrothendieck.BernoulliCumulantIdentification
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! # Lemma 9.8 (exact polynomial coefficients) at every order `r`

Manuscript 12, Lemma 9.8.  With `a_j = 3^j 2^{2j-1} B_{2j}/(j (2j)!)`, the polynomials `P_r(y)`
are defined by `P_0 = 1` and the coefficient recurrence (eg:eq:Pformal-recurrence)
`r P_r = ∑_{j=1}^r j a_{j+1} y^{j+1} P_{r-j}`;
`g_r(k) = ∑_q 2^q (k)_q [y^q] P_r(y)` and `q_r(k) = ∑_{j=0}^r g_j(k) g_{r-j}(k)`.
Proved here, for every `r` and every `k`:
* the degrees occurring in `P_r` lie between `r+1` and `2r` for `r ≥ 1` (`pc_support`);
* `g_0 = 1`, `g_r(0) = 0` for `r > 0`;
* `R_{M,k} = ∑_{r=0}^{k-1} g_r(k) M^{-r}` for all `M ≥ 1`, `k ≥ 1` (`uniformMomentRatio_eq_g_sum`),
  where `R_{M,k}` is the actual normalised uniform moment ratio of the certified library;
* `g_r` and `q_r` are polynomials in `k` with rational coefficients of degree at most `2r`.
The key step is the Euler identity `y P_r' = r P_r + ∑_{j=1}^r a_{j+1} y^{j+1} P_{r-j}` (`euler`),
proved from the recurrence alone by induction on `r`. -/

noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace EulerianGrothendieck.AllOrders

/-- `a_j` with rational values. -/
def aQ (j : ℕ) : ℚ :=
  (3:ℚ) ^ j * 2 ^ (2*j-1) * (bernoulli (2*j)) / (j * ((2*j).factorial : ℚ))

theorem aQ_cast (j : ℕ) : ((aQ j : ℚ) : ℝ) = uniformLogCoefficient j := by
  unfold aQ uniformLogCoefficient
  push_cast
  ring

/-- `[y^q] P_r(y)`, defined by `P_0 = 1` and the recurrence (eg:eq:Pformal-recurrence). -/
def pc : ℕ → ℕ → ℚ
  | 0, q => if q = 0 then 1 else 0
  | r+1, q => ((r:ℚ)+1)⁻¹ * ∑ j ∈ range (r+1),
      ((j:ℚ)+1) * aQ (j+2) * (if j+2 ≤ q then pc (r-j) (q-(j+2)) else 0)
termination_by r _ => r
decreasing_by omega

def T (r q : ℕ) : ℚ :=
  ∑ j ∈ range r, ((j:ℚ)+1) * aQ (j+2) * (if j+2 ≤ q then pc (r-1-j) (q-(j+2)) else 0)

def S (r q : ℕ) : ℚ :=
  ∑ j ∈ range r, aQ (j+2) * (if j+2 ≤ q then pc (r-1-j) (q-(j+2)) else 0)

theorem pc_zero (q : ℕ) : pc 0 q = if q = 0 then 1 else 0 := by
  rw [pc]

theorem pc_succ (r q : ℕ) : pc (r+1) q = ((r:ℚ)+1)⁻¹ * ∑ j ∈ range (r+1),
      ((j:ℚ)+1) * aQ (j+2) * (if j+2 ≤ q then pc (r-j) (q-(j+2)) else 0) := by
  rw [pc]

/-- The recurrence `r P_r = ∑_{j=1}^r j a_{j+1} y^{j+1} P_{r-j}`, coefficientwise. -/
theorem pc_rec (r q : ℕ) : (r:ℚ) * pc r q = T r q := by
  cases r with
  | zero => simp [T]
  | succ r =>
    rw [pc_succ, T]
    have h : ((r:ℚ)+1) ≠ 0 := by positivity
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- Support: the degrees occurring in `P_r` lie between `r+1` and `2r` for `r ≥ 1`. -/
theorem pc_support (r q : ℕ) (h : pc r q ≠ 0) :
    (r = 0 ∧ q = 0) ∨ (r+1 ≤ q ∧ q ≤ 2*r) := by
  induction r using Nat.strong_induction_on generalizing q with
  | h r ih =>
    cases r with
    | zero =>
      left; refine ⟨rfl, ?_⟩
      by_contra hq
      exact h (by simp [pc_zero, hq])
    | succ r =>
      right
      rw [pc_succ] at h
      have hs := right_ne_zero_of_mul h
      obtain ⟨j, hj, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      have hjr : j < r+1 := Finset.mem_range.mp hj
      by_cases hq : j+2 ≤ q
      · rw [if_pos hq] at hjne
        have hp := right_ne_zero_of_mul hjne
        rcases ih (r-j) (by omega) (q-(j+2)) hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · rw [if_neg hq, mul_zero] at hjne
        exact absurd rfl hjne

theorem pc_eq_zero_of_gt (r q : ℕ) (h : 2*r < q) : pc r q = 0 := by
  by_contra hne
  rcases pc_support r q hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem pc_eq_zero_of_le (r q : ℕ) (hr : 0 < r) (h : q ≤ r) : pc r q = 0 := by
  by_contra hne
  rcases pc_support r q hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Extending a range sum by zeros. -/
theorem sum_range_extend (f : ℕ → ℚ) (m n : ℕ) (hmn : m ≤ n) :
    ∑ l ∈ range m, f l = ∑ l ∈ range n, (if l < m then f l else 0) := by
  rw [← Finset.sum_subset (Finset.range_mono hmn)]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [if_pos (Finset.mem_range.mp hl)]
  · intro l _ hl
    rw [if_neg (by simpa using hl)]

/-- The symmetric kernel of the double sums. -/
def F (r q j l : ℕ) : ℚ :=
  if j + l + 2 ≤ r ∧ j + l + 4 ≤ q then
    aQ (j+2) * aQ (l+2) * pc (r-2-j-l) (q-4-j-l) else 0

theorem F_symm (r q j l : ℕ) : F r q j l = F r q l j := by
  unfold F
  have h1 : (j + l + 2 ≤ r ∧ j + l + 4 ≤ q) ↔ (l + j + 2 ≤ r ∧ l + j + 4 ≤ q) := by omega
  by_cases h : j + l + 2 ≤ r ∧ j + l + 4 ≤ q
  · rw [if_pos h, if_pos (h1.mp h), show r-2-l-j = r-2-j-l by omega,
      show q-4-l-j = q-4-j-l by omega]
    ring
  · rw [if_neg h, if_neg (fun h' => h (h1.mpr h'))]

theorem inner_S (r q j : ℕ) (hj : j < r) (c : ℚ) :
    c * aQ (j+2) * (if j+2 ≤ q then S (r-1-j) (q-(j+2)) else 0) =
      ∑ l ∈ range r, c * F r q j l := by
  unfold S
  rw [sum_range_extend _ (r-1-j) r (by omega)]
  by_cases hq : j+2 ≤ q
  · rw [if_pos hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    unfold F
    by_cases hl : l < r-1-j
    · rw [if_pos hl]
      by_cases hl2 : l+2 ≤ q-(j+2)
      · rw [if_pos hl2, if_pos ⟨by omega, by omega⟩,
          show r-1-j-1-l = r-2-j-l by omega, show q-(j+2)-(l+2) = q-4-j-l by omega]
        ring
      · rw [if_neg hl2, if_neg (by omega)]
        ring
    · rw [if_neg hl, if_neg (by omega)]
      ring
  · rw [if_neg hq, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro l _
    unfold F
    rw [if_neg (by omega), mul_zero]

theorem inner_T (r q j : ℕ) (hj : j < r) :
    aQ (j+2) * (if j+2 ≤ q then T (r-1-j) (q-(j+2)) else 0) =
      ∑ l ∈ range r, ((l:ℚ)+1) * F r q j l := by
  unfold T
  rw [sum_range_extend _ (r-1-j) r (by omega)]
  by_cases hq : j+2 ≤ q
  · rw [if_pos hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    unfold F
    by_cases hl : l < r-1-j
    · rw [if_pos hl]
      by_cases hl2 : l+2 ≤ q-(j+2)
      · rw [if_pos hl2, if_pos ⟨by omega, by omega⟩,
          show r-1-j-1-l = r-2-j-l by omega, show q-(j+2)-(l+2) = q-4-j-l by omega]
        ring
      · rw [if_neg hl2, if_neg (by omega)]
        ring
    · rw [if_neg hl, if_neg (by omega)]
      ring
  · rw [if_neg hq, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro l _
    unfold F
    rw [if_neg (by omega), mul_zero]

/-- The two double sums agree, by the symmetry of `F`. -/
theorem D_eq_E (r q : ℕ) :
    ∑ j ∈ range r, ((j:ℚ)+1) * aQ (j+2) * (if j+2 ≤ q then S (r-1-j) (q-(j+2)) else 0) =
      ∑ j ∈ range r, aQ (j+2) * (if j+2 ≤ q then T (r-1-j) (q-(j+2)) else 0) := by
  rw [Finset.sum_congr rfl (fun j hj => inner_S r q j (Finset.mem_range.mp hj) ((j:ℚ)+1)),
    Finset.sum_congr rfl (fun j hj => inner_T r q j (Finset.mem_range.mp hj)),
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [F_symm]

/-- **Euler identity** `y P_r' = r P_r + ∑_{j=1}^r a_{j+1} y^{j+1} P_{r-j}`, coefficientwise. -/
theorem euler (r q : ℕ) : (q:ℚ) * pc r q = r * pc r q + S r q := by
  induction r using Nat.strong_induction_on generalizing q with
  | h r ih =>
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      by_cases hq : q = 0 <;> simp [pc_zero, hq, S]
    · have hR : (r:ℚ) ≠ 0 := by exact_mod_cast hr.ne'
      apply mul_left_cancel₀ hR
      -- left side
      have hL : (r:ℚ) * ((q:ℚ) * pc r q) =
          (r+1) * T r q +
            ∑ j ∈ range r, ((j:ℚ)+1) * aQ (j+2) *
              (if j+2 ≤ q then S (r-1-j) (q-(j+2)) else 0) := by
        rw [show (r:ℚ) * ((q:ℚ) * pc r q) = (q:ℚ) * ((r:ℚ) * pc r q) by ring, pc_rec, T,
          Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjr := Finset.mem_range.mp hj
        by_cases hq : j+2 ≤ q
        · rw [if_pos hq, if_pos hq]
          have hqc : (q:ℚ) = (j:ℚ) + 2 + ((q-(j+2) : ℕ) : ℚ) := by
            rw [Nat.cast_sub hq]; push_cast; ring
          have hrc : ((r-1-j : ℕ) : ℚ) = (r:ℚ) - 1 - j := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
          have e := ih (r-1-j) (by omega) (q-(j+2))
          rw [hrc] at e
          calc (q:ℚ) * (((j:ℚ)+1) * aQ (j+2) * pc (r-1-j) (q-(j+2)))
              = ((j:ℚ)+1) * aQ (j+2) * (((j:ℚ)+2) * pc (r-1-j) (q-(j+2)) +
                  ((q-(j+2) : ℕ) : ℚ) * pc (r-1-j) (q-(j+2))) := by rw [hqc]; ring
            _ = ((j:ℚ)+1) * aQ (j+2) * (((j:ℚ)+2) * pc (r-1-j) (q-(j+2)) +
                  (((r:ℚ) - 1 - j) * pc (r-1-j) (q-(j+2)) + S (r-1-j) (q-(j+2)))) := by rw [e]
            _ = _ := by ring
        · rw [if_neg hq, if_neg hq]; ring
      -- right side
      have hS : (r:ℚ) * S r q = T r q +
          ∑ j ∈ range r, aQ (j+2) * (if j+2 ≤ q then T (r-1-j) (q-(j+2)) else 0) := by
        rw [S, T, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjr := Finset.mem_range.mp hj
        by_cases hq : j+2 ≤ q
        · simp only [if_pos hq]
          rw [← pc_rec]
          have hrc : ((r-1-j : ℕ) : ℚ) = (r:ℚ) - 1 - j := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
          rw [hrc]; ring
        · simp only [if_neg hq]; ring
      rw [hL, mul_add, hS, ← pc_rec, D_eq_E]
      ring

/-- The form used below: `q [y^q]P_r = ∑_{j=1}^r (j+1) a_{j+1} [y^{q-j-1}] P_{r-j}`. -/
theorem euler' (r q : ℕ) : (q:ℚ) * pc r q =
    ∑ j ∈ range r, ((j:ℚ)+2) * aQ (j+2) * (if j+2 ≤ q then pc (r-1-j) (q-(j+2)) else 0) := by
  rw [euler, pc_rec, T, S, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ## The polynomials `P_r` -/

def Ppoly (r : ℕ) : ℚ[X] := ∑ q ∈ range (2*r+1), C (pc r q) * X^q

theorem Ppoly_coeff (r q : ℕ) : (Ppoly r).coeff q = pc r q := by
  rw [Ppoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [pc_eq_zero_of_gt r q (by rw [Finset.mem_range] at h; omega)]

theorem Ppoly_zero : Ppoly 0 = 1 := by
  ext q
  rw [Ppoly_coeff, pc_zero, Polynomial.coeff_one]

/-- (eg:eq:Pformal-recurrence): `r P_r = ∑_{j=1}^r j a_{j+1} y^{j+1} P_{r-j}`. -/
theorem Ppoly_rec (r : ℕ) :
    C (r:ℚ) * Ppoly r = ∑ j ∈ range r, C (((j:ℚ)+1) * aQ (j+2)) * X^(j+2) * Ppoly (r-1-j) := by
  ext q
  rw [Polynomial.coeff_C_mul, Ppoly_coeff, pc_rec, T, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [show C (((j:ℚ)+1) * aQ (j+2)) * X^(j+2) * Ppoly (r-1-j) =
      C (((j:ℚ)+1) * aQ (j+2)) * (Ppoly (r-1-j) * X^(j+2)) by ring,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow', Ppoly_coeff]

/-! ## Real side: `g_r(x) = ∑_q 2^q (x)_q [y^q] P_r` and the recurrence in `k` -/

def pr (r q : ℕ) : ℝ := ((pc r q : ℚ) : ℝ)

def fall (q : ℕ) (x : ℝ) : ℝ := (descPochhammer ℝ q).eval x

theorem fall_zero (x : ℝ) : fall 0 x = 1 := by simp [fall]

theorem fall_succ (q : ℕ) (x : ℝ) : fall (q+1) x = fall q x * (x - q) := by
  simp [fall, descPochhammer_succ_eval]

theorem fall_nat (q n : ℕ) : fall q (n:ℝ) = (n.descFactorial q : ℝ) := by
  simp [fall, descPochhammer_eval_eq_descFactorial]

theorem fall_succ_at_zero (p : ℕ) : fall (p+1) 0 = 0 := by
  induction p with
  | zero => simp [fall_succ, fall_zero]
  | succ p ih => rw [fall_succ, ih, zero_mul]

theorem fall_shift (q : ℕ) (x : ℝ) :
    fall (q+1) (x+1) = fall (q+1) x + ((q:ℝ)+1) * fall q x := by
  induction q with
  | zero => simp [fall_succ, fall_zero]
  | succ q ih =>
    rw [fall_succ (q+1) (x+1), ih, fall_succ (q+1) x, fall_succ q x]
    push_cast
    ring

theorem fall_mul (j q : ℕ) (x : ℝ) : fall j x * fall q (x - j) = fall (j+q) x := by
  induction q with
  | zero => simp [fall_zero]
  | succ q ih =>
    rw [fall_succ, ← mul_assoc, ih, show j + (q+1) = (j+q)+1 by omega, fall_succ]
    push_cast
    ring

def G (r : ℕ) (x : ℝ) : ℝ := ∑ q ∈ range (2*r+1), 2^q * fall q x * pr r q

theorem pr_eq_zero_of_gt (r q : ℕ) (h : 2*r < q) : pr r q = 0 := by
  simp [pr, pc_eq_zero_of_gt r q h]

theorem G_range (r : ℕ) (x : ℝ) (N : ℕ) (hN : 2*r+1 ≤ N) :
    G r x = ∑ q ∈ range N, 2^q * fall q x * pr r q := by
  apply Finset.sum_subset (Finset.range_mono hN)
  intro q _ hq
  rw [pr_eq_zero_of_gt r q (by simp at hq; omega), mul_zero]

theorem sum_shift (f : ℕ → ℝ) (s M : ℕ) (h : s ≤ M) :
    ∑ m ∈ range M, (if s ≤ m then f m else 0) = ∑ q ∈ range (M-s), f (s+q) := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le s) h]
  rw [Finset.sum_eq_zero (fun m hm => by
    rw [if_neg (by simp at hm; omega)]), zero_add]
  rw [Finset.sum_congr rfl (fun m hm => by
    rw [if_pos (by simp at hm; omega)]), Finset.sum_Ico_eq_sum_range,
    Finset.range_eq_Ico]

theorem kappa_eq (j : ℕ) :
    standardUniformCumulant j = ((j:ℝ)+1) * ((aQ (j+1) : ℚ) : ℝ) := by
  have h := standardUniformCumulant_eq_mul_logCoefficient (j+1) (by omega)
  rw [show j + 1 - 1 = j by omega] at h
  rw [h, aQ_cast]
  push_cast
  ring

theorem euler_real (r m : ℕ) : ((m:ℝ)+1) * pr r (m+1) =
    ∑ j ∈ range r, standardUniformCumulant (j+1) *
      (if j+1 ≤ m then pr (r-1-j) (m-(j+1)) else 0) := by
  have h := congrArg (fun t : ℚ => (t:ℝ)) (euler' r (m+1))
  simp only at h
  push_cast at h
  rw [show ((m:ℝ)+1) * pr r (m+1) = ((m:ℝ)+1) * ((pc r (m+1) : ℚ) : ℝ) from rfl, h]
  apply Finset.sum_congr rfl
  intro j _
  rw [kappa_eq]
  simp only [show j + 1 + 1 = j + 2 from rfl]
  by_cases hj : j+1 ≤ m
  · rw [if_pos hj, if_pos hj]
    simp only [pr]; push_cast; ring
  · rw [if_neg hj, if_neg hj]
    simp

/-- The recurrence in `k` satisfied by `g_r(k)`, for every real argument. -/
theorem G_shift (r : ℕ) (x : ℝ) :
    G r (x+1) = ∑ j ∈ range (r+1),
      2^(j+1) * fall j x * standardUniformCumulant j * G (r-j) (x-j) := by
  rw [G_range r (x+1) (2*r+1+1) (by omega), Finset.sum_range_succ']
  have h1 : ∀ m ∈ range (2*r+1),
      2^(m+1) * fall (m+1) (x+1) * pr r (m+1) =
        2^(m+1) * fall (m+1) x * pr r (m+1) +
          2^(m+1) * fall m x * (((m:ℝ)+1) * pr r (m+1)) := by
    intro m _
    rw [fall_shift]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have hG : G r x = ∑ m ∈ range (2*r+1), 2^(m+1) * fall (m+1) x * pr r (m+1) +
      2^0 * fall 0 x * pr r 0 := by
    rw [G_range r x (2*r+1+1) (by omega), Finset.sum_range_succ']
  rw [Finset.sum_range_succ' _ r, fall_zero, fall_zero, standardUniformCumulant_zero]
  simp only [Nat.cast_zero, sub_zero, Nat.sub_zero]
  have hcore : ∑ m ∈ range (2*r+1), 2^(m+1) * fall m x * (((m:ℝ)+1) * pr r (m+1)) =
      ∑ j ∈ range r, 2^(j+1+1) * fall (j+1) x * standardUniformCumulant (j+1) *
        G (r-(j+1)) (x - ((j+1 : ℕ) : ℝ)) := by
    simp_rw [euler_real, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hjr := Finset.mem_range.mp hj
    have hs := sum_shift (fun m => 2^(m+1) * fall m x *
        (standardUniformCumulant (j+1) * pr (r-1-j) (m-(j+1)))) (j+1) (2*r+1) (by omega)
    have hlhs : ∑ m ∈ range (2*r+1), 2^(m+1) * fall m x *
        (standardUniformCumulant (j+1) * (if j+1 ≤ m then pr (r-1-j) (m-(j+1)) else 0)) =
        ∑ m ∈ range (2*r+1), (if j+1 ≤ m then 2^(m+1) * fall m x *
          (standardUniformCumulant (j+1) * pr (r-1-j) (m-(j+1))) else 0) := by
      apply Finset.sum_congr rfl
      intro m _
      split_ifs <;> ring
    rw [hlhs, hs, G_range (r-(j+1)) _ (2*r+1-(j+1)) (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    beta_reduce
    rw [show j+1+q-(j+1) = q by omega, show r-1-j = r-(j+1) by omega]
    rw [show (2:ℝ)^(j+1+q+1) * fall (j+1+q) x = 2^(j+1+1) * 2^q *
        (fall (j+1) x * fall q (x - ((j+1 : ℕ) : ℝ))) by
      rw [fall_mul, ← pow_add]; ring_nf]
    ring
  rw [hcore, hG]
  simp only [fall_zero]
  ring

/-- Recurrence for the certified coefficients (copied from `CoefficientIdentification`
under a new name, so that this module does not need the order-13 tables). -/
theorem coeff_rec (n r : ℕ) :
    (uniformRatioPolynomial (n+1)).coeff r =
      ∑ j ∈ range (r+1), ratioRecurrenceCoefficient n j *
        (uniformRatioPolynomial (n-j)).coeff (r-j) := by
  rw [uniformRatioPolynomial_recurrence, Polynomial.finset_sum_coeff]
  simp only [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  have hz : ∀ j, n < j → ratioRecurrenceCoefficient n j = 0 := by
    intro j h; simp [ratioRecurrenceCoefficient, Nat.descFactorial_of_lt h]
  let f := fun j => ratioRecurrenceCoefficient n j *
    (if j ≤ r then (uniformRatioPolynomial (n-j)).coeff (r-j) else 0)
  have he : (∑ j ∈ range (n+1), f j) = ∑ j ∈ range (r+1), f j := by
    by_cases h : n ≤ r
    · apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hnot
      have hjn : n < j := by simp only [Finset.mem_range] at hnot; omega
      simp [f, hz j hjn]
    · symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hnot
      have hjr : ¬j ≤ r := by simp only [Finset.mem_range] at hnot; omega
      simp [f, hjr]
  change (∑ j ∈ range (n+1), f j) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  simp [f, show j ≤ r by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj]

theorem G_at_zero (r : ℕ) : G r 0 = if r = 0 then 1 else 0 := by
  rw [G, Finset.sum_eq_single 0]
  · simp only [pow_zero, fall_zero, one_mul, pr]
    by_cases h : r = 0
    · subst h; simp [pc_zero]
    · rw [if_neg h, pc_eq_zero_of_le r 0 (by omega) (by omega)]; simp
  · intro q _ hq
    obtain ⟨p, rfl⟩ : ∃ p, q = p+1 := ⟨q-1, by omega⟩
    rw [fall_succ_at_zero]; ring
  · intro h; simp at h

/-- **Lemma 9.8, identification at every order**: the coefficient of `M^{-r}` in the
certified exact polynomial `R_{M,k}` is the printed `g_r(k)`. -/
theorem coeff_eq_G (k r : ℕ) : (uniformRatioPolynomial k).coeff r = G r k := by
  induction k using Nat.strong_induction_on generalizing r with
  | h k ih =>
    cases k with
    | zero =>
      rw [uniformRatioPolynomial_zero, Polynomial.coeff_one, Nat.cast_zero, G_at_zero]
    | succ n =>
      rw [coeff_rec, show ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 by push_cast; ring, G_shift]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hjn : j ≤ n
      · rw [ih (n-j) (by omega), ratioRecurrenceCoefficient, fall_nat, Nat.cast_sub hjn]
      · rw [ratioRecurrenceCoefficient, fall_nat, Nat.descFactorial_of_lt (by omega)]
        simp

theorem G_zero (x : ℝ) : G 0 x = 1 := by
  simp [G, fall_zero, pr, pc_zero]

theorem G_at_zero_pos (r : ℕ) (hr : 0 < r) : G r 0 = 0 := by
  rw [G_at_zero, if_neg (by omega)]

theorem G_vanish (r k : ℕ) (hrk : k ≤ r) (hr : 0 < r) : G r k = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  by_cases h : pc r q = 0
  · simp [pr, h]
  · rcases pc_support r q h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · rw [fall_nat, Nat.descFactorial_of_lt (by omega)]; simp

/-- **Lemma 9.8, (eg:eq:exactpoly)**: `R_{M,k} = ∑_{r=0}^{k-1} g_r(k) M^{-r}` for every
`M ≥ 1` and `k ≥ 1`. -/
theorem uniformMomentRatio_eq_g_sum (M k : ℕ) (hM : M ≠ 0) (hk : 1 ≤ k) :
    uniformMomentRatio M k = ∑ r ∈ range k, G r k * (1/(M:ℝ))^r := by
  rw [uniformMomentRatio_exact_polynomial M k hM]
  have hdeg : (uniformRatioPolynomial k).natDegree < k := by
    have : (uniformRatioPolynomial k).natDegree ≤ k-1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_eq_G]
      exact G_vanish N k (by omega) (by omega)
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg]
  apply Finset.sum_congr rfl
  intro r _
  rw [coeff_eq_G]

/-! ## `g_r` and `q_r` are rational polynomials of degree at most `2r` -/

def gPoly (r : ℕ) : ℚ[X] := ∑ q ∈ range (2*r+1), C (2^q * pc r q) * descPochhammer ℚ q

theorem gPoly_natDegree (r : ℕ) : (gPoly r).natDegree ≤ 2*r := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q hq
  have hq' : q ≤ 2*r := by simp at hq; omega
  calc (C (2^q * pc r q) * descPochhammer ℚ q).natDegree
      ≤ (descPochhammer ℚ q).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ = q := descPochhammer_natDegree ℚ q
    _ ≤ 2*r := hq'

theorem gPoly_eval (r : ℕ) (x : ℝ) : ((gPoly r).map (algebraMap ℚ ℝ)).eval x = G r x := by
  rw [gPoly, Polynomial.map_sum, Polynomial.eval_finset_sum, G]
  apply Finset.sum_congr rfl
  intro q _
  rw [Polynomial.map_mul, Polynomial.map_C, descPochhammer_map, Polynomial.eval_mul,
    Polynomial.eval_C, fall, pr]
  simp only [map_mul, map_pow, eq_ratCast]
  push_cast
  ring

def qPoly (r : ℕ) : ℚ[X] := ∑ j ∈ range (r+1), gPoly j * gPoly (r-j)

theorem qPoly_natDegree (r : ℕ) : (qPoly r).natDegree ≤ 2*r := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hj' : j ≤ r := by simp at hj; omega
  calc (gPoly j * gPoly (r-j)).natDegree
      ≤ (gPoly j).natDegree + (gPoly (r-j)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 2*j + 2*(r-j) := add_le_add (gPoly_natDegree j) (gPoly_natDegree (r-j))
    _ = 2*r := by omega

theorem qPoly_eval (r : ℕ) (x : ℝ) : ((qPoly r).map (algebraMap ℚ ℝ)).eval x =
    ∑ j ∈ range (r+1), G j x * G (r-j) x := by
  rw [qPoly, Polynomial.map_sum, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.map_mul, Polynomial.eval_mul, gPoly_eval, gPoly_eval]

end EulerianGrothendieck.AllOrders
