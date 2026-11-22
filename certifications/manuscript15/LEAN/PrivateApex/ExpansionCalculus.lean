import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt

/-!
PRIVATE.  A calculus of uniform asymptotic expansions to every finite order.

`HasExp S w f a` says that, on the set `S`, the function `f` is approximated by the
polynomials `∑ i < P, a i * w ^ i` in the gauge `w`, with an error `O(|w| ^ P)` for every
order `P`.  The coefficient sequences are combined by three explicit rational operations:
the Cauchy product `cmul`, the power `cpow` and the substitution `ccomp`, which gives the
coefficients of `A (z * B z)`.  All three are computable on `ℚ`.
-/

namespace PrivateApex
open Finset

section Formal
variable {K : Type*} [CommRing K]

/-- Cauchy product of two coefficient sequences. -/
def cmul (a b : ℕ → K) (n : ℕ) : K := ∑ i ∈ range (n + 1), a i * b (n - i)

/-- Coefficients of the `k`-th power of a series. -/
def cpow (a : ℕ → K) : ℕ → ℕ → K
  | 0 => fun n => if n = 0 then 1 else 0
  | k + 1 => cmul (cpow a k) a

/-- Coefficients of the substitution `A (z * B z)`. -/
def ccomp (a b : ℕ → K) (m : ℕ) : K := ∑ i ∈ range (m + 1), a i * cpow b i (m - i)

theorem cpow_zero (a : ℕ → K) : cpow a 0 = fun n => if n = 0 then 1 else 0 := rfl

theorem cpow_succ (a : ℕ → K) (k : ℕ) : cpow a (k + 1) = cmul (cpow a k) a := rfl

variable {L : Type*} [CommRing L]

theorem map_cmul (φ : K →+* L) (a b : ℕ → K) (n : ℕ) :
    φ (cmul a b n) = cmul (fun i => φ (a i)) (fun i => φ (b i)) n := by
  simp only [cmul, map_sum, map_mul]

theorem map_cpow (φ : K →+* L) (a : ℕ → K) (k n : ℕ) :
    φ (cpow a k n) = cpow (fun i => φ (a i)) k n := by
  induction k generalizing n with
  | zero =>
    simp only [cpow_zero]
    split_ifs <;> simp
  | succ k ih =>
    rw [cpow_succ, cpow_succ, map_cmul]
    have h : (fun i => φ (cpow a k i)) = cpow (fun i => φ (a i)) k := funext ih
    rw [h]

theorem map_ccomp (φ : K →+* L) (a b : ℕ → K) (m : ℕ) :
    φ (ccomp a b m) = ccomp (fun i => φ (a i)) (fun i => φ (b i)) m := by
  simp only [ccomp, map_sum, map_mul, map_cpow]

end Formal

/-- Reindexing of a triangular double sum along its antidiagonals. -/
theorem sum_triangle {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (P : ℕ) :
    ∑ i ∈ range P, ∑ j ∈ range (P - i), F i j =
      ∑ n ∈ range P, ∑ i ∈ range (n + 1), F i (n - i) := by
  induction P with
  | zero => simp
  | succ P ih =>
    have h1 : ∑ i ∈ range P, ∑ j ∈ range (P + 1 - i), F i j =
        ∑ i ∈ range P, ∑ j ∈ range (P - i), F i j + ∑ i ∈ range P, F i (P - i) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      have h : P + 1 - i = (P - i) + 1 := by
        have := mem_range.1 hi
        omega
      rw [h, sum_range_succ]
    rw [sum_range_succ, sum_range_succ (fun n => ∑ i ∈ range (n + 1), F i (n - i)), ← ih, h1,
      sum_range_succ (fun i => F i (P - i)) P]
    simp [add_assoc]

section Analytic
variable {α : Type*} {S : Set α} {w f g : α → ℝ} {a b : ℕ → ℝ}

/-- `f` has the expansion `∑ a i * w ^ i` to every finite order, uniformly on `S`. -/
def HasExp (S : Set α) (w f : α → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ P : ℕ, ∃ C : ℝ, ∀ x ∈ S, |f x - ∑ i ∈ range P, a i * w x ^ i| ≤ C * |w x| ^ P

theorem HasExp.bdd (hf : HasExp S w f a) : ∃ C, ∀ x ∈ S, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf 0
  exact ⟨C, fun x hx => by simpa using hC x hx⟩

theorem HasExp.mono {T : Set α} (hf : HasExp S w f a) (h : T ⊆ S) : HasExp T w f a :=
  fun P => (hf P).imp fun _ hC x hx => hC x (h hx)

theorem HasExp.congr (hf : HasExp S w f a) (h : ∀ x ∈ S, g x = f x) : HasExp S w g a :=
  fun P => (hf P).imp fun _ hC x hx => by rw [h x hx]; exact hC x hx

theorem HasExp.congr_coeff (hf : HasExp S w f a) (h : ∀ i, b i = a i) : HasExp S w f b := by
  have e : b = a := funext h
  rw [e]
  exact hf

theorem HasExp.const (S : Set α) (w : α → ℝ) (c : ℝ) :
    HasExp S w (fun _ => c) (fun n => if n = 0 then c else 0) := by
  intro P
  refine ⟨|c|, fun x _ => ?_⟩
  rcases P with _ | P
  · simp
  · have hs : ∑ i ∈ range (P + 1), (if i = 0 then c else 0) * w x ^ i = c := by
      rw [sum_range_succ']
      simp
    rw [hs, sub_self, abs_zero]
    positivity

theorem HasExp.smul (c : ℝ) (hf : HasExp S w f a) :
    HasExp S w (fun x => c * f x) (fun i => c * a i) := by
  intro P
  obtain ⟨C, hC⟩ := hf P
  refine ⟨|c| * |C|, fun x hx => ?_⟩
  have e : c * f x - ∑ i ∈ range P, c * a i * w x ^ i =
      c * (f x - ∑ i ∈ range P, a i * w x ^ i) := by
    rw [mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun i _ => by ring
  rw [e, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    ((hC x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) (abs_nonneg c)

theorem HasExp.neg (hf : HasExp S w f a) : HasExp S w (fun x => -f x) (fun i => -a i) :=
  ((hf.smul (-1)).congr fun x _ => by ring).congr_coeff fun i => by ring

theorem HasExp.add (hf : HasExp S w f a) (hg : HasExp S w g b) :
    HasExp S w (fun x => f x + g x) (fun i => a i + b i) := by
  intro P
  obtain ⟨C, hC⟩ := hf P
  obtain ⟨D, hD⟩ := hg P
  refine ⟨C + D, fun x hx => ?_⟩
  have e : f x + g x - ∑ i ∈ range P, (a i + b i) * w x ^ i =
      (f x - ∑ i ∈ range P, a i * w x ^ i) + (g x - ∑ i ∈ range P, b i * w x ^ i) := by
    simp only [add_mul, sum_add_distrib]
    ring
  rw [e, add_mul]
  exact (abs_add_le _ _).trans (add_le_add (hC x hx) (hD x hx))

/-- Products: the coefficients are given by the Cauchy product. -/
theorem HasExp.mul (hf : HasExp S w f a) (hg : HasExp S w g b) :
    HasExp S w (fun x => f x * g x) (cmul a b) := by
  intro P
  obtain ⟨Cf, hCf⟩ := hf P
  have hg' : ∀ Q : ℕ, ∃ C : ℝ, ∀ x ∈ S,
      |g x - ∑ j ∈ range Q, b j * w x ^ j| ≤ C * |w x| ^ Q := hg
  choose Cg hCg using hg'
  refine ⟨|Cf| * |Cg 0| + ∑ i ∈ range P, |a i| * |Cg (P - i)|, fun x hx => ?_⟩
  have h1 : ∑ n ∈ range P, cmul a b n * w x ^ n =
      ∑ i ∈ range P, ∑ j ∈ range (P - i), a i * b j * w x ^ (i + j) := by
    rw [sum_triangle (fun i j => a i * b j * w x ^ (i + j)) P]
    refine sum_congr rfl fun n _ => ?_
    rw [cmul, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i + (n - i) = n := by
      have := mem_range.1 hi
      omega
    show a i * b (n - i) * w x ^ n = a i * b (n - i) * w x ^ (i + (n - i))
    rw [hi']
  have h2 : ∀ i ∈ range P,
      a i * w x ^ i * (g x - ∑ j ∈ range (P - i), b j * w x ^ j) =
        a i * w x ^ i * g x - ∑ j ∈ range (P - i), a i * b j * w x ^ (i + j) := by
    intro i _
    rw [mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  have key : f x * g x - ∑ n ∈ range P, cmul a b n * w x ^ n =
      (f x - ∑ i ∈ range P, a i * w x ^ i) * g x +
        ∑ i ∈ range P, a i * w x ^ i * (g x - ∑ j ∈ range (P - i), b j * w x ^ j) := by
    rw [h1, sum_congr rfl h2, sum_sub_distrib, ← sum_mul]
    ring
  have hg0 : |g x| ≤ |Cg 0| := by
    have h := hCg 0 x hx
    simp only [range_zero, sum_empty, sub_zero, pow_zero, mul_one] at h
    exact h.trans (le_abs_self _)
  have e1 : |(f x - ∑ i ∈ range P, a i * w x ^ i) * g x| ≤ |Cf| * |Cg 0| * |w x| ^ P := by
    rw [abs_mul]
    have h' : |f x - ∑ i ∈ range P, a i * w x ^ i| ≤ |Cf| * |w x| ^ P :=
      (hCf x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    calc |f x - ∑ i ∈ range P, a i * w x ^ i| * |g x|
        ≤ (|Cf| * |w x| ^ P) * |Cg 0| := mul_le_mul h' hg0 (abs_nonneg _) (by positivity)
      _ = |Cf| * |Cg 0| * |w x| ^ P := by ring
  have e2 : |∑ i ∈ range P, a i * w x ^ i * (g x - ∑ j ∈ range (P - i), b j * w x ^ j)| ≤
      (∑ i ∈ range P, |a i| * |Cg (P - i)|) * |w x| ^ P := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    have hi' := mem_range.1 hi
    rw [abs_mul, abs_mul, abs_pow]
    have h' : |g x - ∑ j ∈ range (P - i), b j * w x ^ j| ≤ |Cg (P - i)| * |w x| ^ (P - i) :=
      (hCg (P - i) x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hp : |w x| ^ i * |w x| ^ (P - i) = |w x| ^ P := by
      rw [← pow_add]
      congr 1
      omega
    calc |a i| * |w x| ^ i * |g x - ∑ j ∈ range (P - i), b j * w x ^ j|
        ≤ |a i| * |w x| ^ i * (|Cg (P - i)| * |w x| ^ (P - i)) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
      _ = |a i| * |Cg (P - i)| * (|w x| ^ i * |w x| ^ (P - i)) := by ring
      _ = |a i| * |Cg (P - i)| * |w x| ^ P := by rw [hp]
  rw [key, add_mul]
  exact (abs_add_le _ _).trans (add_le_add e1 e2)

/-- Powers. -/
theorem HasExp.pow (hf : HasExp S w f a) (k : ℕ) :
    HasExp S w (fun x => f x ^ k) (cpow a k) := by
  induction k with
  | zero => exact (HasExp.const S w 1).congr fun x _ => by simp
  | succ k ih => exact (ih.mul hf).congr fun x _ => pow_succ (f x) k

/-- Change of gauge: if `f` expands in the gauge `v = w * y` and `y` expands in the gauge `w`,
then `f` expands in the gauge `w`, with the substituted coefficients. -/
theorem HasExp.comp {v y : α → ℝ} {c : ℕ → ℝ} (hf : HasExp S v f a)
    (hv : ∀ x ∈ S, v x = w x * y x) (hy : HasExp S w y c) :
    HasExp S w f (ccomp a c) := by
  intro P
  obtain ⟨Cf, hCf⟩ := hf P
  obtain ⟨Y, hY⟩ := hy.bdd
  have hpow : ∀ i : ℕ, ∃ C : ℝ, ∀ x ∈ S,
      |y x ^ i - ∑ l ∈ range (P - i), cpow c i l * w x ^ l| ≤ C * |w x| ^ (P - i) :=
    fun i => (hy.pow i) (P - i)
  choose Cp hCp using hpow
  refine ⟨|Cf| * |Y| ^ P + ∑ i ∈ range P, |a i| * |Cp i|, fun x hx => ?_⟩
  have h1 : ∑ m ∈ range P, ccomp a c m * w x ^ m =
      ∑ i ∈ range P, ∑ l ∈ range (P - i), a i * cpow c i l * w x ^ (i + l) := by
    rw [sum_triangle (fun i l => a i * cpow c i l * w x ^ (i + l)) P]
    refine sum_congr rfl fun n _ => ?_
    rw [ccomp, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i + (n - i) = n := by
      have := mem_range.1 hi
      omega
    show a i * cpow c i (n - i) * w x ^ n = a i * cpow c i (n - i) * w x ^ (i + (n - i))
    rw [hi']
  have h2 : ∀ i ∈ range P,
      a i * w x ^ i * (y x ^ i - ∑ l ∈ range (P - i), cpow c i l * w x ^ l) =
        a i * v x ^ i - ∑ l ∈ range (P - i), a i * cpow c i l * w x ^ (i + l) := by
    intro i _
    rw [hv x hx, mul_pow, mul_sub, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun l _ => by ring
  have key : f x - ∑ m ∈ range P, ccomp a c m * w x ^ m =
      (f x - ∑ i ∈ range P, a i * v x ^ i) +
        ∑ i ∈ range P, a i * w x ^ i * (y x ^ i - ∑ l ∈ range (P - i), cpow c i l * w x ^ l) := by
    rw [h1, sum_congr rfl h2, sum_sub_distrib]
    ring
  have hy0 : |y x| ≤ |Y| := (hY x hx).trans (le_abs_self _)
  have e1 : |f x - ∑ i ∈ range P, a i * v x ^ i| ≤ |Cf| * |Y| ^ P * |w x| ^ P := by
    have h' : |f x - ∑ i ∈ range P, a i * v x ^ i| ≤ |Cf| * |v x| ^ P :=
      (hCf x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hvP : |v x| ^ P ≤ |Y| ^ P * |w x| ^ P := by
      rw [hv x hx, abs_mul, mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hy0 P) (by positivity)
    calc |f x - ∑ i ∈ range P, a i * v x ^ i| ≤ |Cf| * |v x| ^ P := h'
      _ ≤ |Cf| * (|Y| ^ P * |w x| ^ P) := mul_le_mul_of_nonneg_left hvP (abs_nonneg _)
      _ = |Cf| * |Y| ^ P * |w x| ^ P := by ring
  have e2 : |∑ i ∈ range P,
      a i * w x ^ i * (y x ^ i - ∑ l ∈ range (P - i), cpow c i l * w x ^ l)| ≤
      (∑ i ∈ range P, |a i| * |Cp i|) * |w x| ^ P := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    have hi' := mem_range.1 hi
    rw [abs_mul, abs_mul, abs_pow]
    have h' : |y x ^ i - ∑ l ∈ range (P - i), cpow c i l * w x ^ l| ≤
        |Cp i| * |w x| ^ (P - i) :=
      (hCp i x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hp : |w x| ^ i * |w x| ^ (P - i) = |w x| ^ P := by
      rw [← pow_add]
      congr 1
      omega
    calc |a i| * |w x| ^ i * |y x ^ i - ∑ l ∈ range (P - i), cpow c i l * w x ^ l|
        ≤ |a i| * |w x| ^ i * (|Cp i| * |w x| ^ (P - i)) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
      _ = |a i| * |Cp i| * (|w x| ^ i * |w x| ^ (P - i)) := by ring
      _ = |a i| * |Cp i| * |w x| ^ P := by rw [hp]
  rw [key, add_mul]
  exact (abs_add_le _ _).trans (add_le_add e1 e2)

/-- Removal of the first `n` terms and division by `w ^ n`. -/
theorem HasExp.shift (n : ℕ) (hf : HasExp S w f a)
    (hfg : ∀ x ∈ S, f x = ∑ i ∈ range n, a i * w x ^ i + w x ^ n * g x)
    (hg0 : ∀ x ∈ S, w x = 0 → g x = a n) : HasExp S w g (fun i => a (i + n)) := by
  intro P
  obtain ⟨C, hC⟩ := hf (n + P)
  refine ⟨|C| + |a n|, fun x hx => ?_⟩
  by_cases hw0 : w x = 0
  · rw [hg0 x hx hw0, hw0]
    rcases P with _ | P
    · simp
    · have hs : ∑ i ∈ range (P + 1), a (i + n) * (0 : ℝ) ^ i = a n := by
        rw [sum_range_succ']
        simp
      rw [hs, sub_self, abs_zero]
      positivity
  · have h := hC x hx
    have e : f x - ∑ i ∈ range (n + P), a i * w x ^ i =
        w x ^ n * (g x - ∑ i ∈ range P, a (i + n) * w x ^ i) := by
      rw [sum_range_add, hfg x hx, mul_sub, mul_sum]
      have e' : ∑ i ∈ range P, a (n + i) * w x ^ (n + i) =
          ∑ i ∈ range P, w x ^ n * (a (i + n) * w x ^ i) :=
        sum_congr rfl fun i _ => by rw [add_comm n i, pow_add]; ring
      rw [e']
      ring
    rw [e, abs_mul, abs_pow, pow_add] at h
    have hpos : 0 < |w x| ^ n := pow_pos (abs_pos.2 hw0) n
    have h' : |w x| ^ n * |g x - ∑ i ∈ range P, a (i + n) * w x ^ i| ≤
        |w x| ^ n * (C * |w x| ^ P) := by
      calc _ ≤ C * (|w x| ^ n * |w x| ^ P) := h
        _ = _ := by ring
    have h'' := le_of_mul_le_mul_left h' hpos
    exact h''.trans (mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self C, abs_nonneg (a n)]) (by positivity))

/-- Uniqueness of the coefficients when the gauge takes arbitrarily small nonzero values. -/
theorem HasExp.unique (hf : HasExp S w f a) (hg : HasExp S w f b)
    (hsmall : ∀ ε > 0, ∃ x ∈ S, w x ≠ 0 ∧ |w x| < ε) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨C1, h1⟩ := hf (n + 1)
    obtain ⟨C2, h2⟩ := hg (n + 1)
    by_contra hne
    have hpos : 0 < |a n - b n| := abs_pos.2 (sub_ne_zero.2 hne)
    have hD : 0 < |C1| + |C2| + 1 := by positivity
    obtain ⟨x, hx, hw0, hwlt⟩ := hsmall (|a n - b n| / (|C1| + |C2| + 1)) (div_pos hpos hD)
    have e : (∑ i ∈ range (n + 1), a i * w x ^ i) - ∑ i ∈ range (n + 1), b i * w x ^ i =
        (a n - b n) * w x ^ n := by
      rw [sum_range_succ, sum_range_succ]
      have hlow : ∑ i ∈ range n, a i * w x ^ i = ∑ i ∈ range n, b i * w x ^ i :=
        sum_congr rfl fun i hi => by rw [ih i (mem_range.1 hi)]
      rw [hlow]
      ring
    have h3 : |(a n - b n) * w x ^ n| ≤ (|C1| + |C2|) * |w x| ^ (n + 1) := by
      rw [← e]
      have ha := h1 x hx
      have hb := h2 x hx
      rw [abs_sub_comm] at ha
      have ha' : |∑ i ∈ range (n + 1), a i * w x ^ i - f x| ≤ |C1| * |w x| ^ (n + 1) :=
        ha.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      have hb' : |f x - ∑ i ∈ range (n + 1), b i * w x ^ i| ≤ |C2| * |w x| ^ (n + 1) :=
        hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      calc _ ≤ |∑ i ∈ range (n + 1), a i * w x ^ i - f x| +
            |f x - ∑ i ∈ range (n + 1), b i * w x ^ i| := abs_sub_le _ _ _
        _ ≤ |C1| * |w x| ^ (n + 1) + |C2| * |w x| ^ (n + 1) := add_le_add ha' hb'
        _ = _ := by ring
    rw [abs_mul, abs_pow, pow_succ] at h3
    have hwpos : 0 < |w x| ^ n := pow_pos (abs_pos.2 hw0) n
    have h4 : |a n - b n| ≤ (|C1| + |C2|) * |w x| := by
      have h' : |w x| ^ n * |a n - b n| ≤ |w x| ^ n * ((|C1| + |C2|) * |w x|) := by
        calc _ = |a n - b n| * |w x| ^ n := by ring
          _ ≤ (|C1| + |C2|) * (|w x| ^ n * |w x|) := h3
          _ = _ := by ring
      exact le_of_mul_le_mul_left h' hwpos
    have h5 : |w x| * (|C1| + |C2| + 1) < |a n - b n| := by rwa [lt_div_iff₀ hD] at hwlt
    nlinarith [abs_nonneg (w x), abs_nonneg C1, abs_nonneg C2]

end Analytic

end PrivateApex
