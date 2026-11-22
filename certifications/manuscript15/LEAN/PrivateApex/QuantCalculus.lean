import PrivateApex.ExpansionCalculus

/-!
PRIVATE.  Manuscript 15: expansions with explicit constants.

`ExpansionCalculus` proves the existence of the constants of uniform asymptotic expansions.
Here the constants are tracked: `HasExpQ S w n f a C` states that, for every order `P ≤ n` and
every `x ∈ S`,

  `|f x - ∑ i < P, a i * w x ^ i| ≤ C P * |w x| ^ P`,

with rational coefficient and constant sequences `a C : ℕ → ℚ`.  The constants of products,
powers and substitutions are given by the computable functions `mulC`, `powC`, `compC`, so that
explicit numerical bounds can be evaluated by the kernel.

* `HasExpQ.mul`, `HasExpQ.pow`, `HasExpQ.comp`, `HasExpQ.shift`, `HasExpQ.neg`;
* `HasExpQ.of_top`: a bound at the top order gives all lower orders;
* `HasExpQ.improve_zero`: a sharper bound of the function itself.
-/

namespace PrivateApex
open Finset

section Quant
variable {α : Type*} {S : Set α} {w f g : α → ℝ} {n : ℕ} {a b C Cf Cg : ℕ → ℚ}

/-- Expansion with explicit constants up to the order `n`. -/
def HasExpQ (S : Set α) (w : α → ℝ) (n : ℕ) (f : α → ℝ) (a C : ℕ → ℚ) : Prop :=
  ∀ P ≤ n, ∀ x ∈ S, |f x - ∑ i ∈ range P, (a i : ℝ) * w x ^ i| ≤ (C P : ℝ) * |w x| ^ P

theorem HasExpQ.bdd (h : HasExpQ S w n f a C) {x : α} (hx : x ∈ S) : |f x| ≤ (C 0 : ℝ) := by
  have h0 := h 0 (Nat.zero_le n) x hx
  simpa using h0

theorem HasExpQ.mono_order {m : ℕ} (h : HasExpQ S w n f a C) (hm : m ≤ n) :
    HasExpQ S w m f a C := fun P hP x hx => h P (hP.trans hm) x hx

theorem HasExpQ.mono_set {T : Set α} (h : HasExpQ S w n f a C) (hT : T ⊆ S) :
    HasExpQ T w n f a C := fun P hP x hx => h P hP x (hT hx)

theorem HasExpQ.mono_const {C' : ℕ → ℚ} (h : HasExpQ S w n f a C) (hC : ∀ P ≤ n, C P ≤ C' P) :
    HasExpQ S w n f a C' := fun P hP x hx =>
  (h P hP x hx).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hC P hP) (by positivity))

theorem HasExpQ.congr (h : HasExpQ S w n f a C) (hfg : ∀ x ∈ S, g x = f x) :
    HasExpQ S w n g a C := fun P hP x hx => by rw [hfg x hx]; exact h P hP x hx

theorem HasExpQ.congr_coeff (h : HasExpQ S w n f a C) (hab : ∀ i < n, b i = a i) :
    HasExpQ S w n f b C := fun P hP x hx => by
  have e : ∑ i ∈ range P, (b i : ℝ) * w x ^ i = ∑ i ∈ range P, (a i : ℝ) * w x ^ i :=
    sum_congr rfl fun i hi => by rw [hab i (lt_of_lt_of_le (mem_range.1 hi) hP)]
  rw [e]
  exact h P hP x hx

theorem HasExpQ.comap {β : Type*} {T : Set β} (h : HasExpQ S w n f a C) (φ : β → α)
    (hφ : ∀ y ∈ T, φ y ∈ S) : HasExpQ T (fun y => w (φ y)) n (fun y => f (φ y)) a C :=
  fun P hP y hy => h P hP (φ y) (hφ y hy)

theorem HasExpQ.neg (h : HasExpQ S w n f a C) :
    HasExpQ S w n (fun x => -f x) (fun i => -a i) C := fun P hP x hx => by
  have hs : ∑ i ∈ range P, ((-a i : ℚ) : ℝ) * w x ^ i =
      -∑ i ∈ range P, (a i : ℝ) * w x ^ i := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun i _ => by push_cast; ring
  have e : -f x - ∑ i ∈ range P, ((-a i : ℚ) : ℝ) * w x ^ i =
      -(f x - ∑ i ∈ range P, (a i : ℝ) * w x ^ i) := by
    rw [hs]
    ring
  rw [e, abs_neg]
  exact h P hP x hx

/-! ### Products -/

/-- Constant of a product. -/
def mulC (a Cf Cg : ℕ → ℚ) (P : ℕ) : ℚ :=
  |Cf P| * |Cg 0| + ∑ i ∈ range P, |a i| * |Cg (P - i)|

theorem HasExpQ.mul (hf : HasExpQ S w n f a Cf) (hg : HasExpQ S w n g b Cg) :
    HasExpQ S w n (fun x => f x * g x) (cmul a b) (mulC a Cf Cg) := by
  intro P hP x hx
  have hCf := hf P hP x hx
  have hCg : ∀ Q ≤ n, |g x - ∑ j ∈ range Q, (b j : ℝ) * w x ^ j| ≤ (Cg Q : ℝ) * |w x| ^ Q :=
    fun Q hQ => hg Q hQ x hx
  have hcast : ∀ k, ((cmul a b k : ℚ) : ℝ) = cmul (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) k :=
    fun k => map_cmul (Rat.castHom ℝ) a b k
  have h1 : ∑ k ∈ range P, ((cmul a b k : ℚ) : ℝ) * w x ^ k =
      ∑ i ∈ range P, ∑ j ∈ range (P - i), (a i : ℝ) * (b j : ℝ) * w x ^ (i + j) := by
    rw [sum_triangle (fun i j => (a i : ℝ) * (b j : ℝ) * w x ^ (i + j)) P]
    refine sum_congr rfl fun k _ => ?_
    rw [hcast, cmul, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i + (k - i) = k := by
      have := mem_range.1 hi
      omega
    show (a i : ℝ) * (b (k - i) : ℝ) * w x ^ k = (a i : ℝ) * (b (k - i) : ℝ) * w x ^ (i + (k - i))
    rw [hi']
  have h2 : ∀ i ∈ range P,
      (a i : ℝ) * w x ^ i * (g x - ∑ j ∈ range (P - i), (b j : ℝ) * w x ^ j) =
        (a i : ℝ) * w x ^ i * g x - ∑ j ∈ range (P - i), (a i : ℝ) * (b j : ℝ) * w x ^ (i + j) := by
    intro i _
    rw [mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  have key : f x * g x - ∑ k ∈ range P, ((cmul a b k : ℚ) : ℝ) * w x ^ k =
      (f x - ∑ i ∈ range P, (a i : ℝ) * w x ^ i) * g x +
        ∑ i ∈ range P, (a i : ℝ) * w x ^ i *
          (g x - ∑ j ∈ range (P - i), (b j : ℝ) * w x ^ j) := by
    rw [h1, sum_congr rfl h2, sum_sub_distrib, ← sum_mul]
    ring
  have hg0 : |g x| ≤ |(Cg 0 : ℝ)| := (hg.bdd hx).trans (le_abs_self _)
  have e1 : |(f x - ∑ i ∈ range P, (a i : ℝ) * w x ^ i) * g x| ≤
      |(Cf P : ℝ)| * |(Cg 0 : ℝ)| * |w x| ^ P := by
    rw [abs_mul]
    have h' : |f x - ∑ i ∈ range P, (a i : ℝ) * w x ^ i| ≤ |(Cf P : ℝ)| * |w x| ^ P :=
      hCf.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    calc |f x - ∑ i ∈ range P, (a i : ℝ) * w x ^ i| * |g x|
        ≤ (|(Cf P : ℝ)| * |w x| ^ P) * |(Cg 0 : ℝ)| :=
          mul_le_mul h' hg0 (abs_nonneg _) (by positivity)
      _ = |(Cf P : ℝ)| * |(Cg 0 : ℝ)| * |w x| ^ P := by ring
  have e2 : |∑ i ∈ range P, (a i : ℝ) * w x ^ i *
        (g x - ∑ j ∈ range (P - i), (b j : ℝ) * w x ^ j)| ≤
      (∑ i ∈ range P, |(a i : ℝ)| * |(Cg (P - i) : ℝ)|) * |w x| ^ P := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    have hi' := mem_range.1 hi
    rw [abs_mul, abs_mul, abs_pow]
    have h' : |g x - ∑ j ∈ range (P - i), (b j : ℝ) * w x ^ j| ≤
        |(Cg (P - i) : ℝ)| * |w x| ^ (P - i) :=
      (hCg (P - i) (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hp : |w x| ^ i * |w x| ^ (P - i) = |w x| ^ P := by
      rw [← pow_add]
      congr 1
      omega
    calc |(a i : ℝ)| * |w x| ^ i * |g x - ∑ j ∈ range (P - i), (b j : ℝ) * w x ^ j|
        ≤ |(a i : ℝ)| * |w x| ^ i * (|(Cg (P - i) : ℝ)| * |w x| ^ (P - i)) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
      _ = |(a i : ℝ)| * |(Cg (P - i) : ℝ)| * (|w x| ^ i * |w x| ^ (P - i)) := by ring
      _ = |(a i : ℝ)| * |(Cg (P - i) : ℝ)| * |w x| ^ P := by rw [hp]
  have hC : ((mulC a Cf Cg P : ℚ) : ℝ) =
      |(Cf P : ℝ)| * |(Cg 0 : ℝ)| + ∑ i ∈ range P, |(a i : ℝ)| * |(Cg (P - i) : ℝ)| := by
    simp [mulC]
  rw [key, hC, add_mul]
  exact (abs_add_le _ _).trans (add_le_add e1 e2)

/-! ### Powers -/

/-- Constants of the powers. -/
def powC (a C : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => fun P => if P = 0 then 1 else 0
  | k + 1 => mulC (cpow a k) (powC a C k) C

theorem HasExpQ.pow (hf : HasExpQ S w n f a C) (k : ℕ) :
    HasExpQ S w n (fun x => f x ^ k) (cpow a k) (powC a C k) := by
  induction k with
  | zero =>
    intro P hP x hx
    rcases P with _ | P
    · simp [powC]
    · have hs : ∑ i ∈ range (P + 1), ((cpow a 0 i : ℚ) : ℝ) * w x ^ i = 1 := by
        rw [sum_range_succ']
        simp [cpow_zero]
      rw [hs]
      simp [powC]
  | succ k ih => exact (ih.mul hf).congr fun x _ => pow_succ (f x) k

/-! ### Substitution -/

/-- Constant of a substitution. -/
def compC (a c Cf Cy : ℕ → ℚ) (P : ℕ) : ℚ :=
  |Cf P| * |Cy 0| ^ P + ∑ i ∈ range P, |a i| * |powC c Cy i (P - i)|

/-- Change of gauge with explicit constants: if `f` expands in the gauge `v = w * y` and `y`
expands in the gauge `w`, then `f` expands in the gauge `w`. -/
theorem HasExpQ.comp {v y : α → ℝ} {c Cy : ℕ → ℚ} (hf : HasExpQ S v n f a Cf)
    (hv : ∀ x ∈ S, v x = w x * y x) (hy : HasExpQ S w n y c Cy) :
    HasExpQ S w n f (ccomp a c) (compC a c Cf Cy) := by
  intro P hP x hx
  have hCf := hf P hP x hx
  have hCp : ∀ i : ℕ, |y x ^ i - ∑ l ∈ range (P - i), ((cpow c i l : ℚ) : ℝ) * w x ^ l| ≤
      ((powC c Cy i (P - i) : ℚ) : ℝ) * |w x| ^ (P - i) :=
    fun i => (hy.pow i) (P - i) ((Nat.sub_le P i).trans hP) x hx
  have hcast : ∀ m, ((ccomp a c m : ℚ) : ℝ) =
      ∑ i ∈ range (m + 1), (a i : ℝ) * ((cpow c i (m - i) : ℚ) : ℝ) := by
    intro m
    simp [ccomp]
  have h1 : ∑ m ∈ range P, ((ccomp a c m : ℚ) : ℝ) * w x ^ m =
      ∑ i ∈ range P, ∑ l ∈ range (P - i),
        (a i : ℝ) * ((cpow c i l : ℚ) : ℝ) * w x ^ (i + l) := by
    rw [sum_triangle (fun i l => (a i : ℝ) * ((cpow c i l : ℚ) : ℝ) * w x ^ (i + l)) P]
    refine sum_congr rfl fun m _ => ?_
    rw [hcast, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i + (m - i) = m := by
      have := mem_range.1 hi
      omega
    show (a i : ℝ) * ((cpow c i (m - i) : ℚ) : ℝ) * w x ^ m =
      (a i : ℝ) * ((cpow c i (m - i) : ℚ) : ℝ) * w x ^ (i + (m - i))
    rw [hi']
  have h2 : ∀ i ∈ range P,
      (a i : ℝ) * w x ^ i * (y x ^ i - ∑ l ∈ range (P - i), ((cpow c i l : ℚ) : ℝ) * w x ^ l) =
        (a i : ℝ) * v x ^ i -
          ∑ l ∈ range (P - i), (a i : ℝ) * ((cpow c i l : ℚ) : ℝ) * w x ^ (i + l) := by
    intro i _
    rw [hv x hx, mul_pow, mul_sub, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun l _ => by ring
  have key : f x - ∑ m ∈ range P, ((ccomp a c m : ℚ) : ℝ) * w x ^ m =
      (f x - ∑ i ∈ range P, (a i : ℝ) * v x ^ i) +
        ∑ i ∈ range P, (a i : ℝ) * w x ^ i *
          (y x ^ i - ∑ l ∈ range (P - i), ((cpow c i l : ℚ) : ℝ) * w x ^ l) := by
    rw [h1, sum_congr rfl h2, sum_sub_distrib]
    ring
  have hy0 : |y x| ≤ |(Cy 0 : ℝ)| := (hy.bdd hx).trans (le_abs_self _)
  have e1 : |f x - ∑ i ∈ range P, (a i : ℝ) * v x ^ i| ≤
      |(Cf P : ℝ)| * |(Cy 0 : ℝ)| ^ P * |w x| ^ P := by
    have h' : |f x - ∑ i ∈ range P, (a i : ℝ) * v x ^ i| ≤ |(Cf P : ℝ)| * |v x| ^ P :=
      hCf.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hvP : |v x| ^ P ≤ |(Cy 0 : ℝ)| ^ P * |w x| ^ P := by
      rw [hv x hx, abs_mul, mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hy0 P) (by positivity)
    calc |f x - ∑ i ∈ range P, (a i : ℝ) * v x ^ i| ≤ |(Cf P : ℝ)| * |v x| ^ P := h'
      _ ≤ |(Cf P : ℝ)| * (|(Cy 0 : ℝ)| ^ P * |w x| ^ P) :=
          mul_le_mul_of_nonneg_left hvP (abs_nonneg _)
      _ = |(Cf P : ℝ)| * |(Cy 0 : ℝ)| ^ P * |w x| ^ P := by ring
  have e2 : |∑ i ∈ range P, (a i : ℝ) * w x ^ i *
        (y x ^ i - ∑ l ∈ range (P - i), ((cpow c i l : ℚ) : ℝ) * w x ^ l)| ≤
      (∑ i ∈ range P, |(a i : ℝ)| * |((powC c Cy i (P - i) : ℚ) : ℝ)|) * |w x| ^ P := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    have hi' := mem_range.1 hi
    rw [abs_mul, abs_mul, abs_pow]
    have h' : |y x ^ i - ∑ l ∈ range (P - i), ((cpow c i l : ℚ) : ℝ) * w x ^ l| ≤
        |((powC c Cy i (P - i) : ℚ) : ℝ)| * |w x| ^ (P - i) :=
      (hCp i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hp : |w x| ^ i * |w x| ^ (P - i) = |w x| ^ P := by
      rw [← pow_add]
      congr 1
      omega
    calc |(a i : ℝ)| * |w x| ^ i *
          |y x ^ i - ∑ l ∈ range (P - i), ((cpow c i l : ℚ) : ℝ) * w x ^ l|
        ≤ |(a i : ℝ)| * |w x| ^ i * (|((powC c Cy i (P - i) : ℚ) : ℝ)| * |w x| ^ (P - i)) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
      _ = |(a i : ℝ)| * |((powC c Cy i (P - i) : ℚ) : ℝ)| * (|w x| ^ i * |w x| ^ (P - i)) := by
          ring
      _ = |(a i : ℝ)| * |((powC c Cy i (P - i) : ℚ) : ℝ)| * |w x| ^ P := by rw [hp]
  have hC : ((compC a c Cf Cy P : ℚ) : ℝ) =
      |(Cf P : ℝ)| * |(Cy 0 : ℝ)| ^ P +
        ∑ i ∈ range P, |(a i : ℝ)| * |((powC c Cy i (P - i) : ℚ) : ℝ)| := by
    simp [compC]
  rw [key, hC, add_mul]
  exact (abs_add_le _ _).trans (add_le_add e1 e2)

/-! ### Removal of the first terms -/

/-- Removal of the first `m` terms and division by `w ^ m`. -/
theorem HasExpQ.shift (m : ℕ) (hf : HasExpQ S w (m + n) f a C)
    (hfg : ∀ x ∈ S, f x = ∑ i ∈ range m, (a i : ℝ) * w x ^ i + w x ^ m * g x)
    (hg0 : ∀ x ∈ S, w x = 0 → g x = (a m : ℝ)) :
    HasExpQ S w n g (fun i => a (i + m)) (fun P => |C (m + P)| + if P = 0 then |a m| else 0) := by
  intro P hP x hx
  have hnn : (0 : ℝ) ≤ ((|C (m + P)| + if P = 0 then |a m| else 0 : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ |C (m + P)| + if P = 0 then |a m| else 0 := by
      split_ifs <;> positivity
    exact_mod_cast this
  by_cases hw0 : w x = 0
  · rw [hg0 x hx hw0, hw0]
    rcases P with _ | P
    · simp
    · have hs : ∑ i ∈ range (P + 1), (a (i + m) : ℝ) * (0 : ℝ) ^ i = (a m : ℝ) := by
        rw [sum_range_succ']
        simp
      rw [hs, sub_self, abs_zero]
      exact mul_nonneg hnn (by positivity)
  · have h := hf (m + P) (by omega) x hx
    have e : f x - ∑ i ∈ range (m + P), (a i : ℝ) * w x ^ i =
        w x ^ m * (g x - ∑ i ∈ range P, (a (i + m) : ℝ) * w x ^ i) := by
      rw [sum_range_add, hfg x hx, mul_sub, mul_sum]
      have e' : ∑ i ∈ range P, (a (m + i) : ℝ) * w x ^ (m + i) =
          ∑ i ∈ range P, w x ^ m * ((a (i + m) : ℝ) * w x ^ i) :=
        sum_congr rfl fun i _ => by rw [add_comm m i, pow_add]; ring
      rw [e']
      ring
    rw [e, abs_mul, abs_pow, pow_add] at h
    have hpos : 0 < |w x| ^ m := pow_pos (abs_pos.2 hw0) m
    have h' : |w x| ^ m * |g x - ∑ i ∈ range P, (a (i + m) : ℝ) * w x ^ i| ≤
        |w x| ^ m * ((C (m + P) : ℝ) * |w x| ^ P) := by
      calc _ ≤ (C (m + P) : ℝ) * (|w x| ^ m * |w x| ^ P) := h
        _ = _ := by ring
    have h'' := le_of_mul_le_mul_left h' hpos
    refine h''.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hle : C (m + P) ≤ |C (m + P)| + if P = 0 then |a m| else 0 := by
      have h1 := le_abs_self (C (m + P))
      split_ifs
      · linarith [abs_nonneg (a m)]
      · linarith
    exact_mod_cast hle

/-! ### From the top order to the lower orders -/

/-- A bound at the order `n` gives explicit bounds at all the orders `P ≤ n`, when the gauge is
bounded by `W`. -/
theorem HasExpQ.of_top {W : ℚ} (hW : ∀ x ∈ S, |w x| ≤ (W : ℝ)) {D : ℚ}
    (h : ∀ x ∈ S, |f x - ∑ i ∈ range n, (a i : ℝ) * w x ^ i| ≤ (D : ℝ) * |w x| ^ n) :
    HasExpQ S w n f a
      (fun P => |D| * W ^ (n - P) + ∑ i ∈ range (n - P), |a (P + i)| * W ^ i) := by
  intro P hP x hx
  have hz := hW x hx
  have hz0 : 0 ≤ |w x| := abs_nonneg _
  have hsplit : ∑ i ∈ range n, (a i : ℝ) * w x ^ i =
      ∑ i ∈ range P, (a i : ℝ) * w x ^ i +
        ∑ i ∈ range (n - P), (a (P + i) : ℝ) * w x ^ (P + i) := by
    rw [← sum_range_add]
    congr 2
    omega
  have key : f x - ∑ i ∈ range P, (a i : ℝ) * w x ^ i =
      (f x - ∑ i ∈ range n, (a i : ℝ) * w x ^ i) +
        ∑ i ∈ range (n - P), (a (P + i) : ℝ) * w x ^ (P + i) := by
    rw [hsplit]
    ring
  have e1 : |f x - ∑ i ∈ range n, (a i : ℝ) * w x ^ i| ≤
      |(D : ℝ)| * (W : ℝ) ^ (n - P) * |w x| ^ P := by
    have hn : |w x| ^ n = |w x| ^ (n - P) * |w x| ^ P := by
      rw [← pow_add]
      congr 1
      omega
    calc |f x - ∑ i ∈ range n, (a i : ℝ) * w x ^ i| ≤ (D : ℝ) * |w x| ^ n := h x hx
      _ ≤ |(D : ℝ)| * |w x| ^ n := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = |(D : ℝ)| * |w x| ^ (n - P) * |w x| ^ P := by rw [hn]; ring
      _ ≤ |(D : ℝ)| * (W : ℝ) ^ (n - P) * |w x| ^ P :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz _) (abs_nonneg _))
            (by positivity)
  have e2 : |∑ i ∈ range (n - P), (a (P + i) : ℝ) * w x ^ (P + i)| ≤
      (∑ i ∈ range (n - P), |(a (P + i) : ℝ)| * (W : ℝ) ^ i) * |w x| ^ P := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_pow, pow_add]
    calc |(a (P + i) : ℝ)| * (|w x| ^ P * |w x| ^ i)
        = |(a (P + i) : ℝ)| * |w x| ^ i * |w x| ^ P := by ring
      _ ≤ |(a (P + i) : ℝ)| * (W : ℝ) ^ i * |w x| ^ P :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz _) (abs_nonneg _))
            (by positivity)
  have hC : ((|D| * W ^ (n - P) + ∑ i ∈ range (n - P), |a (P + i)| * W ^ i : ℚ) : ℝ) =
      |(D : ℝ)| * (W : ℝ) ^ (n - P) + ∑ i ∈ range (n - P), |(a (P + i) : ℝ)| * (W : ℝ) ^ i := by
    simp
  rw [key, hC, add_mul]
  exact (abs_add_le _ _).trans (add_le_add e1 e2)

/-- The constants of the lower orders can be replaced by those obtained from the top order. -/
theorem HasExpQ.improve {W : ℚ} (hW : ∀ x ∈ S, |w x| ≤ (W : ℝ)) (h : HasExpQ S w n f a C) :
    HasExpQ S w n f a
      (fun P => |C n| * W ^ (n - P) + ∑ i ∈ range (n - P), |a (P + i)| * W ^ i) :=
  HasExpQ.of_top hW (h n le_rfl)

/-- A sharper bound of the function itself, from the expansion of order `q`. -/
theorem HasExpQ.improve_zero {W : ℚ} (hW : ∀ x ∈ S, |w x| ≤ (W : ℝ)) (h : HasExpQ S w n f a C)
    {q : ℕ} (hq : q ≤ n) :
    HasExpQ S w n f a
      (fun P => if P = 0 then |C q| * W ^ q + ∑ i ∈ range q, |a i| * W ^ i else C P) := by
  intro P hP x hx
  rcases P with _ | P
  · have h0 := (HasExpQ.of_top hW (h q hq)) 0 (Nat.zero_le q) x hx
    simpa using h0
  · simpa using h (P + 1) hP x hx

end Quant

end PrivateApex
