import Bridge.Saddle.Laplace
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Manuscript 12, Lemma 5.6: strict interior log-concavity of the cardinal B-spline

Source: frozen `12.tex`, label `lem:ul-spline`.  The manuscript obtains the strict monotonicity
of `φ_M'` from Floater, *Log-concavity of B-splines*, J. Approx. Theory 300 (2024) 106042
(Lemma 2 and inequality (11)).  This file gives a self-contained proof for the cardinal B-spline
`w_M`, by induction on `M`, which uses no premise from that paper.

Let `win f x = ∫_{x-1/2}^{x+1/2} f`, so that `w (M+1) = win (w M)`.

* `PF2 f`: `f a * f (b + h) ≤ f (a + h) * f b` for `a ≤ b`, `0 ≤ h` (Pólya frequency of order two);
* `SPF2 f`: the same inequality is strict for `a < b`, `0 < h` whenever its right side is positive.

For continuous `f` the derivative of `win f` is `f (x + 1/2) - f (x - 1/2)`, and for `x ≤ y`
`(win f)'(x) · win f y - (win f)'(y) · win f x` is the integral over `[-1/2, 1/2]` of a function
which is pointwise a sum of two `PF2` defects of `f` (`cross_eq`, `cross_integrand_nonneg`).  Hence
`s ↦ win f (p + s) · win f (q - s)` is nondecreasing while `p + s ≤ q - s`, which is `PF2 (win f)`
(`pf2_win`); the strict statements (`cross_strict`, `spf2_win`) need in addition `f (±1/2) > 0`.

Results for the actual spline:
* `w_two_of_nonpos`, `w_two_of_nonneg`, `w_two_eq_zero`: `w 2 y = max 0 (1 - |y|)`;
* `lc_w`: for `M ≥ 2`, `w M` is continuous, nonnegative, `PF2`, `SPF2`, positive at `±1/2`;
* `w_pos`: `0 < w M y` for `|y| < M/2`, `M ≥ 2`;
* `hasDerivAt_w_succ`: `(w (M+1))'(y) = w M (y + 1/2) - w M (y - 1/2)` for `M ≥ 2`;
* `w_logDeriv_strictAnti`: for `M ≥ 3`, `w_M'/w_M` is strictly decreasing on `(-M/2, M/2)`.
-/

open MeasureTheory Set Filter Topology

namespace EulerianBridge.Saddle

/-- Pólya frequency of order two, in multiplicative form. -/
def PF2 (f : ℝ → ℝ) : Prop :=
  ∀ a b h : ℝ, a ≤ b → 0 ≤ h → f a * f (b + h) ≤ f (a + h) * f b

/-- Strict form of `PF2`: strict as soon as the right side is positive. -/
def SPF2 (f : ℝ → ℝ) : Prop :=
  ∀ a b h : ℝ, a < b → 0 < h → 0 < f (a + h) → 0 < f b → f a * f (b + h) < f (a + h) * f b

/-- The moving average over a window of length one. -/
noncomputable def win (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (x - 1/2)..(x + 1/2), f t

/-- The positivity set of a nonnegative `PF2` function is order-connected. -/
theorem pf2_pos_between {f : ℝ → ℝ} (hP : PF2 f) (h0 : ∀ x, 0 ≤ f x) {p v q : ℝ}
    (hpv : p ≤ v) (hvq : v ≤ q) (hp : 0 < f p) (hq : 0 < f q) : 0 < f v := by
  have hk := hP p (p + q - v) (v - p) (by linarith) (by linarith)
  have e1 : p + q - v + (v - p) = q := by ring
  have e2 : p + (v - p) = v := by ring
  rw [e1, e2] at hk
  rcases (h0 v).lt_or_eq with hv | hv
  · exact hv
  · rw [← hv, zero_mul] at hk
    exact absurd (mul_pos hp hq) (not_lt.mpr hk)

theorem win_eq (f : ℝ → ℝ) (u : ℝ) : win f u = ∫ t in (-(1/2):ℝ)..(1/2), f (u + t) := by
  have hk := intervalIntegral.integral_comp_add_left (a := (-(1/2):ℝ)) (b := 1/2) f u
  have e1 : u + -(1/2) = u - 1/2 := by ring
  rw [hk, e1]
  rfl

/-- Fundamental theorem of calculus for the moving average. -/
theorem hasDerivAt_win {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (win f) (f (x + 1/2) - f (x - 1/2)) x := by
  have hI : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  have hprim : ∀ c : ℝ, HasDerivAt (fun u => ∫ t in (0:ℝ)..u, f t) (f c) c := fun c =>
    intervalIntegral.integral_hasDerivAt_right (hI 0 c) (hf.stronglyMeasurableAtFilter _ _)
      hf.continuousAt
  have heq : win f = fun y => (∫ t in (0:ℝ)..(y + 1/2), f t) - ∫ t in (0:ℝ)..(y - 1/2), f t := by
    funext y
    unfold win
    rw [intervalIntegral.integral_interval_sub_left (hI _ _) (hI _ _)]
  rw [heq]
  exact ((hprim (x + 1/2)).comp_add_const x (1/2)).fun_sub
    ((hprim (x - 1/2)).comp_sub_const x (1/2))

theorem continuous_win {f : ℝ → ℝ} (hf : Continuous f) : Continuous (win f) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_win hf x).continuousAt

theorem win_nonneg {f : ℝ → ℝ} (h0 : ∀ x, 0 ≤ f x) (x : ℝ) : 0 ≤ win f x := by
  unfold win
  exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => h0 t)

/-- A continuous nonnegative function with a positive value in the closed window has a positive
moving average. -/
theorem win_pos_of {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) {x c : ℝ}
    (hc : c ∈ Icc (x - 1/2) (x + 1/2)) (hfc : 0 < f c) : 0 < win f x := by
  have hk := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0:ℝ)) (g := f) (a := x - 1/2) (b := x + 1/2) (by linarith)
    continuousOn_const hf.continuousOn (fun t _ => h0 t) ⟨c, hc, hfc⟩
  rw [intervalIntegral.integral_zero] at hk
  exact hk

theorem exists_pos_of_win_pos {f : ℝ → ℝ} (h0 : ∀ x, 0 ≤ f x) {x : ℝ} (hx : 0 < win f x) :
    ∃ c ∈ Icc (x - 1/2) (x + 1/2), 0 < f c := by
  by_contra hne
  push_neg at hne
  have hz : win f x = 0 := by
    unfold win
    have hEq : EqOn f (fun _ => (0:ℝ)) (uIcc (x - 1/2) (x + 1/2)) := by
      intro t ht
      rw [uIcc_of_le (by linarith : x - 1/2 ≤ x + 1/2)] at ht
      exact le_antisymm (hne t ht) (h0 t)
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
  linarith

/-- The Wronskian of the moving average at two points, as one integral. -/
theorem cross_eq {f : ℝ → ℝ} (hf : Continuous f) (x y : ℝ) :
    (f (x + 1/2) - f (x - 1/2)) * win f y - (f (y + 1/2) - f (y - 1/2)) * win f x =
      ∫ t in (-(1/2):ℝ)..(1/2), ((f (x + 1/2) - f (x - 1/2)) * f (y + t) -
        (f (y + 1/2) - f (y - 1/2)) * f (x + t)) := by
  have hcx : Continuous fun t : ℝ => f (x + t) := hf.comp (continuous_const.add continuous_id)
  have hcy : Continuous fun t : ℝ => f (y + t) := hf.comp (continuous_const.add continuous_id)
  have hIx : IntervalIntegrable (fun t : ℝ => f (x + t)) volume (-(1/2)) (1/2) :=
    hcx.intervalIntegrable _ _
  have hIy : IntervalIntegrable (fun t : ℝ => f (y + t)) volume (-(1/2)) (1/2) :=
    hcy.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hIy.const_mul _) (hIx.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, win_eq f x,
    win_eq f y]

/-- The integrand of `cross_eq` is a sum of two `PF2` defects. -/
theorem cross_integrand_nonneg {f : ℝ → ℝ} (hP : PF2 f) {x y t : ℝ} (hxy : x ≤ y)
    (h1 : -(1/2) ≤ t) (h2 : t ≤ 1/2) :
    0 ≤ (f (x + 1/2) - f (x - 1/2)) * f (y + t) - (f (y + 1/2) - f (y - 1/2)) * f (x + t) := by
  have hA := hP (x + t) (y + t) (1/2 - t) (by linarith) (by linarith)
  have hB := hP (x - 1/2) (y - 1/2) (t + 1/2) (by linarith) (by linarith)
  have e1 : y + t + (1/2 - t) = y + 1/2 := by ring
  have e2 : x + t + (1/2 - t) = x + 1/2 := by ring
  have e3 : y - 1/2 + (t + 1/2) = y + t := by ring
  have e4 : x - 1/2 + (t + 1/2) = x + t := by ring
  rw [e1, e2] at hA
  rw [e3, e4] at hB
  nlinarith [hA, hB]

theorem cross_integrand_pos_left {f : ℝ → ℝ} (hP : PF2 f) (hS : SPF2 f) {x y t : ℝ}
    (hxy : x < y) (h1 : -(1/2) ≤ t) (h2 : t < 1/2) (hx : 0 < f (x + 1/2))
    (hy : 0 < f (y + t)) :
    0 < (f (x + 1/2) - f (x - 1/2)) * f (y + t) - (f (y + 1/2) - f (y - 1/2)) * f (x + t) := by
  have e2 : x + t + (1/2 - t) = x + 1/2 := by ring
  have hA := hS (x + t) (y + t) (1/2 - t) (by linarith) (by linarith)
    (by rw [e2]; exact hx) hy
  have hB := hP (x - 1/2) (y - 1/2) (t + 1/2) (by linarith) (by linarith)
  have e1 : y + t + (1/2 - t) = y + 1/2 := by ring
  have e3 : y - 1/2 + (t + 1/2) = y + t := by ring
  have e4 : x - 1/2 + (t + 1/2) = x + t := by ring
  rw [e1, e2] at hA
  rw [e3, e4] at hB
  nlinarith [hA, hB]

theorem cross_integrand_pos_right {f : ℝ → ℝ} (hP : PF2 f) (hS : SPF2 f) {x y t : ℝ}
    (hxy : x < y) (h1 : -(1/2) < t) (h2 : t ≤ 1/2) (hx : 0 < f (x + t))
    (hy : 0 < f (y - 1/2)) :
    0 < (f (x + 1/2) - f (x - 1/2)) * f (y + t) - (f (y + 1/2) - f (y - 1/2)) * f (x + t) := by
  have e4 : x - 1/2 + (t + 1/2) = x + t := by ring
  have hA := hP (x + t) (y + t) (1/2 - t) (by linarith) (by linarith)
  have hB := hS (x - 1/2) (y - 1/2) (t + 1/2) (by linarith) (by linarith)
    (by rw [e4]; exact hx) hy
  have e1 : y + t + (1/2 - t) = y + 1/2 := by ring
  have e2 : x + t + (1/2 - t) = x + 1/2 := by ring
  have e3 : y - 1/2 + (t + 1/2) = y + t := by ring
  rw [e1, e2] at hA
  rw [e3, e4] at hB
  nlinarith [hA, hB]

/-- `(win f)'/(win f)` is nonincreasing, in cross-multiplied form. -/
theorem cross {f : ℝ → ℝ} (hf : Continuous f) (hP : PF2 f) {x y : ℝ} (hxy : x ≤ y) :
    (f (y + 1/2) - f (y - 1/2)) * win f x ≤ (f (x + 1/2) - f (x - 1/2)) * win f y := by
  have hk := cross_eq hf x y
  have hnn : 0 ≤ ∫ t in (-(1/2):ℝ)..(1/2), ((f (x + 1/2) - f (x - 1/2)) * f (y + t) -
      (f (y + 1/2) - f (y - 1/2)) * f (x + t)) :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => cross_integrand_nonneg hP hxy ht.1 ht.2)
  linarith

/-- `(win f)'/(win f)` is strictly decreasing on the positivity set of `win f`, in
cross-multiplied form. -/
theorem cross_strict {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) (hP : PF2 f)
    (hS : SPF2 f) (hm : 0 < f (-(1/2))) (hp : 0 < f (1/2)) {x y : ℝ} (hxy : x < y)
    (hx : 0 < win f x) (hy : 0 < win f y) :
    (f (y + 1/2) - f (y - 1/2)) * win f x < (f (x + 1/2) - f (x - 1/2)) * win f y := by
  obtain ⟨cx, hcx, hfx⟩ := exists_pos_of_win_pos h0 hx
  obtain ⟨cy, hcy, hfy⟩ := exists_pos_of_win_pos h0 hy
  have hk := cross_eq hf x y
  have hcont : Continuous fun t : ℝ => (f (x + 1/2) - f (x - 1/2)) * f (y + t) -
      (f (y + 1/2) - f (y - 1/2)) * f (x + t) :=
    (continuous_const.mul (hf.comp (continuous_const.add continuous_id))).sub
      (continuous_const.mul (hf.comp (continuous_const.add continuous_id)))
  have hex : ∃ t ∈ Icc (-(1/2):ℝ) (1/2), 0 < (f (x + 1/2) - f (x - 1/2)) * f (y + t) -
      (f (y + 1/2) - f (y - 1/2)) * f (x + t) := by
    by_cases h1 : 0 < f (x + 1/2)
    · rcases le_total (x + 1/2) (y - 1/2) with hle | hle
      · refine ⟨-(1/2), ⟨le_rfl, by norm_num⟩,
          cross_integrand_pos_left hP hS hxy le_rfl (by norm_num) h1 ?_⟩
        exact pf2_pos_between hP h0 (p := x + 1/2) (q := cy) (by linarith)
          (by linarith [hcy.1]) h1 hfy
      · refine ⟨x - y + 1/2, ⟨by linarith, by linarith⟩,
          cross_integrand_pos_left hP hS hxy (by linarith) (by linarith) h1 ?_⟩
        have e : y + (x - y + 1/2) = x + 1/2 := by ring
        rw [e]
        exact h1
    · by_cases h2 : 0 < f (y - 1/2)
      · rcases le_total (x + 1/2) (y - 1/2) with hle | hle
        · refine ⟨1/2, ⟨by norm_num, le_rfl⟩,
            cross_integrand_pos_right hP hS hxy (by norm_num) le_rfl ?_ h2⟩
          exact pf2_pos_between hP h0 (p := cx) (q := y - 1/2) hcx.2 hle hfx h2
        · refine ⟨y - x - 1/2, ⟨by linarith, by linarith⟩,
            cross_integrand_pos_right hP hS hxy (by linarith) (by linarith) ?_ h2⟩
          have e : x + (y - x - 1/2) = y - 1/2 := by ring
          rw [e]
          exact h2
      · exfalso
        have hx0 : 0 < x := by
          by_contra hneg
          push_neg at hneg
          exact h1 (pf2_pos_between hP h0 (p := cx) (q := 1/2) hcx.2 (by linarith) hfx hp)
        have hy0 : y < 0 := by
          by_contra hneg
          push_neg at hneg
          exact h2 (pf2_pos_between hP h0 (p := -(1/2)) (q := cy) (by linarith) hcy.1 hm hfy)
        linarith
  have hpos : 0 < ∫ t in (-(1/2):ℝ)..(1/2), ((f (x + 1/2) - f (x - 1/2)) * f (y + t) -
      (f (y + 1/2) - f (y - 1/2)) * f (x + t)) := by
    have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ : ℝ => (0:ℝ))
      (g := fun t : ℝ => (f (x + 1/2) - f (x - 1/2)) * f (y + t) -
        (f (y + 1/2) - f (y - 1/2)) * f (x + t))
      (a := -(1/2)) (b := 1/2) (by norm_num) continuousOn_const hcont.continuousOn
      (fun t ht => cross_integrand_nonneg hP hxy.le ht.1.le ht.2) hex
    rw [intervalIntegral.integral_zero] at hlt
    exact hlt
  linarith

/-- The derivative of `s ↦ win f (p + s) * win f (q - s)`. -/
noncomputable def pairDeriv (f : ℝ → ℝ) (p q s : ℝ) : ℝ :=
  (f (p + s + 1/2) - f (p + s - 1/2)) * win f (q - s) +
    win f (p + s) * -(f (q - s + 1/2) - f (q - s - 1/2))

theorem hasDerivAt_pair {f : ℝ → ℝ} (hf : Continuous f) (p q s : ℝ) :
    HasDerivAt (fun s => win f (p + s) * win f (q - s)) (pairDeriv f p q s) s :=
  ((hasDerivAt_win hf (p + s)).comp_const_add p s).fun_mul
    ((hasDerivAt_win hf (q - s)).comp_const_sub q s)

theorem pairDeriv_nonneg {f : ℝ → ℝ} (hf : Continuous f) (hP : PF2 f) {p q s : ℝ}
    (hle : p + s ≤ q - s) : 0 ≤ pairDeriv f p q s := by
  have hc := cross hf hP hle
  unfold pairDeriv
  nlinarith [hc]

theorem pairDeriv_pos {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) (hP : PF2 f)
    (hS : SPF2 f) (hm : 0 < f (-(1/2))) (hp : 0 < f (1/2)) {p q s : ℝ} (hlt : p + s < q - s)
    (hx : 0 < win f (p + s)) (hy : 0 < win f (q - s)) : 0 < pairDeriv f p q s := by
  have hc := cross_strict hf h0 hP hS hm hp hlt hx hy
  unfold pairDeriv
  nlinarith [hc]

theorem monotoneOn_Icc_of_hasDerivAt {P P' : ℝ → ℝ} {c : ℝ}
    (hP : ∀ s, HasDerivAt P (P' s) s) (hnn : ∀ s ∈ Ioo (0:ℝ) c, 0 ≤ P' s) :
    MonotoneOn P (Icc 0 c) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 c)
  · exact fun s _ => (hP s).continuousAt.continuousWithinAt
  · exact fun s _ => (hP s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(hP s).deriv]
    exact hnn s hs

theorem strictMonoOn_Icc_of_hasDerivAt {P P' : ℝ → ℝ} {c : ℝ}
    (hP : ∀ s, HasDerivAt P (P' s) s) (hpos : ∀ s ∈ Ioo (0:ℝ) c, 0 < P' s) :
    StrictMonoOn P (Icc 0 c) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 c)
  · exact fun s _ => (hP s).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(hP s).deriv]
    exact hpos s hs

/-- The moving average of a continuous `PF2` function is `PF2`. -/
theorem pf2_win {f : ℝ → ℝ} (hf : Continuous f) (hP : PF2 f) : PF2 (win f) := by
  intro a b h hab hh
  have hmono : MonotoneOn (fun s => win f (a + s) * win f (b + h - s))
      (Icc 0 ((b + h - a) / 2)) :=
    monotoneOn_Icc_of_hasDerivAt (P' := pairDeriv f a (b + h))
      (fun s => hasDerivAt_pair hf a (b + h) s)
      (fun s hs => pairDeriv_nonneg hf hP (by linarith [hs.2]))
  have m0 : (0:ℝ) ∈ Icc (0:ℝ) ((b + h - a) / 2) := ⟨le_rfl, by linarith⟩
  rcases le_total h (b - a) with hle | hle
  · have mh : h ∈ Icc (0:ℝ) ((b + h - a) / 2) := ⟨hh, by linarith⟩
    have key : win f (a + 0) * win f (b + h - 0) ≤ win f (a + h) * win f (b + h - h) :=
      hmono m0 mh hh
    have e3 : b + h - h = b := by ring
    rw [add_zero, sub_zero, e3] at key
    exact key
  · have md : b - a ∈ Icc (0:ℝ) ((b + h - a) / 2) := ⟨by linarith, by linarith⟩
    have key : win f (a + 0) * win f (b + h - 0) ≤
        win f (a + (b - a)) * win f (b + h - (b - a)) := hmono m0 md (by linarith)
    have e4 : a + (b - a) = b := by ring
    have e5 : b + h - (b - a) = a + h := by ring
    rw [add_zero, sub_zero, e4, e5] at key
    calc win f a * win f (b + h) ≤ win f b * win f (a + h) := key
      _ = win f (a + h) * win f b := mul_comm _ _

/-- The moving average of a continuous, nonnegative, `PF2` and `SPF2` function which is positive
at `±1/2` is `SPF2`. -/
theorem spf2_win {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) (hP : PF2 f)
    (hS : SPF2 f) (hm : 0 < f (-(1/2))) (hp : 0 < f (1/2)) : SPF2 (win f) := by
  intro a b h hab hh hah hb
  have hw0 : ∀ x, 0 ≤ win f x := win_nonneg h0
  have hwP : PF2 (win f) := pf2_win hf hP
  by_cases ha : 0 < win f a
  · by_cases hbh : 0 < win f (b + h)
    · have hposI : ∀ v, a ≤ v → v ≤ b + h → 0 < win f v := fun v h1 h2 =>
        pf2_pos_between hwP hw0 h1 h2 ha hbh
      have hstrict : ∀ c : ℝ, c ≤ (b + h - a) / 2 →
          StrictMonoOn (fun s => win f (a + s) * win f (b + h - s)) (Icc 0 c) := fun c hc =>
        strictMonoOn_Icc_of_hasDerivAt (P' := pairDeriv f a (b + h))
          (fun s => hasDerivAt_pair hf a (b + h) s)
          (fun s hs => pairDeriv_pos hf h0 hP hS hm hp (by linarith [hs.1, hs.2, hc])
            (hposI _ (by linarith [hs.1, hs.2, hc]) (by linarith [hs.1, hs.2, hc]))
            (hposI _ (by linarith [hs.1, hs.2, hc]) (by linarith [hs.1, hs.2, hc])))
      rcases le_total h (b - a) with hle | hle
      · have m0 : (0:ℝ) ∈ Icc (0:ℝ) h := ⟨le_rfl, hh.le⟩
        have mh : h ∈ Icc (0:ℝ) h := ⟨hh.le, le_rfl⟩
        have key : win f (a + 0) * win f (b + h - 0) < win f (a + h) * win f (b + h - h) :=
          hstrict h (by linarith) m0 mh hh
        have e3 : b + h - h = b := by ring
        rw [add_zero, sub_zero, e3] at key
        exact key
      · have hd : 0 < b - a := by linarith
        have m0 : (0:ℝ) ∈ Icc (0:ℝ) (b - a) := ⟨le_rfl, hd.le⟩
        have md : b - a ∈ Icc (0:ℝ) (b - a) := ⟨hd.le, le_rfl⟩
        have key : win f (a + 0) * win f (b + h - 0) <
            win f (a + (b - a)) * win f (b + h - (b - a)) :=
          hstrict (b - a) (by linarith) m0 md hd
        have e4 : a + (b - a) = b := by ring
        have e5 : b + h - (b - a) = a + h := by ring
        rw [add_zero, sub_zero, e4, e5] at key
        calc win f a * win f (b + h) < win f b * win f (a + h) := key
          _ = win f (a + h) * win f b := mul_comm _ _
    · have hz : win f (b + h) = 0 := le_antisymm (not_lt.mp hbh) (hw0 _)
      rw [hz, mul_zero]
      exact mul_pos hah hb
  · have hz : win f a = 0 := le_antisymm (not_lt.mp ha) (hw0 _)
    rw [hz, zero_mul]
    exact mul_pos hah hb

/-- The class preserved by the moving average. -/
structure LogConcaveKernel (f : ℝ → ℝ) : Prop where
  cont : Continuous f
  nonneg : ∀ x, 0 ≤ f x
  pf2 : PF2 f
  spf2 : SPF2 f
  neg_half : 0 < f (-(1/2))
  half : 0 < f (1/2)

theorem logConcaveKernel_win {f : ℝ → ℝ} (hL : LogConcaveKernel f) :
    LogConcaveKernel (win f) where
  cont := continuous_win hL.cont
  nonneg := win_nonneg hL.nonneg
  pf2 := pf2_win hL.cont hL.pf2
  spf2 := spf2_win hL.cont hL.nonneg hL.pf2 hL.spf2 hL.neg_half hL.half
  neg_half := win_pos_of hL.cont hL.nonneg (x := -(1/2)) (c := -(1/2))
    ⟨by norm_num, by norm_num⟩ hL.neg_half
  half := win_pos_of hL.cont hL.nonneg (x := 1/2) (c := 1/2)
    ⟨by norm_num, by norm_num⟩ hL.half

/-! ## The triangle `w 2` -/

theorem w_two_of_nonneg {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : w 2 y = 1 - y := by
  have hk : w 2 y = ∫ t in (y - 1/2)..(y + 1/2), w 1 t := w_succ_primitive 1 le_rfl y
  have hI := intervalIntegrable_of_le_one (w_measurable 1) (w_nonneg 1) (w_le_one 1)
  have hA : ∫ t in (y - 1/2)..(1/2:ℝ), w 1 t = ∫ _t in (y - 1/2)..(1/2:ℝ), (1:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Eventually.of_forall (fun t ht => ?_)
    rw [uIoc_of_le (by linarith : y - 1/2 ≤ 1/2)] at ht
    have hmem : t ∈ Ioc (-1/2:ℝ) (1/2) := ⟨by linarith [ht.1], ht.2⟩
    rw [w_one_eq, if_pos hmem]
  have hB : ∫ t in (1/2:ℝ)..(y + 1/2), w 1 t = 0 := by
    apply intervalIntegral.integral_zero_ae
    refine Eventually.of_forall (fun t ht => ?_)
    rw [uIoc_of_le (by linarith : (1/2:ℝ) ≤ y + 1/2)] at ht
    have hnm : t ∉ Ioc (-1/2:ℝ) (1/2) := fun hmem => by linarith [ht.1, hmem.2]
    rw [w_one_eq, if_neg hnm]
  rw [hk, ← intervalIntegral.integral_add_adjacent_intervals (hI (y - 1/2) (1/2))
    (hI (1/2) (y + 1/2)), hA, hB, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem w_two_of_nonpos {y : ℝ} (h0 : y ≤ 0) (h1 : -1 ≤ y) : w 2 y = 1 + y := by
  have hk : w 2 y = ∫ t in (y - 1/2)..(y + 1/2), w 1 t := w_succ_primitive 1 le_rfl y
  have hI := intervalIntegrable_of_le_one (w_measurable 1) (w_nonneg 1) (w_le_one 1)
  have hA : ∫ t in (y - 1/2)..(-1/2:ℝ), w 1 t = 0 := by
    apply intervalIntegral.integral_zero_ae
    refine Eventually.of_forall (fun t ht => ?_)
    rw [uIoc_of_le (by linarith : y - 1/2 ≤ -1/2)] at ht
    have hnm : t ∉ Ioc (-1/2:ℝ) (1/2) := fun hmem => by linarith [ht.2, hmem.1]
    rw [w_one_eq, if_neg hnm]
  have hB : ∫ t in (-1/2:ℝ)..(y + 1/2), w 1 t = ∫ _t in (-1/2:ℝ)..(y + 1/2), (1:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Eventually.of_forall (fun t ht => ?_)
    rw [uIoc_of_le (by linarith : (-1/2:ℝ) ≤ y + 1/2)] at ht
    have hmem : t ∈ Ioc (-1/2:ℝ) (1/2) := ⟨ht.1, by linarith [ht.2]⟩
    rw [w_one_eq, if_pos hmem]
  rw [hk, ← intervalIntegral.integral_add_adjacent_intervals (hI (y - 1/2) (-1/2))
    (hI (-1/2) (y + 1/2)), hA, hB, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem w_two_eq_zero {y : ℝ} (hy : y ≤ -1 ∨ 1 ≤ y) : w 2 y = 0 := by
  rcases hy with hy | hy
  · rcases hy.lt_or_eq with hlt | heq
    · apply w_support 2 (by norm_num)
      rw [lt_abs]
      right
      push_cast
      linarith
    · rw [heq, w_two_of_nonpos (y := -1) (by norm_num) le_rfl]
      norm_num
  · rcases hy.lt_or_eq with hlt | heq
    · apply w_support 2 (by norm_num)
      rw [lt_abs]
      left
      push_cast
      linarith
    · rw [← heq, w_two_of_nonneg (y := 1) (by norm_num) le_rfl]
      norm_num

theorem w_two_le {y : ℝ} (h1 : -1 ≤ y) (h2 : y ≤ 1) : w 2 y ≤ 1 + y ∧ w 2 y ≤ 1 - y := by
  rcases le_total y 0 with hle | hle
  · rw [w_two_of_nonpos hle h1]
    constructor <;> linarith
  · rw [w_two_of_nonneg hle h2]
    constructor <;> linarith

theorem w_two_eq {y : ℝ} (h1 : -1 ≤ y) (h2 : y ≤ 1) : w 2 y = 1 + y ∨ w 2 y = 1 - y := by
  rcases le_total y 0 with hle | hle
  · exact Or.inl (w_two_of_nonpos hle h1)
  · exact Or.inr (w_two_of_nonneg hle h2)

/-- The triangle is strictly `PF2` inside its support. -/
theorem w_two_strict {a b h : ℝ} (hab : a < b) (hh : 0 < h) (ha : -1 < a) (hb : b + h < 1) :
    w 2 a * w 2 (b + h) < w 2 (a + h) * w 2 b := by
  have hLa := w_two_le (y := a) (by linarith) (by linarith)
  have hLc := w_two_le (y := b + h) (by linarith) (by linarith)
  have h0c : 0 ≤ w 2 (b + h) := w_nonneg 2 _
  have p1 : (0:ℝ) ≤ 1 + a := by linarith
  have p2 : (0:ℝ) ≤ 1 - a := by linarith
  have hd : 0 < h * (b - a) := mul_pos hh (by linarith)
  have hs : 0 < h * (2 + a - b) := mul_pos hh (by linarith)
  have ht : 0 < (b - a) * (2 - h) := mul_pos (by linarith) (by linarith)
  rcases w_two_eq (y := a + h) (by linarith) (by linarith) with hu | hu <;>
    rcases w_two_eq (y := b) (by linarith) (by linarith) with hv | hv
  · rw [hu, hv]
    calc w 2 a * w 2 (b + h) ≤ (1 + a) * (1 + (b + h)) := mul_le_mul hLa.1 hLc.1 h0c p1
      _ < (1 + (a + h)) * (1 + b) := by nlinarith [hd]
  · rw [hu, hv]
    calc w 2 a * w 2 (b + h) ≤ (1 + a) * (1 - (b + h)) := mul_le_mul hLa.1 hLc.2 h0c p1
      _ < (1 + (a + h)) * (1 - b) := by nlinarith [hs]
  · rw [hu, hv]
    calc w 2 a * w 2 (b + h) ≤ (1 + a) * (1 - (b + h)) := mul_le_mul hLa.1 hLc.2 h0c p1
      _ < (1 - (a + h)) * (1 + b) := by nlinarith [ht]
  · rw [hu, hv]
    calc w 2 a * w 2 (b + h) ≤ (1 - a) * (1 - (b + h)) := mul_le_mul hLa.2 hLc.2 h0c p2
      _ < (1 - (a + h)) * (1 - b) := by nlinarith [hd]

theorem pf2_w_two : PF2 (w 2) := by
  intro a b h hab hh
  by_cases ha : -1 < a
  · by_cases hb : b + h < 1
    · rcases hab.lt_or_eq with hab' | hab'
      · rcases hh.lt_or_eq with hh' | hh'
        · exact (w_two_strict hab' hh' ha hb).le
        · subst hh'
          simp
      · subst hab'
        exact le_of_eq (mul_comm _ _)
    · rw [w_two_eq_zero (Or.inr (not_lt.mp hb)), mul_zero]
      exact mul_nonneg (w_nonneg 2 _) (w_nonneg 2 _)
  · rw [w_two_eq_zero (Or.inl (not_lt.mp ha)), zero_mul]
    exact mul_nonneg (w_nonneg 2 _) (w_nonneg 2 _)

theorem spf2_w_two : SPF2 (w 2) := by
  intro a b h hab hh hah hb'
  by_cases ha : -1 < a
  · by_cases hb : b + h < 1
    · exact w_two_strict hab hh ha hb
    · rw [w_two_eq_zero (Or.inr (not_lt.mp hb)), mul_zero]
      exact mul_pos hah hb'
  · rw [w_two_eq_zero (Or.inl (not_lt.mp ha)), zero_mul]
    exact mul_pos hah hb'

theorem logConcaveKernel_w_two : LogConcaveKernel (w 2) where
  cont := w_continuous 2 le_rfl
  nonneg := w_nonneg 2
  pf2 := pf2_w_two
  spf2 := spf2_w_two
  neg_half := by
    rw [w_two_of_nonpos (y := -(1/2)) (by norm_num) (by norm_num)]
    norm_num
  half := by
    rw [w_two_of_nonneg (y := 1/2) (by norm_num) (by norm_num)]
    norm_num

/-! ## All `w M`, `M ≥ 2` -/

theorem w_succ_eq_win (M : ℕ) (hM : 1 ≤ M) : w (M + 1) = win (w M) := by
  funext y
  exact w_succ_primitive M hM y

/-- For `M ≥ 2` the cardinal B-spline `w M` is continuous, nonnegative, `PF2`, strictly `PF2`,
and positive at `±1/2`. -/
theorem lc_w : ∀ M : ℕ, 2 ≤ M → LogConcaveKernel (w M) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => exact logConcaveKernel_w_two
  | succ n hn ih =>
    rw [w_succ_eq_win n (by omega)]
    exact logConcaveKernel_win ih

/-- `w M` is positive on its open support `(-M/2, M/2)`, `M ≥ 2`. -/
theorem w_pos : ∀ M : ℕ, 2 ≤ M → ∀ y : ℝ, |y| < (M:ℝ) / 2 → 0 < w M y := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    intro y hy
    push_cast at hy
    have hy' := abs_lt.mp hy
    rcases le_total y 0 with hle | hle
    · rw [w_two_of_nonpos hle (by linarith [hy'.1])]
      linarith [hy'.1]
    · rw [w_two_of_nonneg hle (by linarith [hy'.2])]
      linarith [hy'.2]
  | succ n hn ih =>
    intro y hy
    have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    push_cast at hy
    have hy' := abs_lt.mp hy
    rw [w_succ_eq_win n (by omega)]
    rcases le_total 0 y with h0y | h0y
    · refine win_pos_of (w_continuous n hn) (w_nonneg n) (c := y - 1/2)
        ⟨le_rfl, by linarith⟩ ?_
      exact ih (y - 1/2) (abs_lt.mpr ⟨by linarith, by linarith [hy'.2]⟩)
    · refine win_pos_of (w_continuous n hn) (w_nonneg n) (c := y + 1/2)
        ⟨by linarith, le_rfl⟩ ?_
      exact ih (y + 1/2) (abs_lt.mpr ⟨by linarith [hy'.1], by linarith⟩)

/-- The derivative of `w (M+1)`, `M ≥ 2`, from the fundamental theorem of calculus. -/
theorem hasDerivAt_w_succ (M : ℕ) (hM : 2 ≤ M) (y : ℝ) :
    HasDerivAt (w (M + 1)) (w M (y + 1/2) - w M (y - 1/2)) y := by
  rw [w_succ_eq_win M (by omega)]
  exact hasDerivAt_win (w_continuous M hM) y

theorem continuous_deriv_w_three {M : ℕ} (hM : 3 ≤ M) : Continuous (deriv (w M)) := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  have he : deriv (w (k + 1)) = fun y => w k (y + 1/2) - w k (y - 1/2) := by
    funext y
    exact (hasDerivAt_w_succ k hk y).deriv
  rw [he]
  have hc := w_continuous k hk
  exact (hc.comp (continuous_id.add continuous_const)).sub
    (hc.comp (continuous_id.sub continuous_const))

/-- **Strict interior log-concavity of the cardinal B-spline.**  For `M ≥ 3` the logarithmic
derivative `w_M'/w_M` is strictly decreasing on the open support `(-M/2, M/2)`. -/
theorem w_logDeriv_strictAnti (M : ℕ) (hM : 3 ≤ M) :
    StrictAntiOn (fun y => deriv (w M) y / w M y) (Ioo (-((M:ℝ) / 2)) ((M:ℝ) / 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  have hL := lc_w k hk
  intro x hx y hy hxy
  have hpx : 0 < w (k + 1) x := w_pos (k + 1) (by omega) x (abs_lt.mpr ⟨hx.1, hx.2⟩)
  have hpy : 0 < w (k + 1) y := w_pos (k + 1) (by omega) y (abs_lt.mpr ⟨hy.1, hy.2⟩)
  have hwin := w_succ_eq_win k (by omega)
  have hc := cross_strict hL.cont hL.nonneg hL.pf2 hL.spf2 hL.neg_half hL.half hxy
    (by rw [← hwin]; exact hpx) (by rw [← hwin]; exact hpy)
  rw [← hwin] at hc
  show deriv (w (k + 1)) y / w (k + 1) y < deriv (w (k + 1)) x / w (k + 1) x
  rw [(hasDerivAt_w_succ k hk x).deriv, (hasDerivAt_w_succ k hk y).deriv,
    div_lt_div_iff₀ hpy hpx]
  exact hc

end EulerianBridge.Saddle

#print axioms EulerianBridge.Saddle.pf2_win
#print axioms EulerianBridge.Saddle.spf2_win
#print axioms EulerianBridge.Saddle.lc_w
#print axioms EulerianBridge.Saddle.w_pos
#print axioms EulerianBridge.Saddle.hasDerivAt_w_succ
#print axioms EulerianBridge.Saddle.continuous_deriv_w_three
#print axioms EulerianBridge.Saddle.w_logDeriv_strictAnti
