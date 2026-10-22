/-
Uniform Lanczos note, Lemma 3 (the Levin–Lubinsky class 𝒬): the elementary reductions.

For the varying weight `exp(-2N Q(y)) = a g_M(a y)` with `g_M = exp(-M φ_M)` one has
`Q(y) = (M/(2N)) φ_M(a y) - log a/(2N)` and `Q'(y) = (a M/(2N)) φ_M'(a y)`.
Proved here:
* `Q_hasDerivAt`        : that derivative formula (every factor of `a`, `M`, `N`, `2`);
* `Qprime_strictMono`   : `φ_M'` strictly increasing ⇒ `Q'` strictly increasing   (Def. 1.1(ii));
* `Qprime_lipschitz`    : a Lipschitz bound `Lφ` for `φ_M'` on `[-a r, a r]` gives the bound
                          `(a² M/(2N)) Lφ` for `Q'` on `[-r, r]`;
* `holder_of_lipschitz` : Lipschitz on `[-r, r]` ⇒ Hölder of every order `α ∈ (0,1]` there
                          with constant `L (2r)^(1-α)`   (Def. 1.1(iii) and (iv));
* `interval_contains`   : `a r < 1/2` ⇒ `[-r, r] ⊆ (-1/(2a), 1/(2a))`, the support of the weight.
The bound on `φ_M''` itself (Lemma 1) and the equilibrium-support statement Def. 1.1(v)
(potential theory) are not formalised here.
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

namespace UniformLanczos

theorem Q_hasDerivAt {φ : ℝ → ℝ} {φ1 a M N y : ℝ} (hφ : HasDerivAt φ φ1 (a * y)) :
    HasDerivAt (fun y => M / (2 * N) * φ (a * y) - Real.log a / (2 * N))
      (a * M / (2 * N) * φ1) y := by
  have h1 : HasDerivAt (fun y => a * y) a y := by
    simpa using (hasDerivAt_id y).const_mul a
  have h2 := ((hφ.comp y h1).const_mul (M / (2 * N))).sub_const (Real.log a / (2 * N))
  convert h2 using 1
  · rfl
  · ring

theorem Qprime_strictMono {φ1 : ℝ → ℝ} {a M N : ℝ} (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    {S : Set ℝ} (hφ : StrictMonoOn φ1 ((fun y => a * y) '' S)) :
    StrictMonoOn (fun y => a * M / (2 * N) * φ1 (a * y)) S := by
  intro x hx y hy hxy
  have hc : 0 < a * M / (2 * N) := by positivity
  have : φ1 (a * x) < φ1 (a * y) :=
    hφ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (mul_lt_mul_of_pos_left hxy ha)
  exact mul_lt_mul_of_pos_left this hc

theorem Qprime_lipschitz {φ1 : ℝ → ℝ} {a M N r Lφ : ℝ} (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hφ : ∀ u ∈ Icc (-(a * r)) (a * r), ∀ w ∈ Icc (-(a * r)) (a * r),
      |φ1 u - φ1 w| ≤ Lφ * |u - w|) :
    ∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
      |a * M / (2 * N) * φ1 (a * x) - a * M / (2 * N) * φ1 (a * y)|
        ≤ a ^ 2 * M / (2 * N) * Lφ * |x - y| := by
  intro x hx y hy
  have hmem : ∀ z ∈ Icc (-r) r, a * z ∈ Icc (-(a * r)) (a * r) := fun z hz =>
    ⟨by nlinarith [hz.1], by nlinarith [hz.2]⟩
  have hc : 0 ≤ a * M / (2 * N) := by positivity
  have := hφ _ (hmem x hx) _ (hmem y hy)
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  have e : |a * x - a * y| = a * |x - y| := by
    rw [← mul_sub, abs_mul, abs_of_pos ha]
  rw [e] at this
  calc a * M / (2 * N) * |φ1 (a * x) - φ1 (a * y)|
      ≤ a * M / (2 * N) * (Lφ * (a * |x - y|)) := mul_le_mul_of_nonneg_left this hc
    _ = a ^ 2 * M / (2 * N) * Lφ * |x - y| := by ring

theorem holder_of_lipschitz {f : ℝ → ℝ} {L r α : ℝ} (hL : 0 ≤ L) (hα1 : α ≤ 1)
    (h : ∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r, |f x - f y| ≤ L * |x - y|) :
    ∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
      |f x - f y| ≤ L * (2 * r) ^ (1 - α) * |x - y| ^ α := by
  intro x hx y hy
  have hd0 : 0 ≤ |x - y| := abs_nonneg _
  have hd : |x - y| ≤ 2 * r := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hsplit : |x - y| = |x - y| ^ (1 - α) * |x - y| ^ α := by
    rw [← Real.rpow_add' hd0 (by norm_num : (1 - α) + α ≠ 0)]
    simp
  have hpow : |x - y| ^ (1 - α) ≤ (2 * r) ^ (1 - α) :=
    Real.rpow_le_rpow hd0 hd (by linarith)
  calc |f x - f y| ≤ L * |x - y| := h x hx y hy
    _ = L * (|x - y| ^ (1 - α) * |x - y| ^ α) := by rw [← hsplit]
    _ ≤ L * ((2 * r) ^ (1 - α) * |x - y| ^ α) := by
        gcongr
    _ = L * (2 * r) ^ (1 - α) * |x - y| ^ α := by ring

theorem interval_contains {a r : ℝ} (ha : 0 < a) (har : a * r < 1 / 2) :
    Icc (-r) r ⊆ Ioo (-(1 / (2 * a))) (1 / (2 * a)) := by
  intro y hy
  have hr : r < 1 / (2 * a) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

end UniformLanczos
