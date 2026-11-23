import UniformLanczos.Lemma513Exponential
import Mathlib

/-!
# M12 Lemma 5.13: uniform first exponential tail for the actual Lanczos β[M]

The mathematically new step, beyond the green PRs #512 and #515 and the
precise exponential corollary of #518, is that the growing-window
inequalities hold *automatically* for every sufficiently large integer M
and every k/M in the prescribed proportional interval.

The classical orthonormal family and its three-term recurrence are
external published inputs, stated explicitly. Nothing resembling the
first tail bound is assumed. No independent proof of a classical theorem
is requested.
-/

namespace UniformLanczos.Lemma513UniformFirst

open Set MeasureTheory UniformLanczos.Theorem59 UniformLanczos.Lemma513Exponential

/-- For q = floor(t₁ M/8), the full local bond window is eventually inside
an enlarged positive proportional compact interval. The constants depend
only on t₁ and the pre-existing uniform compact threshold L. -/
theorem floor_window_eventually {t₁ : ℝ} (ht₁ : 0 < t₁) (L : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ k : ℕ, t₁ ≤ (k : ℝ) / (M : ℝ) →
      L + ⌊(t₁ / 8) * (M : ℝ)⌋₊ + 1 ≤ k ∧
      ((⌊(t₁ / 8) * (M : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (t₁ / 2) * (M : ℝ) ∧
      2 ≤ (t₁ / 8) * (M : ℝ) := by
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (((16 : ℝ) + 8 * ((L : ℝ) + 1)) / t₁)
  refine ⟨M₀, ?_⟩
  intro M hM k hk
  have hMc : (M₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMlower : ((16 : ℝ) + 8 * ((L : ℝ) + 1)) / t₁ < (M : ℝ) :=
    lt_of_lt_of_le hM₀ hMc
  have hbound : (16 : ℝ) + 8 * ((L : ℝ) + 1) < t₁ * (M : ℝ) :=
    (div_lt_iff₀ ht₁).mp hMlower
  have hMpos : 0 < (M : ℝ) := by
    by_contra hh
    have hn : (M : ℝ) ≤ 0 := le_of_not_gt hh
    have hc : t₁ * (M : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht₁.le hn
    nlinarith
  have hklo : t₁ * (M : ℝ) ≤ (k : ℝ) := (le_div_iff₀ hMpos).mp hk
  let q : ℕ := ⌊(t₁ / 8) * (M : ℝ)⌋₊
  have hδ0 : 0 ≤ (t₁ / 8) * (M : ℝ) := by positivity
  have hqle : (q : ℝ) ≤ (t₁ / 8) * (M : ℝ) := by
    dsimp [q]
    exact Nat.floor_le hδ0
  have hindex : L + q + 1 ≤ k := by
    have hr : (L : ℝ) + (q : ℝ) + 1 ≤ (k : ℝ) := by
      nlinarith [hbound, hqle, hklo]
    exact_mod_cast hr
  have hwindow : (q : ℝ) + 1 ≤ (t₁ / 2) * (M : ℝ) := by
    nlinarith [hbound, hqle]
  have hlarge : 2 ≤ (t₁ / 8) * (M : ℝ) := by
    nlinarith [hbound]
  exact ⟨hindex, hwindow, hlarge⟩

/-- **Uniform first bound (158), for actual β[M].**
For all sufficiently large M and all k/M in [t₁,t₂], one choice
of s∈(0,1/2) and c>0 bounds the actual p_k tail by exp(-cM).

Only the published Levin–Lubinsky input and the classical orthonormality/
three-term recurrence are hypotheses. The global coefficient nonnegativity
is a consequence of those same standard polynomials; it is exposed
rather than assumed to be a mysterious new analytic property. -/
theorem first_tail_uniform_for_actual_beta (hLL : LL_13_4) {t₁ t₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : t₁ ≤ t₂) :
    ∃ s c : ℝ, 0 < s ∧ s < 1 / 2 ∧ 0 < c ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        ∀ k : ℕ, (k : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
          (∀ m : ℕ, 0 ≤ betaM M m) →
          ∀ (μ : Measure ℝ) (p : ℕ → ℝ → ℝ),
            (∀ l m, ∫ x, p l x * p m x ∂μ = if l = m then 1 else 0) →
            (∀ l m, Integrable (fun x => p l x * p m x) μ) →
            (∀ l x, x * p l x =
              (Real.sqrt (betaM M (l + 1)) / (M : ℝ)) * p (l + 1) x +
                (if l = 0 then 0 else
                  (Real.sqrt (betaM M l) / (M : ℝ)) * p (l - 1) x)) →
            ∫ x in {x : ℝ | s ≤ |x|}, p k x ^ 2 ∂μ ≤
              Real.exp (-c * (M : ℝ)) := by
  obtain ⟨r₀, hr₀, hr₀lt, L, hExp⟩ :=
    first_tail_actual_exponential hLL ht₁ ht₂
  obtain ⟨M₀, hWindow⟩ := floor_window_eventually ht₁ L
  let δ : ℝ := t₁ / 8
  let s : ℝ := (r₀ + 1 / 2) / 2
  let c : ℝ := -δ * Real.log (r₀ / s)
  have hrs : r₀ < s := by dsimp [s]; linarith
  have hs : 0 < s := lt_trans hr₀ hrs
  have hss : s < 1 / 2 := by dsimp [s]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρpos : 0 < r₀ / s := div_pos hr₀ hs
  have hρlt : r₀ / s < 1 := (div_lt_one hs).mpr hrs
  have hlog : Real.log (r₀ / s) < 0 := Real.log_neg hρpos hρlt
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos_of_neg_of_neg (by linarith) hlog
  refine ⟨s, c, hs, hss, hc, M₀, ?_⟩
  intro M hM k hk hpos μ p horth hint hrec
  obtain ⟨hindex, hwindow, hlarge⟩ := hWindow M hM k hk.1
  have htail := hExp k M hk δ s hδ hrs hlarge hindex hwindow
    (fun m _ _ => hpos m) μ p horth hint hrec
  simpa only [c, δ] using htail

end UniformLanczos.Lemma513UniformFirst

#print axioms UniformLanczos.Lemma513UniformFirst.floor_window_eventually
#print axioms UniformLanczos.Lemma513UniformFirst.first_tail_uniform_for_actual_beta
