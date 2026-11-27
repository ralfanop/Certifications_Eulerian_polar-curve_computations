import UniformLanczos.Lemma513ActualTail
import UniformLanczos.Lemma513Tails
import Mathlib

/-!
# Manuscript 12 — Lemma 5.13: strict exponential first-tail bound for actual β[M]

The already audited `first_tail_actual_jacobi` proves the geometrical
`(r₀/s)^(2*q)` bound for the *actual* Jacobi coefficients
`a_m = sqrt(betaM M m)/M`. This module chooses
`q = floor(delta * M)` and composes with the independently audited
`Lemma513Tails.geometric_le_exp`. It does not assume exponential
localization as an input.

The index-window constraints, orthonormal-polynomial recurrence, and positivity
of recurrence coefficients remain explicit; a subsequent theorem will establish
uniform eventual validity of the index constraints and combine the second
(weighted, two-sided) tail. No classical analysis theorem is being reproved.
-/

namespace UniformLanczos.Lemma513Exponential

open Set MeasureTheory UniformLanczos.Theorem59

/-- The actual first-tail bound, with a genuine *positive exponential rate*
`c = -δ log(r₀/s)`, for `q=floor(δ M)`.

The only additional analytic premise is the published Levin–Lubinsky theorem
`LL_13_4` already used by the original Theorem 5.9. The lower bounds on
`M` and the enlarged-window inclusion are elementary and explicit. -/
theorem first_tail_actual_exponential (hLL : LL_13_4) {t₁ t₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : t₁ ≤ t₂) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 / 2 ∧
      ∃ L : ℕ, ∀ k M : ℕ, (k : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
        ∀ δ s : ℝ, 0 < δ → r₀ < s →
          2 ≤ δ * (M : ℝ) →
          L + ⌊δ * (M : ℝ)⌋₊ + 1 ≤ k →
          ((⌊δ * (M : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (t₁ / 2) * (M : ℝ) →
          (∀ m : ℕ, k ≤ m + ⌊δ * (M : ℝ)⌋₊ + 1 →
            m ≤ k + ⌊δ * (M : ℝ)⌋₊ + 1 → 0 ≤ betaM M m) →
          ∀ (μ : Measure ℝ) (p : ℕ → ℝ → ℝ),
            (∀ l m, ∫ x, p l x * p m x ∂μ = if l = m then 1 else 0) →
            (∀ l m, Integrable (fun x => p l x * p m x) μ) →
            (∀ l x, x * p l x =
              (Real.sqrt (betaM M (l + 1)) / (M : ℝ)) * p (l + 1) x +
                (if l = 0 then 0 else
                  (Real.sqrt (betaM M l) / (M : ℝ)) * p (l - 1) x)) →
            ∫ x in {x : ℝ | s ≤ |x|}, p k x ^ 2 ∂μ ≤
              Real.exp (-(-δ * Real.log (r₀ / s)) * (M : ℝ)) := by
  obtain ⟨r₀, hr₀, hr₀lt, L, hFirst⟩ :=
    UniformLanczos.Lemma513ActualTail.first_tail_actual_jacobi hLL ht₁ ht₂
  refine ⟨r₀, hr₀, hr₀lt, L, ?_⟩
  intro k M hkM δ s hδ hrs hM hindex hwindow hpositive μ p horth hint hrec
  have hs : 0 < s := lt_trans hr₀ hrs
  have hρ0 : 0 < r₀ / s := div_pos hr₀ hs
  have hρ1 : r₀ / s < 1 := (div_lt_one hs).2 hrs
  let q : ℕ := ⌊δ * (M : ℝ)⌋₊
  have htail : ∫ x in {x : ℝ | s ≤ |x|}, p k x ^ 2 ∂μ
      ≤ (r₀ / s) ^ (2 * q) :=
    hFirst k M q hindex hkM hwindow hpositive μ p horth hint hrec s hs
  have hexp := (UniformLanczos.Lemma513Tails.geometric_le_exp hρ0 hρ1 hδ hM).2
  exact htail.trans hexp

end UniformLanczos.Lemma513Exponential

#print axioms UniformLanczos.Lemma513Exponential.first_tail_actual_exponential
