import UniformLanczos.Lemma513BondWindow
import UniformLanczos.Lemma513Tails
import Mathlib

/-!
# M12 Lemma 5.13 (158), first tail: the ACTUAL Lanczos/Jacobi coefficients

This statement composes the actual compact-window Jacobi bond bound obtained from
Theorem 5.9 with the already audited `Lemma513Tails.tail_bound`. The coefficients
are not abstract: they are exactly `sqrt (Theorem59.betaM M m) / M` from the
cardinal B-spline moments. The published existence, orthonormality and recurrence
of the corresponding orthogonal polynomials are explicit premises. No copy of
the tail estimate is assumed, and no new axiom is introduced.

This supplies a concrete original bridge in the proof of (158); selection
`q=floor(delta*M)`, positivity on the growing window, and the simultaneous
two-sided exponential constants remain separate downstream obligations.
-/

namespace UniformLanczos.Lemma513ActualTail

open Set MeasureTheory UniformLanczos.Theorem59 UniformLanczos.Lemma513BondWindow

/-- Original first-tail implication of (158) with the **actual** betaM:
compact convergence + local Jacobi recurrence => quantitative exponential-ready
moment bound on the whole index window. -/
theorem first_tail_actual_jacobi (hLL : LL_13_4) {t₁ t₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : t₁ ≤ t₂) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 / 2 ∧
      ∃ L : ℕ, ∀ k M q : ℕ,
        L + q + 1 ≤ k →
        (k : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
        (q : ℝ) + 1 ≤ (t₁ / 2) * (M : ℝ) →
        (∀ m : ℕ, k ≤ m + q + 1 → m ≤ k + q + 1 → 0 ≤ betaM M m) →
        ∀ (μ : Measure ℝ) (p : ℕ → ℝ → ℝ),
          (∀ l m, ∫ x, p l x * p m x ∂μ = if l = m then 1 else 0) →
          (∀ l m, Integrable (fun x => p l x * p m x) μ) →
          (∀ l x, x * p l x =
            (Real.sqrt (betaM M (l + 1)) / (M : ℝ)) * p (l + 1) x +
              (if l = 0 then 0 else
                (Real.sqrt (betaM M l) / (M : ℝ)) * p (l - 1) x)) →
          ∀ s : ℝ, 0 < s →
            ∫ x in {x : ℝ | s ≤ |x|}, p k x ^ 2 ∂μ ≤ (r₀ / s) ^ (2 * q) := by
  obtain ⟨r₀, hr₀, hr₀lt, L, hL⟩ := actual_window_bonds hLL ht₁ ht₂
  refine ⟨r₀, hr₀, hr₀lt, L, ?_⟩
  intro k M q hk hkm hq hβ μ p horth hint hrec s hs
  have hb : ∀ m, k ≤ m + q + 1 → m ≤ k + q + 1 →
      |Real.sqrt (betaM M m) / (M : ℝ)| ≤ r₀ / 2 :=
    hL k M q hk hkm hq hβ
  exact UniformLanczos.Lemma513Tails.tail_bound
    μ p (fun m => Real.sqrt (betaM M m) / (M : ℝ))
    horth hint hrec k q hs hb

end UniformLanczos.Lemma513ActualTail

#print axioms UniformLanczos.Lemma513ActualTail.first_tail_actual_jacobi
