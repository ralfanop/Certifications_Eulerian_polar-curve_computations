import UniformLanczos.Lemma513BondGap
import UniformLanczos.Lemma513Tails
import Mathlib

/-!
# M12 Lemma 5.13: transfer the *actual* Jacobi bond gap to a growing index window

A strict compact-uniform upper bound for the normalized squared coefficients is
not enough by itself to use the local Jacobi-power tail lemma: the latter needs
every bond within distance q+1 of the central index k. This module proves
the required transfer, using the actual `betaM` and the existing certified
Theorem 5.9, on a widened compact proportional interval. The orthogonal-family
positivity premise is explicit; it is standard published input, not a new theorem.

Stacked on PR #512, without editing PR #511 or its second-tail estimates.
-/

namespace UniformLanczos.Lemma513BondWindow

open Set UniformLanczos.Theorem59 UniformLanczos.Lemma513BondGap

/-- Actual, compact-uniform Jacobi bond bound on the whole index window.

For `k/M ∈ [t₁,t₂]`, `q+1 ≤ t₁ M/2` and `L+q+1 ≤ k`, the
enlarged compact set `[t₁/2,t₂+t₁/2]` contains every `m/M`
with `k ≤ m+q+1` and `m ≤ k+q+1`. Thus Theorem 5.9 supplies
a *single* `r₀ < 1/2` for every bond required by Lemma513Tails.

The hypothesis `hpositive` is the classical positivity of the
recurrence coefficients of an orthonormal family, stated explicitly. -/
theorem actual_window_bonds (hLL : LL_13_4) {t₁ t₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : t₁ ≤ t₂) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 / 2 ∧
      ∃ L : ℕ, ∀ k M q : ℕ,
        L + q + 1 ≤ k →
        (k : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
        (q : ℝ) + 1 ≤ (t₁ / 2) * (M : ℝ) →
        (∀ m : ℕ, k ≤ m + q + 1 → m ≤ k + q + 1 → 0 ≤ betaM M m) →
        ∀ m : ℕ, k ≤ m + q + 1 → m ≤ k + q + 1 →
          |Real.sqrt (betaM M m) / (M : ℝ)| ≤ r₀ / 2 := by
  have hK0 : Icc (t₁ / 2) (t₂ + t₁ / 2) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    have hh : (0 : ℝ) < t₁ / 2 := by linarith
    exact lt_of_lt_of_le hh hx.1
  obtain ⟨r₀, hr₀, hr₀lt, L, hL⟩ :=
    actual_uniform_bond_gap hLL isCompact_Icc hK0
  refine ⟨r₀, hr₀, hr₀lt, L, ?_⟩
  intro k M q hk hkm hq hpositive m hmleft hmright
  have hM : 0 < M := by
    by_contra hh
    have hmzero : M = 0 := Nat.eq_zero_of_not_pos hh
    have hp : t₁ ≤ (k : ℝ) / (M : ℝ) := hkm.1
    rw [hmzero] at hp
    norm_num at hp
    linarith
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hJlo : t₁ * (M : ℝ) ≤ (k : ℝ) :=
    (le_div_iff₀ hMr).mp hkm.1
  have hJhi : (k : ℝ) ≤ t₂ * (M : ℝ) :=
    (div_le_iff₀ hMr).mp hkm.2
  have hIdxLo : (k : ℝ) ≤ (m : ℝ) + (q : ℝ) + 1 := by
    exact_mod_cast hmleft
  have hIdxHi : (m : ℝ) ≤ (k : ℝ) + (q : ℝ) + 1 := by
    exact_mod_cast hmright
  have hmK : (m : ℝ) / (M : ℝ) ∈ Icc (t₁ / 2) (t₂ + t₁ / 2) := by
    constructor
    · apply (le_div_iff₀ hMr).mpr
      nlinarith [hJlo, hIdxLo, hq]
    · apply (div_le_iff₀ hMr).mpr
      nlinarith [hJhi, hIdxHi, hq]
  have hmL : L ≤ m := by omega
  have hb := hL m M hmL hmK (hpositive m hmleft hmright)
  have hnonneg : 0 ≤ Real.sqrt (betaM M m) / (M : ℝ) :=
    div_nonneg (Real.sqrt_nonneg _) hMr.le
  rw [abs_of_nonneg hnonneg]
  linarith

end UniformLanczos.Lemma513BondWindow

#print axioms UniformLanczos.Lemma513BondWindow.actual_window_bonds
