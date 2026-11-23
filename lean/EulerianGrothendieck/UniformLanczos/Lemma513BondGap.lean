import UniformLanczos.Lemma513
import Mathlib

/-!
# Manuscript 12, Lemma 5.13 — actual compact-window Jacobi bond gap

Theorem 5.9 already gives a uniform strict gap for the *actual* moment coefficient
`betaM M j / M²` on each compact K ⊂ (0,∞), conditional only on the *published*
Levin–Lubinsky theorem `LL_13_4`.

This file turns that gap into precisely the bond smallness `2a_j ≤ r₀ < 1/2`,
where `a_j = sqrt(betaM M j)/M`, required by the local Jacobi-power argument in
`Lemma513Tails.tail_bound`. Positivity of the actual recurrence coefficient is
an explicit premise, as supplied by the classical orthonormal-polynomial theory.
No bound on `a_j` is assumed. The published Levin–Lubinsky input is not reproved.
-/

namespace UniformLanczos.Lemma513BondGap

open Set UniformLanczos.Theorem59 UniformLanczos.Lemma513

/-- Exact elementary conversion of a squared gap into a Jacobi-bond gap.
For 0 < δ ≤ 1/16, β ≥ 0, M > 0:
β/M² ≤ 1/16−δ ⇒ 2√β/M ≤ 1/2−2δ. -/
theorem squared_gap_to_bond {β M δ : ℝ}
    (hβ : 0 ≤ β) (hM : 0 < M) (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16)
    (hgap : β / M ^ 2 ≤ 1 / 16 - δ) :
    2 * (Real.sqrt β / M) ≤ 1 / 2 - 2 * δ := by
  have ha0 : 0 ≤ Real.sqrt β / M :=
    div_nonneg (Real.sqrt_nonneg β) hM.le
  have ha_sq : (Real.sqrt β / M) ^ 2 = β / M ^ 2 := by
    rw [div_pow, Real.sq_sqrt hβ]
  have htarget0 : 0 ≤ (1 / 4 : ℝ) - δ := by linarith
  have hsq : (Real.sqrt β / M) ^ 2 ≤ ((1 / 4 : ℝ) - δ) ^ 2 := by
    rw [ha_sq]
    nlinarith [sq_nonneg δ]
  nlinarith

/-- The compact-window bond gap used in Lemma 5.13, for the actual `betaM`.
The only external analytic input is the published `LL_13_4` already used in
Theorem 5.9. Positivity of `betaM` is stated explicitly, not hidden. -/
theorem actual_uniform_bond_gap (hLL : LL_13_4) {K : Set ℝ}
    (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 / 2 ∧
      ∃ L : ℕ, ∀ j M : ℕ, L ≤ j →
        (j : ℝ) / M ∈ K → 0 ≤ betaM M j →
        2 * (Real.sqrt (betaM M j) / (M : ℝ)) ≤ r₀ := by
  obtain ⟨η, hη, L, hL⟩ := uniform_interior_gap hLL hK hK0
  let δ : ℝ := min η (1 / 16)
  have hδ : 0 < δ := lt_min hη (by norm_num)
  have hδ16 : δ ≤ 1 / 16 := min_le_right _ _
  have hδη : δ ≤ η := min_le_left _ _
  let r₀ : ℝ := 1 / 2 - 2 * δ
  have hrpos : 0 < r₀ := by dsimp [r₀]; linarith
  have hrlt : r₀ < 1 / 2 := by dsimp [r₀]; linarith
  refine ⟨r₀, hrpos, hrlt, L, ?_⟩
  intro j M hj hmem hβ
  have hMnat : 0 < M := by
    by_contra h
    have hMzero : M = 0 := Nat.eq_zero_of_not_pos h
    subst M
    have hp : (0 : ℝ) < (j : ℝ) / (0 : ℝ) := hK0 hmem
    norm_num at hp
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hraw := hL j M hj hmem
  have hgap : betaM M j / (M : ℝ) ^ 2 ≤ 1 / 16 - δ := by linarith
  exact squared_gap_to_bond hβ hMreal hδ hδ16 hgap

end UniformLanczos.Lemma513BondGap

#print axioms UniformLanczos.Lemma513BondGap.squared_gap_to_bond
#print axioms UniformLanczos.Lemma513BondGap.actual_uniform_bond_gap
