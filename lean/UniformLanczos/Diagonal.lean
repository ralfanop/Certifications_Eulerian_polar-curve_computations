/-
Uniform Lanczos note, proof of the Theorem: the diagonal (contradiction) argument that turns
convergence along every admissible sequence `n ↦ (n, m n)` into convergence that is uniform
over all pairs `(N, M)` with `N ≥ L` and `N/M ∈ K`.

`E N M` stands for `β_N^{[M]}/M² - F(N/M)`; `Good N M` for `M ≥ 1 ∧ N/M ∈ K`;
`Good' N M` for `M ≥ 1 ∧ N/M ∈ K'` with `K ⊆ K'`.  The hypothesis `hseq` is what
Levin–Lubinsky's Theorem 13.4, applied to one varying-weight sequence, provides
(together with Lemmas 1–3); it is a hypothesis here, not proved.

`fill_ratio` proves that the filling step is always possible: for `0 < t₁ < t₂` and all
large `n` there is `M ≥ 1` with `t₁ ≤ n/M ≤ t₂`.
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace UniformLanczos

theorem uniform_of_sequential (E : ℕ → ℕ → ℝ) (Good Good' : ℕ → ℕ → Prop)
    (hsub : ∀ N M, Good N M → Good' N M)
    (hfill : ∀ᶠ n in atTop, ∃ M, Good' n M)
    (hseq : ∀ m : ℕ → ℕ, (∀ᶠ n in atTop, Good' n (m n)) →
      Tendsto (fun n => E n (m n)) atTop (𝓝 0)) :
    ∀ ε > 0, ∃ L : ℕ, ∀ N M, L ≤ N → Good N M → |E N M| < ε := by
  classical
  intro ε hε
  by_contra hcon
  push Not at hcon
  -- bad degrees: some admissible `M` with error at least `ε`
  let bad : ℕ → Prop := fun n => ∃ M, Good n M ∧ ε ≤ |E n M|
  have hbad : ∃ᶠ n in atTop, bad n := by
    rw [Filter.frequently_atTop]
    intro L
    obtain ⟨N, M, hLN, hG, hE⟩ := hcon L
    exact ⟨N, hLN, M, hG, hE⟩
  -- the diagonal sequence: a bad `M` where available, a filler otherwise
  let m : ℕ → ℕ := fun n =>
    if h : bad n then Classical.choose h
    else if h' : ∃ M, Good' n M then Classical.choose h' else 0
  have hm : ∀ᶠ n in atTop, Good' n (m n) := by
    filter_upwards [hfill] with n hn
    by_cases h : bad n
    · simp only [m, h, dite_true]
      exact hsub _ _ (Classical.choose_spec h).1
    · simp only [m, h, hn, dite_false, dite_true]
      exact Classical.choose_spec hn
  have hT := hseq m hm
  have hsmall : ∀ᶠ n in atTop, |E n (m n)| < ε := by
    have := (hT.abs).eventually (gt_mem_nhds (by simpa using hε))
    simpa using this
  obtain ⟨n, hb, hs⟩ := (hbad.and_eventually hsmall).exists
  have : ε ≤ |E n (m n)| := by
    simp only [m, hb, dite_true]
    exact (Classical.choose_spec hb).2
  linarith

/-- Filling: for `0 < t₁ < t₂`, every large `n` admits `M ≥ 1` with `t₁ ≤ n/M ≤ t₂`. -/
theorem fill_ratio {t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h₁₂ : t₁ < t₂) :
    ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, 1 ≤ M ∧ t₁ ≤ (n : ℝ) / M ∧ (n : ℝ) / M ≤ t₂ := by
  have h₂ : 0 < t₂ := h₁.trans h₁₂
  have hgap : 0 < 1 / t₁ - 1 / t₂ := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt h₁ h₁₂
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / (1 / t₁ - 1 / t₂))
  filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hnn₀ : (n₀ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hnpos : (0 : ℝ) < n := by linarith
  set M := ⌈(n : ℝ) / t₂⌉₊ with hM
  have hMge : (n : ℝ) / t₂ ≤ M := Nat.le_ceil _
  have hMlt : (M : ℝ) < (n : ℝ) / t₂ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMge
  refine ⟨M, ?_, ?_, ?_⟩
  · exact_mod_cast hMpos
  · -- t₁ ≤ n / M  ⇔  t₁ M ≤ n ; use M < n/t₂ + 1 ≤ n/t₁
    rw [le_div_iff₀ hMpos]
    have key : (n : ℝ) / t₂ + 1 ≤ (n : ℝ) / t₁ := by
      have : 1 ≤ (n : ℝ) * (1 / t₁ - 1 / t₂) := by
        have h1 : 1 / (1 / t₁ - 1 / t₂) < n := lt_of_lt_of_le hn₀ hnn₀
        rw [div_lt_iff₀ hgap] at h1; linarith
      have e1 : (n : ℝ) / t₁ = n * (1 / t₁) := by ring
      have e2 : (n : ℝ) / t₂ = n * (1 / t₂) := by ring
      rw [e1, e2]; nlinarith
    have : (M : ℝ) ≤ (n : ℝ) / t₁ := by linarith
    calc t₁ * M ≤ t₁ * ((n : ℝ) / t₁) := by gcongr
      _ = n := by field_simp
  · rw [div_le_iff₀ hMpos]
    have := (div_le_iff₀ h₂).mp hMge
    linarith [mul_comm t₂ (M : ℝ)]

end UniformLanczos
