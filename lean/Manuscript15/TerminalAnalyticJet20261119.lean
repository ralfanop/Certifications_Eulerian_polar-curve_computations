import Manuscript15.TerminalAnalyticGraph20261119
import Manuscript15.InternalHyperlinks20261115
import Mathlib.Analysis.Analytic.Order

/-!
M15 §6.2: exact analytic order and analytic remainder of the actual
terminal graph. Connects the manuscript's explicit leading coefficient
to the independent-variable graph, rather than a formal scalar only.
-/

open Filter Topology
noncomputable section
namespace Manuscript15.TerminalJet

open Manuscript15 TerminalAnalytic InternalHyperlinks20261115

/-- Exact vanishing order of the actual transverse coordinate. -/
theorem Y_order (a : ℝ) (ha : a ≠ 0) (M : ℕ) :
    analyticOrderAt (YConv a M) (2 * Real.pi) = (↑(2 * M) : ℕ∞) := by
  have hk := kernel_analytic_nonzero (2 * Real.pi) (by positivity)
  have hkd : deriv eulerianKernel (2 * Real.pi) ≠ 0 := by
    rw [eulerian_kernel_hasDerivAt_two_pi.deriv]
    exact div_ne_zero (by norm_num) (by positivity)
  have hko := hk.analyticOrderAt_eq_one_of_zero_deriv_ne_zero eulerianKernel_two_pi_zero hkd
  let p : ℝ → ℝ := fun t => a * t ^ 2 / 2
  have hp : AnalyticAt ℝ p (2 * Real.pi) := by
    have hi : AnalyticAt ℝ (fun t : ℝ => t) (2 * Real.pi) := analyticAt_id
    have hc : AnalyticAt ℝ (fun _ : ℝ => a) (2 * Real.pi) := analyticAt_const
    exact (hc.mul (hi.pow 2)).div_const
  have hp0 : p (2 * Real.pi) ≠ 0 := by
    dsimp [p]
    exact div_ne_zero (mul_ne_zero ha (pow_ne_zero _ (by positivity))) (by norm_num)
  have hpo := hp.analyticOrderAt_eq_zero.mpr hp0
  change analyticOrderAt (p * eulerianKernel ^ (2 * M)) (2 * Real.pi) = _
  rw [analyticOrderAt_mul hp (hk.pow _), hpo, analyticOrderAt_pow hk, hko]
  simp

/-- The coefficient from the actual contact limit matches the manuscript
normalization at every positive convolution order, including arbitrary scale. -/
theorem leading_coefficient (a : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    (a * (2 * Real.pi) ^ 2 / 2 * (-1 / (2 * Real.pi)) ^ (2 * M)) /
      a ^ (2 * M) = a * terminalCoefficient M / a ^ (2 * M) := by
  have hp : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hs : (-1 / (2 * Real.pi)) ^ 2 = 1 / (4 * Real.pi ^ 2) := by
    field_simp [Real.pi_ne_zero] <;> ring
  have hm : M = (M - 1) + 1 := by omega
  have hpow : (1 / (4 * Real.pi ^ 2)) ^ M =
      1 / ((4 * Real.pi ^ 2) ^ (M - 1) * (4 * Real.pi ^ 2)) := by
    conv_lhs => rw [hm, pow_succ]
    rw [div_pow, one_pow, div_mul_div_comm] <;> simp
  rw [pow_mul, hs, hpow]
  unfold terminalCoefficient
  congr 1
  field_simp [hp, pow_ne_zero _ hp] <;> ring

/-- The actual analytic graph has precisely order 2M. Its lower Taylor
jets vanish, and its 2M-th derivative does not vanish. -/
theorem graph_order (a : ℝ) (ha : a ≠ 0) (M : ℕ) (hM : 2 ≤ M)
    {G : ℝ → ℝ}
    (hG : ∀ᶠ t in 𝓝 (2 * Real.pi), G (XConv a M t) = YConv a M t) :
    analyticOrderAt G (XConv a M (2 * Real.pi)) = (↑(2 * M) : ℕ∞) := by
  have hd : deriv (XConv a M) (2 * Real.pi) ≠ 0 := by
    rw [convolution_endpoint_X_deriv a M hM]
    exact ha
  have hcomp : analyticOrderAt (G ∘ XConv a M) (2 * Real.pi) =
      analyticOrderAt G (XConv a M (2 * Real.pi)) :=
    analyticOrderAt_comp_of_deriv_ne_zero (X_analytic a M) hd
  rw [← hcomp, analyticOrderAt_congr hG, Y_order a ha M]

/-- Full analytic leading-term decomposition in the independent horizontal
variable, with a genuine analytic remainder of order at least 2M+1.
The actual graph agrees with the parametrized curve locally. -/
theorem exists_terminal_analytic_remainder (a : ℝ) (ha : a ≠ 0)
    (M : ℕ) (hM : 2 ≤ M) :
    ∃ G R : ℝ → ℝ,
      AnalyticAt ℝ G (XConv a M (2 * Real.pi)) ∧
      AnalyticAt ℝ R (XConv a M (2 * Real.pi)) ∧
      (∀ᶠ t in 𝓝 (2 * Real.pi), G (XConv a M t) = YConv a M t) ∧
      analyticOrderAt G (XConv a M (2 * Real.pi)) = (↑(2 * M) : ℕ∞) ∧
      (∀ᶠ x in 𝓝 (XConv a M (2 * Real.pi)),
        G x = (x - XConv a M (2 * Real.pi)) ^ (2 * M) *
          (a * terminalCoefficient M / a ^ (2 * M) +
            (x - XConv a M (2 * Real.pi)) * R x)) := by
  obtain ⟨G, hGa, hG0, hleft, hlim⟩ := exists_analytic_terminal_graph a ha M hM
  let x₀ := XConv a M (2 * Real.pi)
  let c := a * terminalCoefficient M / a ^ (2 * M)
  have ho : analyticOrderAt G x₀ = (↑(2 * M) : ℕ∞) := graph_order a ha M hM hleft
  obtain ⟨H, hHa, hHnz, hfac⟩ := hGa.analyticOrderAt_eq_natCast.mp ho
  have hHlim : Tendsto (fun x : ℝ => G x / (x - x₀) ^ (2 * M))
      (𝓝[≠] x₀) (𝓝 (H x₀)) := by
    apply (hHa.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] x₀ ≤ 𝓝 x₀)).congr'
    have hn : ∀ᶠ x : ℝ in 𝓝[≠] x₀, x ≠ x₀ := self_mem_nhdsWithin
    filter_upwards [hn, hfac.filter_mono nhdsWithin_le_nhds] with x hx hfx
    rw [hfx, smul_eq_mul]
    field_simp [pow_ne_zero _ (sub_ne_zero.mpr hx)]
  have hclim : Tendsto (fun x : ℝ => G x / (x - x₀) ^ (2 * M))
      (𝓝[≠] x₀) (𝓝 c) := by
    simpa only [x₀, c, ← leading_coefficient a M (by omega)] using hlim
  have hval : H x₀ = c := tendsto_nhds_unique hHlim hclim
  have hsub : AnalyticAt ℝ (fun x : ℝ => H x - c) x₀ :=
    hHa.sub analyticAt_const
  have hle : (↑(1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun x : ℝ => H x - c) x₀ := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hsub).2
    intro i hi
    have he : i = 0 := by omega
    subst i
    simp [hval]
  obtain ⟨R, hRa, hR⟩ := (natCast_le_analyticOrderAt hsub).mp hle
  refine ⟨G, R, hGa, hRa, hleft, ho, ?_⟩
  filter_upwards [hfac, hR] with x hfx hrx
  have hsplit : H x = c + (x - x₀) * R x := by
    simp only [pow_one, smul_eq_mul] at hrx
    linarith
  change G x = (x - x₀) ^ (2 * M) * (c + (x - x₀) * R x)
  rw [hfx, smul_eq_mul, hsplit]

/-- Actual Taylor-jet classification (not simply a polynomial calculation). -/
theorem graph_jets (a : ℝ) (ha : a ≠ 0) (M : ℕ) (hM : 2 ≤ M)
    {G : ℝ → ℝ}
    (hGa : AnalyticAt ℝ G (XConv a M (2 * Real.pi)))
    (hG : ∀ᶠ t in 𝓝 (2 * Real.pi), G (XConv a M t) = YConv a M t) :
    (∀ k < 2 * M, iteratedDeriv k G (XConv a M (2 * Real.pi)) = 0) ∧
      iteratedDeriv (2 * M) G (XConv a M (2 * Real.pi)) ≠ 0 :=
  (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hGa).mp (graph_order a ha M hM hG)

end Manuscript15.TerminalJet

#print axioms Manuscript15.TerminalJet.Y_order
#print axioms Manuscript15.TerminalJet.leading_coefficient
#print axioms Manuscript15.TerminalJet.graph_order
#print axioms Manuscript15.TerminalJet.exists_terminal_analytic_remainder
#print axioms Manuscript15.TerminalJet.graph_jets
