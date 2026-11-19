import Manuscript15.TerminalContactLimit20261117
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
M15 §6.2: genuine local analytic inverse and graph at the terminal point.
This is an all-order contact limit in the independent X variable, not just
a limit along the original parametrization. The explicit higher
Lagrange–Bürmann coefficient formula remains a separate obligation.
-/

open Filter Topology
noncomputable section
namespace Manuscript15.TerminalAnalytic

open Manuscript15

/-- The actual Eulerian kernel is analytic away from the removable origin. -/
theorem kernel_analytic_nonzero (t : ℝ) (ht : t ≠ 0) :
    AnalyticAt ℝ eulerianKernel t := by
  have hi : AnalyticAt ℝ (fun u : ℝ => u) t := analyticAt_id
  have hh : AnalyticAt ℝ (fun u : ℝ => u / 2) t := hi.div_const
  have hs : AnalyticAt ℝ (fun u : ℝ => Real.sin (u / 2)) t :=
    Real.analyticAt_sin.comp hh
  have hd : (t / 2 : ℝ) ≠ 0 := div_ne_zero ht (by norm_num)
  have hq : AnalyticAt ℝ (fun u : ℝ => Real.sin (u / 2) / (u / 2)) t :=
    hs.div hh hd
  apply hq.congr
  filter_upwards [eventually_ne_nhds ht] with u hu
  change Real.sin (u / 2) / (u / 2) = EulerianCert.FourierModes.rE u
  rw [EulerianCert.FourierModes.rE_of_ne_zero hu]
  field_simp

/-- The actual first reconstruction coordinate is analytic at the endpoint. -/
theorem X_analytic (a : ℝ) (M : ℕ) :
    AnalyticAt ℝ (XConv a M) (2 * Real.pi) := by
  have hi : AnalyticAt ℝ (fun t : ℝ => t) (2 * Real.pi) := analyticAt_id
  have hc : AnalyticAt ℝ (fun _ : ℝ => (2 : ℝ)) (2 * Real.pi) := analyticAt_const
  have hd : AnalyticAt ℝ (fun t : ℝ => 2 * t) (2 * Real.pi) := hc.mul hi
  have hk : AnalyticAt ℝ (fun t : ℝ => eulerianKernel (2 * t)) (2 * Real.pi) :=
    (kernel_analytic_nonzero _ (by positivity)).comp hd
  have ha : AnalyticAt ℝ (fun _ : ℝ => a) (2 * Real.pi) := analyticAt_const
  have h1 : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) (2 * Real.pi) := analyticAt_const
  exact (ha.mul hi).mul (h1.sub (hk.pow M))

/-- The true transverse coordinate is analytic at the endpoint. -/
theorem Y_analytic (a : ℝ) (M : ℕ) :
    AnalyticAt ℝ (YConv a M) (2 * Real.pi) := by
  have hi : AnalyticAt ℝ (fun t : ℝ => t) (2 * Real.pi) := analyticAt_id
  have ha : AnalyticAt ℝ (fun _ : ℝ => a) (2 * Real.pi) := analyticAt_const
  have hk := kernel_analytic_nonzero (2 * Real.pi) (by positivity)
  exact ((ha.mul (hi.pow 2)).div_const (c := 2)).mul (hk.pow (2 * M))

/-- A genuine two-sided analytic inverse of X exists for every nonzero
scale and every M≥2. Its derivative is the reciprocal of the scale. -/
theorem exists_analytic_inverse (a : ℝ) (ha : a ≠ 0) (M : ℕ) (hM : 2 ≤ M) :
    ∃ T : ℝ → ℝ,
      AnalyticAt ℝ T (XConv a M (2 * Real.pi)) ∧
      T (XConv a M (2 * Real.pi)) = 2 * Real.pi ∧
      HasStrictDerivAt T a⁻¹ (XConv a M (2 * Real.pi)) ∧
      (∀ᶠ t in 𝓝 (2 * Real.pi), T (XConv a M t) = t) ∧
      (∀ᶠ x in 𝓝 (XConv a M (2 * Real.pi)), XConv a M (T x) = x) := by
  have hf := X_analytic a M
  have hder : deriv (XConv a M) (2 * Real.pi) = a :=
    convolution_endpoint_X_deriv a M hM
  have hne : deriv (XConv a M) (2 * Real.pi) ≠ 0 := by rw [hder]; exact ha
  have hstrict := hf.hasStrictDerivAt
  let T := hstrict.localInverse _ _ _ hne
  have hleft : ∀ᶠ t in 𝓝 (2 * Real.pi), T (XConv a M t) = t :=
    hstrict.eventually_left_inverse hne
  have hright : ∀ᶠ x in 𝓝 (XConv a M (2 * Real.pi)), XConv a M (T x) = x :=
    hstrict.eventually_right_inverse hne
  refine ⟨T, hf.analyticAt_localInverse hne, hleft.self_of_nhds, ?_, hleft, hright⟩
  simpa only [hder] using hstrict.to_localInverse hne

/-- Actual analytic graph in the independent horizontal variable: it
agrees with the parametrized curve near the endpoint, has zero height
there, and has the certified nonzero leading contact limit. -/
theorem exists_analytic_terminal_graph (a : ℝ) (ha : a ≠ 0) (M : ℕ) (hM : 2 ≤ M) :
    ∃ G : ℝ → ℝ,
      AnalyticAt ℝ G (XConv a M (2 * Real.pi)) ∧
      G (XConv a M (2 * Real.pi)) = 0 ∧
      (∀ᶠ t in 𝓝 (2 * Real.pi), G (XConv a M t) = YConv a M t) ∧
      Tendsto (fun x : ℝ => G x / (x - XConv a M (2 * Real.pi)) ^ (2 * M))
        (𝓝[≠] (XConv a M (2 * Real.pi)))
        (𝓝 ((a * (2 * Real.pi) ^ 2 / 2 * (-1 / (2 * Real.pi)) ^ (2 * M)) /
          a ^ (2 * M))) := by
  obtain ⟨T, hTa, hT0, hTd, hleft, hright⟩ := exists_analytic_inverse a ha M hM
  let G := fun x : ℝ => YConv a M (T x)
  have hy : AnalyticAt ℝ (YConv a M) (T (XConv a M (2 * Real.pi))) := by
    rw [hT0]
    exact Y_analytic a M
  refine ⟨G, hy.comp hTa, ?_, ?_, ?_⟩
  · change YConv a M (T (XConv a M (2 * Real.pi))) = 0
    rw [hT0]
    exact convolution_endpoint_Y a M (by omega)
  · filter_upwards [hleft] with t ht
    change YConv a M (T (XConv a M t)) = YConv a M t
    rw [ht]
  · have hT : Tendsto T (𝓝[≠] (XConv a M (2 * Real.pi))) (𝓝[≠] (2 * Real.pi)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa only [hT0] using
          (hTa.continuousAt.tendsto.mono_left
            (nhdsWithin_le_nhds : 𝓝[≠] (XConv a M (2 * Real.pi)) ≤ 𝓝 (XConv a M (2 * Real.pi))))
      · have hn : ∀ᶠ x : ℝ in 𝓝[≠] (XConv a M (2 * Real.pi)),
            x ≠ XConv a M (2 * Real.pi) := self_mem_nhdsWithin
        filter_upwards [hn, hright.filter_mono nhdsWithin_le_nhds] with x hx hr
        change T x ≠ 2 * Real.pi
        intro he
        apply hx
        rw [← hr, he]
    apply ((TerminalContact.graph_contact a ha M hM).comp hT).congr'
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds] with x hx
    change YConv a M (T x) / (XConv a M (T x) - XConv a M (2 * Real.pi)) ^ (2 * M) =
      G x / (x - XConv a M (2 * Real.pi)) ^ (2 * M)
    rw [hx] <;> rfl

end Manuscript15.TerminalAnalytic

#print axioms Manuscript15.TerminalAnalytic.kernel_analytic_nonzero
#print axioms Manuscript15.TerminalAnalytic.X_analytic
#print axioms Manuscript15.TerminalAnalytic.Y_analytic
#print axioms Manuscript15.TerminalAnalytic.exists_analytic_inverse
#print axioms Manuscript15.TerminalAnalytic.exists_analytic_terminal_graph
