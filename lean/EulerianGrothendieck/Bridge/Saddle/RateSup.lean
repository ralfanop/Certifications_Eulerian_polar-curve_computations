import Bridge.Saddle.Corollary

/-!
# The rate function: `I(x) = s(x)x - Λ(s(x)) = sup_s {sx - Λ(s)}` (eqs. (94)–(95))
-/

open Set Filter Topology

namespace EulerianBridge.Saddle

theorem κ1_strictMono : StrictMono (κ 1) := by
  rw [κ_one_eq_Lp]; exact UL.Lp_strictMono

/-- `I(x) = s(x)x - Λ(s(x))` is the Legendre transform `sup_t (tx - Λ(t))`. -/
theorem Irate_isGreatest {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    IsGreatest (Set.range fun t : ℝ => t * x - Lr t) (Irate x) := by
  refine ⟨⟨UL.Ip x, rfl⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  set s := UL.Ip x
  have hs : κ 1 s = x := Lp_Ip' hx
  set f : ℝ → ℝ := fun t => t * x - Lr t
  have hf : ∀ y, HasDerivAt f (x - κ 1 y) y := by
    intro y
    have h := hasDerivAt_κ 0 y
    rw [show κ 0 = Lr by funext u; exact κ_zero_eq u] at h
    have := ((hasDerivAt_id y).mul_const x).sub h
    simpa [f] using this
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  show f t ≤ f s
  rcases lt_trichotomy t s with h | h | h
  · obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope f (fun y => x - κ 1 y) h hcont.continuousOn
      (fun y _ => hf y)
    have hξs : κ 1 ξ < κ 1 s := κ1_strictMono hξ.2
    have : 0 ≤ (f s - f t) / (s - t) := by rw [← hξd]; linarith
    have hst : 0 < s - t := by linarith
    have := (div_nonneg_iff.mp this)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  · rw [h]
  · obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope f (fun y => x - κ 1 y) h hcont.continuousOn
      (fun y _ => hf y)
    have hξs : κ 1 s < κ 1 ξ := κ1_strictMono hξ.1
    have hts : 0 < t - s := by linarith
    have : (f t - f s) / (t - s) ≤ 0 := by rw [← hξd]; linarith
    have := div_nonpos_iff.mp this
    rcases this with ⟨h1, _⟩ | ⟨h1, h2⟩
    · linarith
    · linarith

end EulerianBridge.Saddle
