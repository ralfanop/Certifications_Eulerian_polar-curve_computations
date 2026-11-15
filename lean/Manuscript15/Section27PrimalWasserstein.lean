import Mathlib

/-!
# M15 §2.7 — direct primal Wasserstein-1 transport on the real line

A coupling is an actual measure on ℝ × ℝ with both prescribed pushforward
marginals. The distance is the standard infimum of the (unscaled) integral
transport cost, on probability measures with finite first moments.
No optimal coupling, duality theorem, or extra axioms are assumed.
-/

open MeasureTheory
noncomputable section

namespace Manuscript15.Section27.Primal

def couplings (μ ν : Measure ℝ) : Set (Measure (ℝ × ℝ)) :=
  {γ | Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν}

def cost (γ : Measure (ℝ × ℝ)) : ℝ :=
  ∫ p, |p.1 - p.2| ∂γ

/-- Primal Wasserstein-1; the probability and finite-moment domain of the
distance is explicit in the theorems below. -/
def wasserstein1 (μ ν : Measure ℝ) : ℝ :=
  sInf (cost '' couplings μ ν)

theorem couplings_nonempty (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : (couplings μ ν).Nonempty := by
  refine ⟨μ.prod ν, ?_⟩
  simp [couplings]

theorem cost_integrable {μ ν : Measure ℝ} {γ : Measure (ℝ × ℝ)}
    (hγ : γ ∈ couplings μ ν)
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) :
    Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) γ := by
  change Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν at hγ
  have hp : MeasurePreserving Prod.fst γ μ := ⟨measurable_fst, hγ.1⟩
  have hq : MeasurePreserving Prod.snd γ ν := ⟨measurable_snd, hγ.2⟩
  have hx : Integrable (fun p : ℝ × ℝ => p.1) γ :=
    hp.integrable_comp_of_integrable hμ
  have hy : Integrable (fun p : ℝ × ℝ => p.2) γ :=
    hq.integrable_comp_of_integrable hν
  simpa only [Real.norm_eq_abs] using (hx.sub' hy).norm

theorem wasserstein1_nonneg (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : 0 ≤ wasserstein1 μ ν := by
  unfold wasserstein1
  apply le_csInf ((couplings_nonempty μ ν).image cost)
  intro c hc
  obtain ⟨γ, _, rfl⟩ := hc
  exact integral_nonneg (fun p => abs_nonneg (p.1 - p.2))

private theorem integral_comp_preserving
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {γ : Measure (ℝ × ℝ)} {ρ : Measure ℝ}
    {p : ℝ × ℝ → ℝ} {f : ℝ → E}
    (hp : MeasurePreserving p γ ρ) (hf : Integrable f ρ) :
    (∫ z, f (p z) ∂γ) = ∫ x, f x ∂ρ := by
  have hm : AEStronglyMeasurable f (Measure.map p γ) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  calc
    (∫ z, f (p z) ∂γ) = ∫ x, f x ∂Measure.map p γ :=
      (integral_map hp.measurable.aemeasurable hm).symm
    _ = ∫ x, f x ∂ρ := by rw [hp.map_eq]

/-- Every coupling gives the actual marginal integral bound, then taking
the infimum gives the sharp primal W₁ bound. Works for real and complex
observables (and general real Banach-valued observables). -/
theorem norm_integral_sub_le_wasserstein1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν)
    (f : ℝ → E) (K : ℝ) (hK : 0 ≤ K)
    (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (hLip : ∀ x y : ℝ, ‖f x - f y‖ ≤ K * |x - y|) :
    ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ ≤ K * wasserstein1 μ ν := by
  have hb : ∀ γ ∈ couplings μ ν,
      ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ ≤ K * cost γ := by
    intro γ hγ
    have hc := cost_integrable hγ hμ hν
    change Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν at hγ
    have hp : MeasurePreserving Prod.fst γ μ := ⟨measurable_fst, hγ.1⟩
    have hq : MeasurePreserving Prod.snd γ ν := ⟨measurable_snd, hγ.2⟩
    have hf1 : Integrable (fun p : ℝ × ℝ => f p.1) γ :=
      hp.integrable_comp_of_integrable hfμ
    have hf2 : Integrable (fun p : ℝ × ℝ => f p.2) γ :=
      hq.integrable_comp_of_integrable hfν
    have hpoint : ∀ᵐ p ∂γ, ‖f p.1 - f p.2‖ ≤ K * |p.1 - p.2| :=
      Filter.Eventually.of_forall (fun p => hLip p.1 p.2)
    calc
      ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ =
          ‖∫ p, f p.1 - f p.2 ∂γ‖ := by
        rw [integral_sub hf1 hf2, integral_comp_preserving hp hfμ,
          integral_comp_preserving hq hfν]
      _ ≤ ∫ p, K * |p.1 - p.2| ∂γ :=
        norm_integral_le_of_norm_le (hc.const_mul K) hpoint
      _ = K * cost γ := by rw [cost, integral_const_mul]
  rcases eq_or_lt_of_le hK with hzero | hpos
  · obtain ⟨γ, hγ⟩ := couplings_nonempty μ ν
    subst K
    simpa using hb γ hγ
  · have hi : ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ / K ≤
        wasserstein1 μ ν := by
      unfold wasserstein1
      apply le_csInf ((couplings_nonempty μ ν).image cost)
      intro c hc
      obtain ⟨γ, hγ, rfl⟩ := hc
      apply (div_le_iff₀ hpos).2
      rw [mul_comm]
      exact hb γ hγ
    have hh := (div_le_iff₀ hpos).mp hi
    rwa [mul_comm (wasserstein1 μ ν) K] at hh

private theorem phase_norm (a : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- Sharp complex chord bound, not the weaker sum of two real bounds. -/
theorem complex_phase_lipschitz (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) -
      Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have hadd : Complex.I * ((a - b : ℝ) : ℂ) + Complex.I * (b : ℂ) =
      Complex.I * (a : ℂ) := by
    push_cast
    ring
  calc
    _ = ‖(Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (b : ℂ))‖ := by
      rw [sub_mul, one_mul, ← Complex.exp_add, hadd]
    _ = ‖Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1‖ := by
      rw [norm_mul, phase_norm, mul_one]
    _ ≤ |a - b| := by
      simpa only [Real.norm_eq_abs] using
        (Complex.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

/-- The actual Mathlib characteristic functions satisfy the sharp stability
estimate for the primal Wasserstein-1 distance on probability measures. -/
theorem charFun_sub_le_wasserstein1
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) (s : ℝ) :
    ‖charFun μ s - charFun ν s‖ ≤ |s| * wasserstein1 μ ν := by
  let f : ℝ → ℂ := fun x => Complex.exp (Complex.I * ((s * x : ℝ) : ℂ))
  have hf (ρ : Measure ℝ) [IsProbabilityMeasure ρ] : Integrable f ρ := by
    apply (integrable_const (1 : ℝ)).mono'
    · dsimp [f]
      fun_prop
    · exact Filter.Eventually.of_forall (fun x => by
        change ‖Complex.exp (Complex.I * ((s * x : ℝ) : ℂ))‖ ≤ 1
        rw [phase_norm])
  have hl (x y : ℝ) : ‖f x - f y‖ ≤ |s| * |x - y| := by
    calc
      _ ≤ |s * x - s * y| := complex_phase_lipschitz (s * x) (s * y)
      _ = _ := by rw [← mul_sub, abs_mul]
  have hchar (ρ : Measure ℝ) : charFun ρ s = ∫ x, f x ∂ρ := by
    simp only [charFun_apply_real, f, Complex.ofReal_mul, mul_comm Complex.I]
  rw [hchar μ, hchar ν]
  exact norm_integral_sub_le_wasserstein1 μ ν hμ hν f |s| (abs_nonneg s)
    (hf μ) (hf ν) hl

/-- The stability estimate and Mathlib's characteristic-function
uniqueness imply separation, without proving Kantorovich duality. -/
theorem eq_of_wasserstein1_eq_zero
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν)
    (hzero : wasserstein1 μ ν = 0) : μ = ν := by
  apply Measure.ext_of_charFun
  funext s
  have h := charFun_sub_le_wasserstein1 μ ν hμ hν s
  rw [hzero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

#print axioms Manuscript15.Section27.Primal.couplings_nonempty
#print axioms Manuscript15.Section27.Primal.cost_integrable
#print axioms Manuscript15.Section27.Primal.wasserstein1_nonneg
#print axioms Manuscript15.Section27.Primal.norm_integral_sub_le_wasserstein1
#print axioms Manuscript15.Section27.Primal.complex_phase_lipschitz
#print axioms Manuscript15.Section27.Primal.charFun_sub_le_wasserstein1
#print axioms Manuscript15.Section27.Primal.eq_of_wasserstein1_eq_zero

end Manuscript15.Section27.Primal
