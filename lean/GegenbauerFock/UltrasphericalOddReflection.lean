import GegenbauerFock.UltrasphericalBetaSymmetry
import GegenbauerFock.UltrasphericalBetaMoments

/-!
# V007: symmetric Beta odd integrands and Lebesgue reflection

This certifies an explicit antisymmetry of every odd weighted
moment integrand, and invariance of real Lebesgue volume under the
affine reflection x ↦ 1-x. Both steps are required before the
unconditional vanishing of all ultraspherical odd moments.
-/

open MeasureTheory ProbabilityTheory

namespace GegenbauerFock.Ultraspherical

/-- Odd moment integrand against the correctly normalized symmetric
Beta density on the entire real line. -/
noncomputable def oddBetaIntegrand (lam : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x *
    (betaToInterval x) ^ (2 * n + 1)

/-- Exactly odd under reflection about one half. -/
theorem oddBetaIntegrand_reflection (lam : ℝ) (n : ℕ) (x : ℝ) :
    oddBetaIntegrand lam n (1 - x) = -oddBetaIntegrand lam n x := by
  unfold oddBetaIntegrand
  rw [symmetricBetaPDFReal_reflection_all lam x]
  have h : betaToInterval (1 - x) = -betaToInterval x := by
    unfold betaToInterval
    ring
  rw [h, Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1))]
  ring

/-- The Lebesgue measure on ℝ is invariant under x ↦ 1-x. -/
theorem volume_map_reflection :
    Measure.map (fun x : ℝ => 1 - x) (volume : Measure ℝ) =
      (volume : Measure ℝ) := by
  have hneg : Measure.map (fun x : ℝ => -x) (volume : Measure ℝ) =
      (volume : Measure ℝ) := Measure.map_neg_eq_self _
  have hshift : Measure.map (fun x : ℝ => 1 + x) (volume : Measure ℝ) =
      (volume : Measure ℝ) :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self (1 : ℝ)
  calc
    Measure.map (fun x : ℝ => 1 - x) (volume : Measure ℝ) =
        Measure.map (fun x : ℝ => 1 + x)
          (Measure.map (fun x : ℝ => -x) (volume : Measure ℝ)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      simp only [Function.comp_def, sub_eq_add_neg]
    _ = Measure.map (fun x : ℝ => 1 + x) (volume : Measure ℝ) := by rw [hneg]
    _ = volume := hshift

#print axioms GegenbauerFock.Ultraspherical.oddBetaIntegrand_reflection
#print axioms GegenbauerFock.Ultraspherical.volume_map_reflection

end GegenbauerFock.Ultraspherical
