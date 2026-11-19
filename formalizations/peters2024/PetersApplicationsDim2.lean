import BorsukUlamTwo
import WoodhouseContinuity
import HomotopyRealization

/-! Dimension-two versions of the three statements of `PetersApplications`, with
`borsukUlam_two` (Mathlib only) in place of the general bridge. None of the modules
imported here uses the external general-dimensional proof. The concrete coordinate
maps and integrand are required to be continuous, exactly as in `PetersApplications`;
the continuity of the resulting integral is proved in `WoodhouseContinuity`. -/
namespace Peters2024
open Metric

theorem thm_6_2_woodhouse_dim2 (ξ τ : Sphere 2 → ℂ) (f : ℂ × ℂ × ℂ → ℂ)
    (hξ : Continuous ξ) (hτ : Continuous τ) (hf : Continuous f) :
    ∃ p, woodhouseIntegral ξ τ f p = woodhouseIntegral ξ τ f (-p) :=
  thm_6_2_woodhouse borsukUlam_two ξ τ f hξ hτ hf

theorem cor_6_3_woodhouse_dim2 (ξ τ : Sphere 2 → ℂ) (f : ℂ × ℂ × ℂ → ℂ)
    (hξ : Continuous ξ) (hτ : Continuous τ) (hf : Continuous f) :
    ∃ p : Sphere 2, woodhouseIntegral ξ τ f p = woodhouseIntegral ξ τ f (-p) ∧
      ∃ d : DiscreteArc p (-p),
      ∃ k : DiscreteArc (complexCoordinates (woodhouseIntegral ξ τ f p))
          (complexCoordinates (woodhouseIntegral ξ τ f p)),
      (∀ t : unitInterval, k.path t = complexCoordinates (woodhouseIntegral ξ τ f (d.path t))) ∧
      k.path.Homotopic (Path.refl _) := by
  letI : LocallyCompactSpace (Sphere 2) := isClosed_sphere.locallyCompactSpace
  let g := complexCoordinates ∘ woodhouseIntegral ξ τ f
  have hg : Continuous g := continuous_complexCoordinates.comp
    (continuous_woodhouseIntegral ξ τ f hξ hτ hf)
  obtain ⟨p, hp, d, k, hk, hh⟩ := thm_3_5_nullhomotopic 2 (by decide) borsukUlam_two g hg
  exact ⟨p, injective_complexCoordinates hp, d, k, hk, hh⟩

theorem thm_3_5_nullhomotopic_dim2 (f : Sphere 2 → Coordinates 2) (hf : Continuous f) :
    ∃ p : Sphere 2, f p = f (-p) ∧
      ∃ d : DiscreteArc p (-p), ∃ k : DiscreteArc (f p) (f p),
      (∀ t : unitInterval, k.path t = f (d.path t)) ∧
      k.path.Homotopic (Path.refl (f p)) :=
  thm_3_5_nullhomotopic 2 (by decide) borsukUlam_two f hf

end Peters2024

#print axioms Peters2024.thm_6_2_woodhouse_dim2
#print axioms Peters2024.cor_6_3_woodhouse_dim2
#print axioms Peters2024.thm_3_5_nullhomotopic_dim2
