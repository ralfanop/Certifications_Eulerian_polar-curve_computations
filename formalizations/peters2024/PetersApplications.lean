import BorsukBridge
import WoodhouseContinuity
import HomotopyRealization

/-! Compose the checked classical bridge with the explicit analytic and
relative-homotopy models. The concrete coordinate maps and integrand are
required to be continuous; the continuity of the resulting integral is proved. -/
namespace Peters2024
open Metric

theorem thm_6_2_woodhouse_closed (ξ τ : Sphere 2 → ℂ) (f : ℂ × ℂ × ℂ → ℂ)
    (hξ : Continuous ξ) (hτ : Continuous τ) (hf : Continuous f) :
    ∃ p, woodhouseIntegral ξ τ f p = woodhouseIntegral ξ τ f (-p) :=
  thm_6_2_woodhouse (thm_1_1 2) ξ τ f hξ hτ hf

theorem cor_6_3_woodhouse_closed (ξ τ : Sphere 2 → ℂ) (f : ℂ × ℂ × ℂ → ℂ)
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
  obtain ⟨p, hp, d, k, hk, hh⟩ := thm_3_5_nullhomotopic 2 (by decide) (thm_1_1 2) g hg
  exact ⟨p, injective_complexCoordinates hp, d, k, hk, hh⟩

theorem thm_3_5_nullhomotopic_closed (n : ℕ) (hn : 1 ≤ n)
    (f : Sphere n → Coordinates n) (hf : Continuous f) :
    ∃ p : Sphere n, f p = f (-p) ∧
      ∃ d : DiscreteArc p (-p), ∃ k : DiscreteArc (f p) (f p),
      (∀ t : unitInterval, k.path t = f (d.path t)) ∧
      k.path.Homotopic (Path.refl (f p)) :=
  thm_3_5_nullhomotopic n hn (thm_1_1 n) f hf

end Peters2024

#print axioms Peters2024.thm_6_2_woodhouse_closed
#print axioms Peters2024.cor_6_3_woodhouse_closed
#print axioms Peters2024.thm_3_5_nullhomotopic_closed
