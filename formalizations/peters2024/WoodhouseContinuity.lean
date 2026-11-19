import Peters2024
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Def. 6.1, for a specified globally continuous family of Woodhouse
coordinates and integrands. This is the actual Mathlib circle integral,
not an abstract function merely assumed to be continuous. -/
namespace Peters2024
open Set Metric MeasureTheory Complex
noncomputable section

variable {X : Type*}

def woodhouseIntegrand (ξ τ : X → ℂ) (f : ℂ × ℂ × ℂ → ℂ) (p : X) (z : ℂ) : ℂ :=
  f (ξ p + star z * τ p, star (ξ p) + z * star (τ p), z)

def woodhouseIntegral (ξ τ : X → ℂ) (f : ℂ × ℂ × ℂ → ℂ) (p : X) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * circleIntegral (fun z => woodhouseIntegrand ξ τ f p z / z) 0 1

/-- The factor dz/z is i dθ on the unit circle, without changing the
normalization 1/(2π) printed in the paper. -/
theorem woodhouse_parameterization (ξ τ : X → ℂ) (f : ℂ × ℂ × ℂ → ℂ) (p : X) :
    woodhouseIntegral ξ τ f p = (2 * (Real.pi : ℂ))⁻¹ *
      (∫ θ in Icc (0 : ℝ) (2 * Real.pi), Complex.I * woodhouseIntegrand ξ τ f p (circleMap 0 1 θ)) := by
  have hfun : (fun θ : ℝ => deriv (circleMap 0 1) θ •
      (woodhouseIntegrand ξ τ f p (circleMap 0 1 θ) / circleMap 0 1 θ)) =
      (fun θ : ℝ => Complex.I * woodhouseIntegrand ξ τ f p (circleMap 0 1 θ)) := by
    funext θ
    have hz : circleMap 0 1 θ ≠ 0 := by simp
    rw [deriv_circleMap, smul_eq_mul]
    field_simp [hz]
  rw [woodhouseIntegral, circleIntegral_def_Icc, hfun]

variable [TopologicalSpace X]

/-- Joint continuity of the angular integrand follows from continuous
coordinate maps, continuous conjugation, and a continuous integrand. -/
theorem continuous_woodhouse_angular (ξ τ : X → ℂ) (f : ℂ × ℂ × ℂ → ℂ)
    (hξ : Continuous ξ) (hτ : Continuous τ) (hf : Continuous f) :
    Continuous (fun q : X × ℝ => Complex.I * woodhouseIntegrand ξ τ f q.1 (circleMap 0 1 q.2)) := by
  have hz : Continuous (fun q : X × ℝ => circleMap 0 1 q.2) := (continuous_circleMap 0 1).comp continuous_snd
  have hx := hξ.comp (continuous_fst : Continuous (Prod.fst : X × ℝ → X))
  have ht := hτ.comp (continuous_fst : Continuous (Prod.fst : X × ℝ → X))
  unfold woodhouseIntegrand
  exact continuous_const.mul (hf.comp ((hx.add ((continuous_star.comp hz).mul ht)).prodMk
    (((continuous_star.comp hx).add (hz.mul (continuous_star.comp ht))).prodMk hz)))

/-- Continuity of the actual parameterized contour family. No continuity
of the integral itself is assumed. -/
theorem continuous_woodhouseIntegral [FirstCountableTopology X] [LocallyCompactSpace X]
    (ξ τ : X → ℂ) (f : ℂ × ℂ × ℂ → ℂ)
    (hξ : Continuous ξ) (hτ : Continuous τ) (hf : Continuous f) :
    Continuous (woodhouseIntegral ξ τ f) := by
  have h : Continuous (fun p : X => ∫ θ in Icc (0 : ℝ) (2 * Real.pi),
      Complex.I * woodhouseIntegrand ξ τ f p (circleMap 0 1 θ)) :=
    continuous_parametric_integral_of_continuous (continuous_woodhouse_angular ξ τ f hξ hτ hf) isCompact_Icc
  have he : woodhouseIntegral ξ τ f = (fun p : X => (2 * (Real.pi : ℂ))⁻¹ *
      (∫ θ in Icc (0 : ℝ) (2 * Real.pi), Complex.I * woodhouseIntegrand ξ τ f p (circleMap 0 1 θ))) :=
    funext (woodhouse_parameterization ξ τ f)
  rw [he]
  exact continuous_const.mul h

/-- The real/imaginary coordinate identification used for Borsuk–Ulam. -/
def complexCoordinates (z : ℂ) : Coordinates 2 := fun j => if j = 0 then z.re else z.im

theorem continuous_complexCoordinates : Continuous complexCoordinates := by
  apply continuous_pi
  intro j
  by_cases h : j = 0
  · simpa [complexCoordinates, h] using Complex.continuous_re
  · simpa [complexCoordinates, h] using Complex.continuous_im

theorem injective_complexCoordinates : Function.Injective complexCoordinates := by
  intro z w h
  apply Complex.ext
  · simpa [complexCoordinates] using congrFun h (0 : Fin 2)
  · simpa [complexCoordinates] using congrFun h (1 : Fin 2)

theorem thm_6_2_woodhouse (but : BorsukUlam 2)
    (ξ τ : Sphere 2 → ℂ) (f : ℂ × ℂ × ℂ → ℂ)
    (hξ : Continuous ξ) (hτ : Continuous τ) (hf : Continuous f) :
    ∃ p, woodhouseIntegral ξ τ f p = woodhouseIntegral ξ τ f (-p) := by
  letI : LocallyCompactSpace (Sphere 2) := isClosed_sphere.locallyCompactSpace
  have hc := continuous_complexCoordinates.comp (continuous_woodhouseIntegral ξ τ f hξ hτ hf)
  obtain ⟨p, hp⟩ := but (complexCoordinates ∘ woodhouseIntegral ξ τ f) hc
  exact ⟨p, injective_complexCoordinates hp⟩

end
end Peters2024

#print axioms Peters2024.woodhouse_parameterization
#print axioms Peters2024.continuous_woodhouse_angular
#print axioms Peters2024.continuous_woodhouseIntegral
#print axioms Peters2024.continuous_complexCoordinates
#print axioms Peters2024.injective_complexCoordinates
#print axioms Peters2024.thm_6_2_woodhouse
