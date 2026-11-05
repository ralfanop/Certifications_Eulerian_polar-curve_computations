import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation
import GegenbauerFock.GegenbauerIntrinsicEntireAlphaCoherence
import GegenbauerFock.OutputComplexAnalyticIdentity

/-!
# V007 — genuine Fourier–Bochner uniqueness from an arbitrary accumulation set

A nontrivial sampling set S ⊆ ℂ with any finite accumulation point w
determines the entire Fourier–Bochner transform and, by injectivity of
the true compact ultraspherical-to-Fock operator, the source L² class.
No interval assumption is needed: infinitely many distinct samples
accumulating at w suffice, regardless of their geometric arrangement.

The complex analytic identity theorem is applied to the *actual*
canonical entire Gaussian L² representative. Two different positive
Gaussian Fock weights are allowed, but their norms are not identified.
-/

noncomputable section
open MeasureTheory Set

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- An entire complex function is determined by any set S which has a
finite accumulation point w: w belongs to the closure of S without w. -/
theorem entire_eq_of_accumulation_samples
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (F G : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hsame : ∀ z ∈ S, F z = G z) :
    F = G := by
  let D : ℂ → ℂ := fun z => F z - G z
  have hdiff : Differentiable ℂ D := hF.sub hG
  have hanalytic : AnalyticOnNhd ℂ D Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff
  have hsub :
      S \ ({w} : Set ℂ) ⊆
        {z : ℂ | D z = 0} \ ({w} : Set ℂ) := by
    intro z hz
    rcases hz with ⟨hzS, hzne⟩
    refine ⟨?_, hzne⟩
    exact sub_eq_zero.mpr (hsame z hzS)
  have hz :
      w ∈ closure ({z : ℂ | D z = 0} \ ({w} : Set ℂ)) :=
    (closure_mono hsub) hacc
  have hident : Set.EqOn D 0 Set.univ :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure
      hanalytic isPreconnected_univ (Set.mem_univ w) hz
  funext z
  exact sub_eq_zero.mp (hident (Set.mem_univ z))

/-- Arbitrary complex-frequency samples with a finite accumulation
point determine the ultraspherical L² input via its actual entire
Bargmann–Fock-valued Gegenbauer transform. -/
theorem C_intrinsicEntire_injective_of_accumulation_samples
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : ∀ z ∈ S,
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) z =
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha g) z) :
    f = g := by
  have hrep :
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) =
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha g) := by
    apply entire_eq_of_accumulation_samples S w hacc
    · exact GaussianArea.entireRepresentative_differentiable alpha
        (C_intrinsicEntire lam alpha hlam ha f)
    · exact GaussianArea.entireRepresentative_differentiable alpha
        (C_intrinsicEntire lam alpha hlam ha g)
    · exact h
  apply C_intrinsicEntire_injective lam alpha hlam ha
  exact GaussianArea.entireRepresentative_injective alpha hrep

/-- The *original* Fourier–Bochner integral on any sampling set S with
a finite accumulation point is injective on ultraspherical L². -/
theorem ultraspherical_fourierBochner_injective_of_accumulation_samples
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : ∀ z ∈ S,
      (∫ u : ℝ, f u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) =
      (∫ u : ℝ, g u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam))) :
    f = g := by
  apply C_intrinsicEntire_injective_of_accumulation_samples
    lam alpha hlam ha S w hacc f g
  intro z hz
  rw [C_intrinsicEntire_pointwiseBochner,
    C_intrinsicEntire_pointwiseBochner]
  exact h z hz

/-- Sampled entire outputs of two distinct positive Gaussian-Fock
realizations still determine the same original L² source, provided
the complex sample set has a finite accumulation point. -/
theorem C_intrinsicEntire_crossAlpha_injective_of_accumulation_samples
    (lam alpha beta : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) (hb : 0 < beta)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : ∀ z ∈ S,
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) z =
      GaussianArea.entireRepresentative beta
        (C_intrinsicEntire lam beta hlam hb g) z) :
    f = g := by
  apply C_intrinsicEntire_injective_of_accumulation_samples
    lam alpha hlam ha S w hacc f g
  intro z hz
  exact (h z hz).trans
    (C_intrinsicEntire_pointwise_independent_of_alpha
      lam alpha beta hlam ha hb g z).symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.entire_eq_of_accumulation_samples
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_injective_of_accumulation_samples
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_injective_of_accumulation_samples
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_crossAlpha_injective_of_accumulation_samples

end GegenbauerFock.GeneralUltrasphericalFock
