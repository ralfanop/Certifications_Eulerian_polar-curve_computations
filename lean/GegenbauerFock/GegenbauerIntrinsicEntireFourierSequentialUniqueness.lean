import GegenbauerFock.GegenbauerIntrinsicEntireFourierAccumulationUniqueness

/-!
# V007 — countable convergent sampling determines the ultraspherical source

Let zₙ ∈ ℂ tend to a finite complex limit w, with zₙ ≠ w for all n.
Then the samples have w as a genuine accumulation point (even if
the sequence is not assumed injective). Thus genuine Fourier–Bochner
integral data at the points zₙ uniquely determine f ∈ L²(ν_λ).
The same is true for two different positive Gaussian Fock scales.

No claim of stable reconstruction or finite-sample injectivity is made:
this is qualitative analytic uniqueness, not a bounded inverse theorem.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A convergent sequence avoiding its limit yields an actual
finite accumulation point of its range. -/
theorem range_has_accumulation_of_tendsto_avoiding_limit
    (z : ℕ → ℂ) (w : ℂ)
    (hz : Tendsto z atTop (𝓝 w))
    (havoid : ∀ n : ℕ, z n ≠ w) :
    w ∈ closure (Set.range z \ ({w} : Set ℂ)) := by
  apply (mem_closure_iff_nhds).2
  intro s hs
  obtain ⟨n, hn⟩ := (hz.eventually hs).exists
  exact ⟨z n, hn, ⟨⟨n, rfl⟩, havoid n⟩⟩

/-- Equality at every point of a convergent complex-frequency sequence
already determines the original ultraspherical L² class. -/
theorem ultraspherical_fourierBochner_injective_of_convergent_samples
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℕ → ℂ) (w : ℂ)
    (hz : Tendsto z atTop (𝓝 w))
    (havoid : ∀ n : ℕ, z n ≠ w)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : ∀ n : ℕ,
      (∫ u : ℝ, f u *
        Complex.exp (Complex.I * z n * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) =
      (∫ u : ℝ, g u *
        Complex.exp (Complex.I * z n * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam))) :
    f = g := by
  apply ultraspherical_fourierBochner_injective_of_accumulation_samples
    lam alpha hlam ha (Set.range z) w
    (range_has_accumulation_of_tendsto_avoiding_limit z w hz havoid)
    f g
  intro t ht
  rcases ht with ⟨n, rfl⟩
  exact h n

/-- Pointwise equality of output entire functions on a convergent
complex sample sequence suffices even for distinct Gaussian weights. -/
theorem C_intrinsicEntire_crossAlpha_injective_of_convergent_samples
    (lam alpha beta : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) (hb : 0 < beta)
    (z : ℕ → ℂ) (w : ℂ)
    (hz : Tendsto z atTop (𝓝 w))
    (havoid : ∀ n : ℕ, z n ≠ w)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : ∀ n : ℕ,
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) (z n) =
      GaussianArea.entireRepresentative beta
        (C_intrinsicEntire lam beta hlam hb g) (z n)) :
    f = g := by
  apply C_intrinsicEntire_crossAlpha_injective_of_accumulation_samples
    lam alpha beta hlam ha hb (Set.range z) w
    (range_has_accumulation_of_tendsto_avoiding_limit z w hz havoid)
    f g
  intro t ht
  rcases ht with ⟨n, rfl⟩
  exact h n

#print axioms GegenbauerFock.GeneralUltrasphericalFock.range_has_accumulation_of_tendsto_avoiding_limit
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_injective_of_convergent_samples
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_crossAlpha_injective_of_convergent_samples

end GegenbauerFock.GeneralUltrasphericalFock
