import GegenbauerFock.GegenbauerIntrinsicEntireFourierPointwiseInstability

/-!
# V007 — no continuous inverse of genuine entire Fourier data with pointwise topology

The original ultraspherical Fourier–Bochner transform maps its L² source
into ℂ → ℂ, the space of ALL complex-frequency data equipped with the
product (pointwise-convergence) topology.

The transform is exactly injective, as proved independently from complex
analytic identity and Gegenbauer–Fock Hilbert injectivity. Nevertheless,
there is NO globally defined, even nonlinear, reconstruction from this
function space into the ultraspherical L² source which is continuous at
the zero data function and is a left inverse of the actual Fourier map.

The proof uses the certified normalized source sequence with genuine
Bochner Fourier integrals tending to zero at every complex frequency,
together with product-topology convergence (tendsto_pi_nhds).

This is a genuine topological inverse obstruction; no extra axiom or
unproved numerical stability assumption is introduced.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The original complex Fourier–Bochner transform as a map into
all complex-valued functions, with their product topology. -/
noncomputable def ultraspherical_fourierBochner_function
    (lam : ℝ) (f : Lp ℂ 2 (Ultraspherical.measure lam)) : ℂ → ℂ :=
  fun z => ∫ v : ℝ, f v *
    Complex.exp (Complex.I * z * (v : ℂ) / 2)
    ∂(Ultraspherical.measure lam)

/-- Unit source vectors can have their ACTUAL complex Fourier transforms
converge to zero as functions in the product topology while the source
sequence has no strong L² limit. -/
theorem ultraspherical_fourierBochner_productTopology_null_no_strong_source_limit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => ultraspherical_fourierBochner_function lam (u n))
        atTop (nhds (0 : ℂ → ℂ)) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ¬ Tendsto u atTop (nhds f)) := by
  obtain ⟨u, hunit, _hFock, hpoint, hnostrong⟩ :=
    ultraspherical_fourierBochner_normalized_pointwise_null_no_strong_source_limit
      lam alpha hlam ha
  refine ⟨u, hunit, ?_, hnostrong⟩
  apply tendsto_pi_nhds.mpr
  intro z
  simpa only [ultraspherical_fourierBochner_function, Pi.zero_apply]
    using hpoint z

/-- No global reconstruction (even nonlinear) of the ultraspherical
L² class from genuine entire Fourier–Bochner data can be continuous
at the zero FUNCTION in the product topology. -/
theorem ultraspherical_fourierBochner_no_continuous_left_inverse_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (r : (ℂ → ℂ) → Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r (ultraspherical_fourierBochner_function lam f) = f) :
    ¬ ContinuousAt r (0 : ℂ → ℂ) := by
  intro hcont
  obtain ⟨u, _hunit, himage, hnostrong⟩ :=
    ultraspherical_fourierBochner_productTopology_null_no_strong_source_limit
      lam alpha hlam ha
  have hrec :
      Tendsto
        (fun n : ℕ => r (ultraspherical_fourierBochner_function lam (u n)))
        atTop (nhds (r (0 : ℂ → ℂ))) :=
    hcont.tendsto.comp himage
  have hsequence :
      (fun n : ℕ => r (ultraspherical_fourierBochner_function lam (u n))) = u := by
    funext n
    exact hleft (u n)
  rw [hsequence] at hrec
  exact hnostrong (r 0) hrec

/-- There is no globally continuous reconstruction from the
product-topology function space of ALL complex frequencies,
even if the reconstruction is permitted to be nonlinear. -/
theorem ultraspherical_fourierBochner_no_continuous_global_reconstruction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ ∃ r : (ℂ → ℂ) → Lp ℂ 2 (Ultraspherical.measure lam),
      Continuous r ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        r (ultraspherical_fourierBochner_function lam f) = f) := by
  rintro ⟨r, hcont, hleft⟩
  exact ultraspherical_fourierBochner_no_continuous_left_inverse_at_zero
    lam alpha hlam ha r hleft hcont.continuousAt

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_productTopology_null_no_strong_source_limit
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_no_continuous_left_inverse_at_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_no_continuous_global_reconstruction

end GegenbauerFock.GeneralUltrasphericalFock
