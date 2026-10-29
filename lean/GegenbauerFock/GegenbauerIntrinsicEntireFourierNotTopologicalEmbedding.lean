import GegenbauerFock.GegenbauerIntrinsicEntireFourierProductTopologyNoInverse

/-!
# V007 — genuine Fourier–Bochner map is not a topological embedding

The full complex-frequency Fourier–Bochner transform is injective
and continuous in the product (pointwise) topology. The normalized
source approximate-null sequence proves something stronger than
nonexistence of a globally continuous reconstruction on all ℂ → ℂ:

* the Fourier transform is not a topological embedding of the genuine
  ultraspherical source Hilbert space into complex-valued functions;
* even its UNIQUE set-theoretic inverse defined ONLY on its range
  cannot be continuous at the zero Fourier-data vector.

All frequencies z∈ℂ are used and the exact genuine Bochner integral
is retained. No finite-sample injectivity or unstable numerical
algorithm is asserted. The issue is discontinuity of the inverse
topology even after restricting to the true transform range.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual complex Fourier–Bochner transform of the source
zero-vector is the zero function on the entire complex plane. -/
theorem ultraspherical_fourierBochner_function_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ultraspherical_fourierBochner_function lam
      (0 : Lp ℂ 2 (Ultraspherical.measure lam)) = (0 : ℂ → ℂ) := by
  funext z
  change (∫ v : ℝ,
    (0 : Lp ℂ 2 (Ultraspherical.measure lam)) v *
      Complex.exp (Complex.I * z * (v : ℂ) / 2)
      ∂(Ultraspherical.measure lam)) = 0
  exact (evaluatedOperator_eq_integral lam alpha hlam ha z
    (0 : Lp ℂ 2 (Ultraspherical.measure lam))).symm.trans
    (map_zero (evaluatedOperator lam alpha hlam ha z))

/-- The actual complex Fourier transform is NOT a topological
embedding from the Hilbert norm topology to the product topology of
all complex frequency samples. Its source norm cannot be recovered
continuously even when ALL complex frequencies are observed. -/
theorem ultraspherical_fourierBochner_not_isEmbedding
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ IsEmbedding (ultraspherical_fourierBochner_function lam) := by
  intro hemb
  obtain ⟨u, _hunit, hFourier, hnostrong⟩ :=
    ultraspherical_fourierBochner_productTopology_null_no_strong_source_limit
      lam alpha hlam ha
  have hFourierZero :
      Tendsto (fun n : ℕ =>
        ultraspherical_fourierBochner_function lam (u n)) atTop
        (nhds (ultraspherical_fourierBochner_function lam
          (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) := by
    rw [ultraspherical_fourierBochner_function_zero lam alpha hlam ha]
    exact hFourier
  have hsource :
      Tendsto u atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    apply (hemb.isInducing.tendsto_nhds_iff).2
    simpa only [Function.comp_def] using hFourierZero
  exact hnostrong 0 hsource

/-- The zero Fourier function, viewed as a point of the TRUE range of
the ultraspherical Fourier transform (not the whole function space). -/
noncomputable def ultraspherical_fourierBochner_rangeZero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Set.range (ultraspherical_fourierBochner_function lam) :=
  ⟨0, ⟨0, ultraspherical_fourierBochner_function_zero
    lam alpha hlam ha⟩⟩

/-- Even a reconstruction defined only on the actual Fourier range
cannot be continuous at zero data if it is a left inverse. This is
strictly stronger than excluding globally continuous reconstructions
on the entire ambient space ℂ → ℂ. -/
theorem ultraspherical_fourierBochner_range_inverse_not_continuousAt_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (r : Set.range (ultraspherical_fourierBochner_function lam) →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r ⟨ultraspherical_fourierBochner_function lam f, ⟨f, rfl⟩⟩ = f) :
    ¬ ContinuousAt r
      (ultraspherical_fourierBochner_rangeZero lam alpha hlam ha) := by
  intro hcont
  obtain ⟨u, _hunit, hFourier, hnostrong⟩ :=
    ultraspherical_fourierBochner_productTopology_null_no_strong_source_limit
      lam alpha hlam ha
  have hsub :
      Tendsto (fun n : ℕ =>
        (⟨ultraspherical_fourierBochner_function lam (u n),
          ⟨u n, rfl⟩⟩ :
          Set.range (ultraspherical_fourierBochner_function lam)))
        atTop (nhds (ultraspherical_fourierBochner_rangeZero
          lam alpha hlam ha)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [ultraspherical_fourierBochner_rangeZero, Subtype.coe_mk]
      using hFourier
  have hrec :
      Tendsto (fun n : ℕ =>
        r ⟨ultraspherical_fourierBochner_function lam (u n),
          ⟨u n, rfl⟩⟩) atTop
        (nhds (r (ultraspherical_fourierBochner_rangeZero
          lam alpha hlam ha))) := by
    have hc := hcont.tendsto.comp hsub
    simpa only [Function.comp_def] using hc
  have hsrc :
      (fun n : ℕ =>
        r ⟨ultraspherical_fourierBochner_function lam (u n),
          ⟨u n, rfl⟩⟩) = u := by
    funext n
    exact hleft (u n)
  rw [hsrc] at hrec
  exact hnostrong _ hrec

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_function_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_not_isEmbedding
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_rangeZero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_range_inverse_not_continuousAt_zero

end GegenbauerFock.GeneralUltrasphericalFock
