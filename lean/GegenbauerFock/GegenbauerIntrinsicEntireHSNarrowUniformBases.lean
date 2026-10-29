import GegenbauerFock.GegenbauerIntrinsicEntireHSNarrowGaussianDivergence
import GegenbauerFock.GegenbauerIntrinsicEntireHSRealGammaIntegral
import Mathlib.Topology.Order.LeftRightNhds

/-!
# V007 — uniform all-basis high-energy threshold as Gaussian width shrinks

At fixed ultraspherical λ>0, the real right-hand limit α↓0 of
the actual unregularized Kummer energy is +∞. Consequently, each
prescribed finite real threshold admits a single sufficiently narrow
positive Gaussian scale that works for EVERY complete source Hilbert
basis, both for the genuine analytic Gaussian Fock S₂ energy and for
the true intrinsic source-Gram diagonal trace.

This turns a scalar filter-level asymptotic into a full uniform
Hilbert-basis statement without silently identifying different
Gaussian target Hilbert spaces.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.KummerCoefficients

/-- Every real energy threshold is eventually exceeded by the
unregularized Kummer mass throughout a punctured right neighborhood
of zero Gaussian width. -/
theorem kummer_gaussianScale_above_uniform_threshold
    (lam : ℝ) (hlam : 0 < lam) (bound : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ alpha : ℝ,
      0 < alpha → alpha < delta →
        bound ≤ kummerSeries lam (1 / (4 * alpha)) := by
  have hlim := kummerSeries_gaussianScale_tendsto_atTop lam hlam
  have hlarge :
      {alpha : ℝ | bound ≤ kummerSeries lam (1 / (4 * alpha))} ∈
        (𝓝[>] (0 : ℝ)) := hlim.eventually_ge_atTop bound
  obtain ⟨delta, hdelta, hsubset⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hlarge
  refine ⟨delta, hdelta, ?_⟩
  intro alpha ha hlt
  exact hsubset ⟨ha, hlt⟩

#print axioms GegenbauerFock.KummerCoefficients.kummer_gaussianScale_above_uniform_threshold

end GegenbauerFock.KummerCoefficients

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For any finite prescribed threshold, every sufficiently narrow
positive Gaussian scale yields squared analytic-Fock HS energy at
least that threshold, simultaneously for ALL source Hilbert bases. -/
theorem C_intrinsicEntire_HS_narrow_above_uniform_bases
    (lam : ℝ) (hlam : 0 < lam) (bound : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ alpha : ℝ,
      0 < alpha → alpha < delta →
        ∀ {ι : Type*}
          (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))),
          bound ≤ ∑' i : ι,
            ‖C_intrinsicEntire lam alpha hlam (by assumption) (b i)‖ ^ 2 := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    KummerCoefficients.kummer_gaussianScale_above_uniform_threshold
      lam hlam bound
  refine ⟨delta, hdelta, ?_⟩
  intro alpha ha hlt ι b
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b]
  exact hbound alpha ha hlt

/-- The analogous all-basis unboundedness statement for the real
Hilbert diagonal trace of the actual intrinsic Gaussian source Gram. -/
theorem C_intrinsicEntire_Gram_narrow_above_uniform_bases
    (lam : ℝ) (hlam : 0 < lam) (bound : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ alpha : ℝ,
      0 < alpha → alpha < delta →
        ∀ {ι : Type*}
          (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))),
          bound ≤ ∑' i : ι,
            RCLike.re (inner ℂ
              (C_intrinsicEntire_gram lam alpha hlam (by assumption) (b i)) (b i)) := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    KummerCoefficients.kummer_gaussianScale_above_uniform_threshold
      lam hlam bound
  refine ⟨delta, hdelta, ?_⟩
  intro alpha ha hlt ι b
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha hlam ha b]
  exact hbound alpha ha hlt

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_narrow_above_uniform_bases
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_narrow_above_uniform_bases

end GegenbauerFock.GeneralUltrasphericalFock
