import GegenbauerFock.TwoSidedGramFredholmSpectralOpenness
import GegenbauerFock.TwoSidedGramResolventFredholmIndexZero
import GegenbauerFock.TwoSidedGramNegativeResolvent
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# V007 — zero Fredholm index at every nonzero bilateral Gram spectral shift

A key strengthening of the nonzero-shift Fredholm certificates:
since the punctured complex plane is connected, and the Fredholm
index is locally constant, a Fredholm shift T - mu I at any nonzero
complex mu has the same index as the invertible shift T + I.
Consequently that index is zero even when mu is a genuine isolated
Gram eigenvalue of positive finite multiplicity.

This proof treats the actual ultraspherical source Gram and the full
Gaussian Fock coefficient output Gram separately, and does not assume
they act on the same Hilbert space.

The source is only a candidate until the pinned Lean CI kernel and
#print axioms checks have succeeded without forbidden axioms.
-/

noncomputable section

open MeasureTheory Module End Filter Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- If every nonzero spectral shift on a complex Hilbert space is
Fredholm and -1 is a resolvent parameter, all those shifts have
Fredholm index zero, including their nonzero eigenvalues. -/
private theorem fredholmShift_index_zero_on_punctured_plane
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (hfred : ∀ mu : ℂ, mu ≠ 0 →
      ContinuousLinearMap.IsFredholm
        (T - mu • (1 : H →L[ℂ] H)))
    (hneg : (-1 : ℂ) ∈ resolventSet ℂ T)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (T - mu • (1 : H →L[ℂ] H)).index = 0 := by
  let f : ℂ → ℤ := fun z =>
    (T - z • (1 : H →L[ℂ] H)).index
  have hcontinuous : ContinuousOn f ({(0 : ℂ)}ᶜ) := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hloc : ∀ᶠ w : ℂ in 𝓝 z, f w = f z := by
      filter_upwards [fredholmShift_index_locally_constant_in_parameter
        T z (hfred z hz0)] with w hw
      exact hw.2
    exact Filter.Tendsto.congr' hloc.symm tendsto_const_nhds
  have hconnected : IsPreconnected ({(0 : ℂ)}ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (0 : ℂ)).isPreconnected
  have hdiscrete : IsDiscrete (Set.univ : Set ℤ) :=
    isDiscrete_univ_iff.mpr inferInstance
  have hmuS : mu ∈ (Set.singleton (0 : ℂ))ᶜ := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmu
  have hnegS : (-1 : ℂ) ∈ ({(0 : ℂ)} : Set ℂ)ᶜ := by norm_num
  have hconst : f mu = f (-1) :=
    hconnected.constant_of_mapsTo hdiscrete hcontinuous
      (by intro z hz; simp) hmuS hnegS
  have hnegIndex :
      (T - (-1 : ℂ) • (1 : H →L[ℂ] H)).index = 0 :=
    fredholmShift_index_zero_of_mem_resolvent T (-1) hneg
  exact hconst.trans hnegIndex

/-- Every nonzero source Gram spectral shift has exactly zero Fredholm
index, including nonzero eigenvalues as well as resolvent points. -/
theorem sourceGram_nonzero_shift_fredholm_index_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))).index = 0 := by
  apply fredholmShift_index_zero_on_punctured_plane
    (gram lam alpha hlam ha)
    (fun z hz => sourceGram_nonzero_shift_isFredholm lam alpha hlam ha z hz)
    (by simpa using
      (source_gram_negative_real_mem_resolventSet
        lam alpha hlam ha 1 (by norm_num)))
    mu hmu

/-- The identical zero-index conclusion holds for the full Gaussian
Fock coefficient output Gram, without identifying the Hilbert spaces. -/
theorem outputGram_nonzero_shift_fredholm_index_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)).index = 0 := by
  apply fredholmShift_index_zero_on_punctured_plane
    (outputGram lam alpha hlam ha)
    (fun z hz => outputGram_nonzero_shift_isFredholm lam alpha hlam ha z hz)
    (by simpa using
      (output_gram_negative_real_mem_resolventSet
        lam alpha hlam ha 1 (by norm_num)))
    mu hmu

/-- At each nonzero complex spectral parameter both genuine Grams
have Fredholm shifts of index zero, whether or not the parameter is
an eigenvalue. This is a bilateral zero-index Riesz–Schauder theorem. -/
theorem two_sided_gram_nonzero_shifts_fredholm_index_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))).IsFredholm ∧
    (gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))).index = 0 ∧
    (outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)).IsFredholm ∧
    (outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)).index = 0 :=
  ⟨sourceGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu,
    sourceGram_nonzero_shift_fredholm_index_zero lam alpha hlam ha mu hmu,
    outputGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu,
    outputGram_nonzero_shift_fredholm_index_zero lam alpha hlam ha mu hmu⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_nonzero_shift_fredholm_index_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_shift_fredholm_index_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_shifts_fredholm_index_zero

end GegenbauerFock.GeneralUltrasphericalFock
