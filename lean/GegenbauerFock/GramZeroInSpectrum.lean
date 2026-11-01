import GegenbauerFock.GramApproximateZeroSpectrum
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — zero belongs to the spectrum of the genuine source Gram

The source Gram G=C†C has a normalized approximate-zero-eigenvector
sequence although the zero eigenspace is trivial (by the previously
kernel-certified Gram theorem). If G were a unit in the Banach algebra
of bounded endomorphisms, its bounded inverse would force those unit
vectors to converge strongly to zero. Therefore zero lies in the
operator spectrum, not in the point spectrum.

The proof refers to the genuine ultraspherical L² Gram, never a finite
Gram matrix nor a surrogate sequence operator.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem gram_zero_mem_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ spectrum ℂ (gram lam alpha hlam ha) := by
  apply spectrum.zero_mem ℂ
  intro hunit
  have hbij : Function.Bijective (gram lam alpha hlam ha) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have hker : (gram lam alpha hlam ha).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hbij.1
  have hrange : (gram lam alpha hlam ha).range = ⊤ :=
    LinearMap.range_eq_top.mpr hbij.2
  let e := ContinuousLinearEquiv.ofBijective
    (gram lam alpha hlam ha) hker hrange
  obtain ⟨u, hunitvec, hgram⟩ :=
    gram_exists_unit_approximate_zero_eigenvectors
      lam alpha hlam ha
  have hconv_inv : Tendsto
      (fun n : ℕ => e.symm (gram lam alpha hlam ha (u n)))
      atTop (nhds (e.symm (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) :=
    e.symm.continuous.continuousAt.tendsto.comp hgram
  have hfun : (fun n : ℕ => e.symm (gram lam alpha hlam ha (u n))) = u := by
    funext n
    exact e.symm_apply_apply (u n)
  rw [hfun] at hconv_inv
  have hezero : e.symm (0 : Lp ℂ 2 (Ultraspherical.measure lam)) = 0 :=
    map_zero e.symm
  rw [hezero] at hconv_inv
  have hnormzero : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (0 : ℝ)) := by
    simpa using hconv_inv.norm
  have hnormone : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (1 : ℝ)) := by
    have heq : (fun n : ℕ => ‖u n‖) = (fun _ : ℕ => (1 : ℝ)) :=
      funext hunitvec
    rw [heq]
    exact tendsto_const_nhds
  have himpossible : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hnormzero hnormone
  norm_num at himpossible

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_zero_mem_spectrum

end GegenbauerFock.GeneralUltrasphericalFock
