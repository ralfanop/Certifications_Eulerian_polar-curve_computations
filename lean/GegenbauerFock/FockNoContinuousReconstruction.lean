import GegenbauerFock.FockApproximateNullNoStrongLimit

/-!
# V007 — no globally continuous reconstruction of the compact Fock map

A globally defined reconstruction r satisfying r (C f) = f for
every L² source cannot be continuous at zero, even if r is nonlinear.
The proof uses the certified normalized approximate-null sequence.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem C_no_continuous_global_left_inverse_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (r : InfiniteAnalysis.FockCoefficients →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r (C lam alpha hlam ha f) = f) :
    ¬ ContinuousAt r (0 : InfiniteAnalysis.FockCoefficients) := by
  intro hcont
  obtain ⟨u, _hunit, himage, hnostrong⟩ :=
    C_exists_approximate_null_sequence_without_strong_limit
      lam alpha hlam ha
  have hrec : Tendsto
      (fun n : ℕ => r (C lam alpha hlam ha (u n)))
      atTop (nhds (r (0 : InfiniteAnalysis.FockCoefficients))) :=
    hcont.tendsto.comp himage
  have hsequence :
      (fun n : ℕ => r (C lam alpha hlam ha (u n))) = u := by
    funext n
    exact hleft (u n)
  rw [hsequence] at hrec
  exact hnostrong (r 0) hrec

theorem C_no_continuous_global_reconstruction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ ∃ r : InfiniteAnalysis.FockCoefficients →
        Lp ℂ 2 (Ultraspherical.measure lam),
      Continuous r ∧
        (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
          r (C lam alpha hlam ha f) = f) := by
  rintro ⟨r, hcont, hleft⟩
  exact C_no_continuous_global_left_inverse_at_zero
    lam alpha hlam ha r hleft hcont.continuousAt

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_no_continuous_global_left_inverse_at_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_no_continuous_global_reconstruction

end GegenbauerFock.GeneralUltrasphericalFock
