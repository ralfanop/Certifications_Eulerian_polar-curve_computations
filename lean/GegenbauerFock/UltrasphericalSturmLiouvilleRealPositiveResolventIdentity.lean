import GegenbauerFock.UltrasphericalSturmLiouvilleRealPositiveShiftEquiv

/-!
# V007 — exact two-parameter resolvent identity on genuine polynomial L²

For λ>0 and all positive shifts t,s>0, the previously kernel-certified
real-linear automorphisms tI-A and sI-A of the genuine weighted-L²
polynomial domain have exact inverses R_t, R_s.

This module proves the actual Hilbert polynomial-core resolvent identity:
  R_t f - R_s f = (s-t) R_t (R_s f).

Unlike a purely formal identity, both inverse maps are defined by
the exact certified finite-polynomial solutions on the actual
L² polynomial-image subspace.

This is not yet an everywhere-defined bounded full-Hilbert resolvent.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev D (lam : ℝ) (hlam : 0 < lam) :=
  sturmRealPolynomialDomain lam hlam

/-- Exact positive shifted polynomial-domain inverse as a real-linear map. -/
noncomputable def sturmRealDomainPositiveResolvent
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    D lam hlam →ₗ[ℝ] D lam hlam :=
  (sturmRealDomainPositiveShiftEquiv lam t hlam ht).symm.toLinearMap

/-- The resolvent solves the positive shifted equation exactly,
on the true weighted-real-L² polynomial domain. -/
theorem sturmRealDomainPositiveShift_resolvent
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : D lam hlam) :
    sturmRealDomainPositiveShift lam t hlam
      (sturmRealDomainPositiveResolvent lam t hlam ht f) = f := by
  exact (sturmRealDomainPositiveShiftEquiv lam t hlam ht).apply_symm_apply f

/-- Difference of two shifts is the scalar identity on the actual
polynomial Hilbert domain, for arbitrary real t,s. -/
theorem sturmRealDomainPositiveShift_sub
    (lam t s : ℝ) (hlam : 0 < lam) (x : D lam hlam) :
    sturmRealDomainPositiveShift lam t hlam x -
      sturmRealDomainPositiveShift lam s hlam x =
        (t-s) • x := by
  change (t • x - sturmRealDomainLinear lam hlam x) -
    (s • x - sturmRealDomainLinear lam hlam x) = (t-s) • x
  calc
    (t • x - sturmRealDomainLinear lam hlam x) -
        (s • x - sturmRealDomainLinear lam hlam x) =
      t • x - s • x := by abel
    _ = (t-s) • x := (sub_smul t s x).symm

/-- The exact second resolvent identity
R_t - R_s = (s-t) R_t R_s for every positive pair t,s
on the actual weighted-L² polynomial domain. -/
theorem sturmRealDomainPositiveResolvent_difference
    (lam t s : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (hs : 0 < s) (f : D lam hlam) :
    sturmRealDomainPositiveResolvent lam t hlam ht f -
      sturmRealDomainPositiveResolvent lam s hlam hs f =
        (s-t) • sturmRealDomainPositiveResolvent lam t hlam ht
          (sturmRealDomainPositiveResolvent lam s hlam hs f) := by
  let Rt := sturmRealDomainPositiveResolvent lam t hlam ht
  let Rs := sturmRealDomainPositiveResolvent lam s hlam hs
  let At := sturmRealDomainPositiveShift lam t hlam
  let As := sturmRealDomainPositiveShift lam s hlam
  have htf : At (Rt f) = f :=
    sturmRealDomainPositiveShift_resolvent lam t hlam ht f
  have hsf : As (Rs f) = f :=
    sturmRealDomainPositiveShift_resolvent lam s hlam hs f
  have hts : At (Rs f) - As (Rs f) = (t-s) • Rs f :=
    sturmRealDomainPositiveShift_sub lam t s hlam (Rs f)
  have hAtRs : At (Rs f) = f + (t-s) • Rs f := by
    rw [hsf] at hts
    apply eq_of_sub_eq_zero
    calc
      At (Rs f) - (f + (t-s) • Rs f) =
        (At (Rs f) - f) - (t-s) • Rs f := by abel
      _ = 0 := sub_eq_zero.mpr hts
  have htd : At (Rt f - Rs f) = (s-t) • Rs f := by
    rw [map_sub, htf, hAtRs]
    have hst : (s-t) • Rs f = -((t-s) • Rs f) := by
      rw [show s - t = -(t-s) by ring]
      simp
    rw [hst]
    abel
  have htr : At ((s-t) • Rt (Rs f)) = (s-t) • Rs f := by
    rw [map_smul, sturmRealDomainPositiveShift_resolvent lam t hlam ht]
  exact (sturmRealDomainPositiveShift_injective lam t hlam ht) (htd.trans htr.symm)

#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainPositiveShift_resolvent
#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainPositiveShift_sub
#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainPositiveResolvent_difference

end GegenbauerFock.Ultraspherical
