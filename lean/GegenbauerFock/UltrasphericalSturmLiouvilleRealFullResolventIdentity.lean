import GegenbauerFock.UltrasphericalSturmLiouvilleRealPositiveResolventFullCLM

/-!
# V007 — exact two-shift resolvent identity on the full real Hilbert space

For all lambda > 0 and t,s > 0 the true weighted real L²
resolvent is the unique bounded extension of the exact polynomial
inverse. The already certified polynomial resolvent identity
transfers to EVERY source vector by density and continuity.

The result is an exact full-space equality, not a finite section
or a formal manipulation of unbounded operators.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev D (lam : ℝ) (hlam : 0 < lam) :=
  sturmRealPolynomialDomain lam hlam

/-- The genuine bounded full-real-L² positive resolvents obey the
second resolvent identity for all strictly positive t,s. -/
theorem sturmRealPositiveResolventFullCLM_difference
    (lam t s : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hs : 0 < s)
    (f : H lam) :
    sturmRealPositiveResolventFullCLM lam t hlam ht f -
      sturmRealPositiveResolventFullCLM lam s hlam hs f =
      (s-t) • sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmRealPositiveResolventFullCLM lam s hlam hs f) := by
  let Rt := sturmRealPositiveResolventFullCLM lam t hlam ht
  let Rs := sturmRealPositiveResolventFullCLM lam s hlam hs
  have hcont : Continuous
      (fun z : H lam => Rt z - Rs z - (s-t) • Rt (Rs z)) := by
    fun_prop
  have hclosed : IsClosed
      {z : H lam | Rt z - Rs z - (s-t) • Rt (Rs z) = 0} :=
    isClosed_eq hcont continuous_const
  have hcore :
      (D lam hlam : Set (H lam)) ⊆
        {z : H lam | Rt z - Rs z - (s-t) • Rt (Rs z) = 0} := by
    intro z hz
    let q : D lam hlam := ⟨z, hz⟩
    have hrt : Rt (q : H lam) =
        (sturmRealDomainPositiveResolvent lam t hlam ht q : H lam) :=
      sturmRealPositiveResolventFullCLM_onCore lam t hlam ht q
    have hrs : Rs (q : H lam) =
        (sturmRealDomainPositiveResolvent lam s hlam hs q : H lam) :=
      sturmRealPositiveResolventFullCLM_onCore lam s hlam hs q
    have hrts : Rt (Rs (q : H lam)) =
        (sturmRealDomainPositiveResolvent lam t hlam ht
          (sturmRealDomainPositiveResolvent lam s hlam hs q) : H lam) := by
      rw [hrs]
      exact sturmRealPositiveResolventFullCLM_onCore lam t hlam ht
        (sturmRealDomainPositiveResolvent lam s hlam hs q)
    change Rt (q : H lam) - Rs (q : H lam) -
      (s-t) • Rt (Rs (q : H lam)) = 0
    rw [hrts, hrt, hrs]
    have hpoly := congrArg Subtype.val
      (sturmRealDomainPositiveResolvent_difference lam t s hlam ht hs q)
    have heq :
        (sturmRealDomainPositiveResolvent lam t hlam ht q : H lam) -
        (sturmRealDomainPositiveResolvent lam s hlam hs q : H lam) =
        (s-t) •
          (sturmRealDomainPositiveResolvent lam t hlam ht
            (sturmRealDomainPositiveResolvent lam s hlam hs q) : H lam) := by
      simpa only [Submodule.coe_sub, Submodule.coe_smul] using hpoly
    exact sub_eq_zero.mpr heq
  have hdense : Dense (D lam hlam : Set (H lam)) :=
    sturmRealPolynomialDomain_dense_set lam hlam
  have hall := closure_minimal hcore hclosed
  exact sub_eq_zero.mp (hall (hdense f))

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_difference

end GegenbauerFock.Ultraspherical
