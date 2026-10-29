import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialL2
import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialExpansion

/-!
# V007 — true real-linear polynomial evaluation in weighted L²

The previously certified genuine finite-sum polynomial vector is
proved to be additive and homogeneous, using almost-everywhere
polynomial evaluation in the concrete ultraspherical measure.

This is not yet an injectivity theorem or a closed operator domain.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

theorem sturmRealPolynomialLp_add
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    sturmRealPolynomialLp lam hlam (p + q) =
      sturmRealPolynomialLp lam hlam p +
        sturmRealPolynomialLp lam hlam q := by
  apply Lp.ext
  filter_upwards
    [sturmRealPolynomialLp_ae_eval lam hlam (p + q),
     sturmRealPolynomialLp_ae_eval lam hlam p,
     sturmRealPolynomialLp_ae_eval lam hlam q,
     Lp.coeFn_add (sturmRealPolynomialLp lam hlam p)
       (sturmRealPolynomialLp lam hlam q)]
    with u hpq hp hq hadd
  rw [hpq, hadd, Pi.add_apply, hp, hq]
  simp

theorem sturmRealPolynomialLp_smul
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (p : ℝ[X]) :
    sturmRealPolynomialLp lam hlam (c • p) =
      c • sturmRealPolynomialLp lam hlam p := by
  apply Lp.ext
  filter_upwards
    [sturmRealPolynomialLp_ae_eval lam hlam (c • p),
     sturmRealPolynomialLp_ae_eval lam hlam p,
     Lp.coeFn_smul c (sturmRealPolynomialLp lam hlam p)]
    with u hcp hp hsmul
  rw [hcp, hsmul, Pi.smul_apply, hp]
  simp

/-- True real-polynomial evaluation in L² of the genuine
Beta-pushforward measure, with a certified linear-map structure. -/
noncomputable def sturmRealPolynomialLinear
    (lam : ℝ) (hlam : 0 < lam) :
    ℝ[X] →ₗ[ℝ] Lp ℝ 2 (measure lam) where
  toFun := sturmRealPolynomialLp lam hlam
  map_add' := sturmRealPolynomialLp_add lam hlam
  map_smul' := sturmRealPolynomialLp_smul lam hlam

@[simp] theorem sturmRealPolynomialLinear_apply
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    sturmRealPolynomialLinear lam hlam p =
      sturmRealPolynomialLp lam hlam p := rfl

/-- The candidate dense domain is the image of the genuine polynomial
evaluation linear map, not an abstract Hilbert-space surrogate. -/
noncomputable def sturmRealPolynomialDomain
    (lam : ℝ) (hlam : 0 < lam) :
    Submodule ℝ (Lp ℝ 2 (measure lam)) :=
  LinearMap.range (sturmRealPolynomialLinear lam hlam)

theorem sturmRealPolynomialLp_mem_domain
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    sturmRealPolynomialLp lam hlam p ∈
      sturmRealPolynomialDomain lam hlam := by
  exact ⟨p, rfl⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_add
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_smul
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_mem_domain

end GegenbauerFock.Ultraspherical
