import GegenbauerFock.UltrasphericalPolynomialDensityReduction
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# V007: complex Stone–Weierstrass on the actual ultraspherical support

Real Weierstrass approximates the real and imaginary parts of a
complex-valued bounded continuous function separately. The two real
polynomials are mapped by ℝ[X] → ℂ[X] and combined into one complex
polynomial. The resulting bound is on the actual support [-1,1],
without changing the underlying ultraspherical probability measure.

The density reduction in the imported module then proves unconditional
complex-monomial density and injectivity of the concrete C operator.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory
open scoped Polynomial

/-- Complex polynomials uniformly approximate every bounded complex
continuous function on [-1,1], with explicitly positive error. -/
theorem complexWeierstrass_unit_interval
    (f : BoundedContinuousFunction ℝ ℂ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ P : Polynomial ℂ,
      ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        ‖f u - P.eval (u : ℂ)‖ < eps := by
  have hcontinuousRe :
      ContinuousOn (fun u : ℝ => (f u).re) (Set.Icc (-1 : ℝ) 1) := by
    fun_prop
  have hcontinuousIm :
      ContinuousOn (fun u : ℝ => (f u).im) (Set.Icc (-1 : ℝ) 1) := by
    fun_prop
  obtain ⟨pRe, hpRe⟩ :=
    exists_polynomial_near_of_continuousOn (-1 : ℝ) 1
      (fun u => (f u).re) hcontinuousRe (eps / 4) (by positivity)
  obtain ⟨pIm, hpIm⟩ :=
    exists_polynomial_near_of_continuousOn (-1 : ℝ) 1
      (fun u => (f u).im) hcontinuousIm (eps / 4) (by positivity)
  let P : Polynomial ℂ :=
    pRe.map (algebraMap ℝ ℂ) +
      Polynomial.C Complex.I * pIm.map (algebraMap ℝ ℂ)
  refine ⟨P, ?_⟩
  intro u hu
  have hmap (q : Polynomial ℝ) :
      (q.map (algebraMap ℝ ℂ)).eval (u : ℂ) =
        ((Polynomial.eval u q : ℝ) : ℂ) := by
    simpa only [Polynomial.eval_map, Complex.coe_algebraMap] using
      (Polynomial.eval₂_hom (p := q) (f := algebraMap ℝ ℂ) u)
  have hP :
      P.eval (u : ℂ) =
        ((Polynomial.eval u pRe : ℝ) : ℂ) + Complex.I * ((Polynomial.eval u pIm : ℝ) : ℂ) := by
    dsimp [P]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      hmap]
  have hre :
      (f u - P.eval (u : ℂ)).re =
        (f u).re - Polynomial.eval u pRe := by
    rw [hP]
    simp
  have him :
      (f u - P.eval (u : ℂ)).im =
        (f u).im - Polynomial.eval u pIm := by
    rw [hP]
    simp
  have hreal : |(f u - P.eval (u : ℂ)).re| < eps / 4 := by
    rw [hre, abs_sub_comm]
    exact hpRe u hu
  have himag : |(f u - P.eval (u : ℂ)).im| < eps / 4 := by
    rw [him, abs_sub_comm]
    exact hpIm u hu
  calc
    ‖f u - P.eval (u : ℂ)‖ ≤
        |(f u - P.eval (u : ℂ)).re| +
          |(f u - P.eval (u : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ < eps := by linarith

/-- Unconditional polynomial density in the true ultraspherical
L²(ν_λ) source: no density assumption is passed to this theorem. -/
theorem sourceMonomialSpan_dense
    (lam : ℝ) (hlam : 0 < lam) :
    (sourceMonomialSpan lam hlam).topologicalClosure = ⊤ := by
  exact sourceMonomialSpan_dense_of_complexWeierstrass
    lam hlam complexWeierstrass_unit_interval

/-- INCONDITIONAL injectivity of the original Gegenbauer–Fock bounded
operator L²(ν_λ) → ℓ², for ALL λ>0 and α>0. -/
theorem C_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (C lam alpha hlam ha) := by
  exact C_injective_of_monomialSpan_dense
    lam alpha hlam ha (sourceMonomialSpan_dense lam hlam)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.complexWeierstrass_unit_interval
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceMonomialSpan_dense
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_injective

end GegenbauerFock.GeneralUltrasphericalFock
