import GegenbauerFock.UltrasphericalSturmLiouvilleMomentIntegrability

/-!
# V007 — genuine real polynomial vectors in weighted ultraspherical L²

Every real monomial belongs to L² for the actual symmetric
Beta-pushforward ultraspherical probability measure (λ>0).
The finite polynomial coefficient sum therefore defines a genuine
real Hilbert L² vector. The representative is proven equal almost
everywhere to ordinary polynomial evaluation.

This construction alone does not assert polynomial evaluation is
injective modulo almost-everywhere equality, or that the resulting
differential operator is closed/self-adjoint.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory
open Polynomial

/-- Every ordinary real monomial has an actual weighted L² class. -/
theorem sturmRealMonomial_memLp
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    MemLp (fun u : ℝ => u ^ n) 2 (measure lam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  have hc : Continuous (fun u : ℝ => u ^ n) := by fun_prop
  apply MemLp.of_bound hc.aestronglyMeasurable 1
  filter_upwards [ae_mem_unit_interval lam] with u hu
  have hbound : |u| ≤ (1 : ℝ) := abs_le.mpr ⟨hu.1, hu.2⟩
  calc
    ‖u ^ n‖ = |u| ^ n := by simp
    _ ≤ (1 : ℝ) ^ n := by gcongr
    _ = 1 := by simp

/-- The genuine real L² Riesz-monomial vector. -/
noncomputable def sturmRealMonomialLp
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Lp ℝ 2 (measure lam) :=
  (sturmRealMonomial_memLp lam hlam n).toLp
    (fun u : ℝ => u ^ n)

theorem sturmRealMonomialLp_ae_eval
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    (sturmRealMonomialLp lam hlam n : ℝ → ℝ)
      =ᵐ[measure lam] (fun u : ℝ => u ^ n) := by
  exact (sturmRealMonomial_memLp lam hlam n).coeFn_toLp

/-- Finite support realization of a real polynomial in true L². -/
noncomputable def sturmRealPolynomialLp
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    Lp ℝ 2 (measure lam) :=
  ∑ n ∈ p.support, p.coeff n • sturmRealMonomialLp lam hlam n

/-- This actual L² vector represents ordinary polynomial evaluation
almost everywhere under the genuine ultraspherical law. -/
theorem sturmRealPolynomialLp_ae_eval
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    (sturmRealPolynomialLp lam hlam p : ℝ → ℝ)
      =ᵐ[measure lam] (fun u : ℝ => p.eval u) := by
  classical
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  have hterm (n : ℕ) :
      ((p.coeff n • sturmRealMonomialLp lam hlam n :
          Lp ℝ 2 (measure lam)) : ℝ → ℝ)
        =ᵐ[measure lam] (fun u : ℝ => p.coeff n * u ^ n) := by
    filter_upwards
      [Lp.coeFn_smul (p.coeff n) (sturmRealMonomialLp lam hlam n),
       sturmRealMonomialLp_ae_eval lam hlam n] with u hs hm
    simpa only [Pi.smul_apply, smul_eq_mul, hm] using hs
  have hsum := Lp.coeFn_finsetSum p.support
    (fun n : ℕ => (p.coeff n • sturmRealMonomialLp lam hlam n :
      Lp ℝ 2 (measure lam)))
  have hall : ∀ᵐ u ∂measure lam, ∀ n ∈ p.support,
      ((p.coeff n • sturmRealMonomialLp lam hlam n :
          Lp ℝ 2 (measure lam)) : ℝ → ℝ) u =
        p.coeff n * u ^ n :=
    (Filter.eventually_all_finset p.support).mpr (fun n _ => hterm n)
  filter_upwards [hsum, hall] with u hsu hu
  change (sturmRealPolynomialLp lam hlam p : ℝ → ℝ) u = p.eval u
  calc
    (sturmRealPolynomialLp lam hlam p : ℝ → ℝ) u =
        ∑ n ∈ p.support,
          ((p.coeff n • sturmRealMonomialLp lam hlam n :
              Lp ℝ 2 (measure lam)) : ℝ → ℝ) u := by
        simpa only [sturmRealPolynomialLp, Finset.sum_apply] using hsu
    _ = ∑ n ∈ p.support, p.coeff n * u ^ n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hu n hn
    _ = p.eval u := by
        simp only [Polynomial.eval_eq_sum, Polynomial.sum]

#print axioms GegenbauerFock.Ultraspherical.sturmRealMonomial_memLp
#print axioms GegenbauerFock.Ultraspherical.sturmRealMonomialLp_ae_eval
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_ae_eval

end GegenbauerFock.Ultraspherical
