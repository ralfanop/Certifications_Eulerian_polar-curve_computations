import GegenbauerFock.UltrasphericalPolynomialKernel

/-!
# V007 — exact complex polynomial realization in ultraspherical L²

Every complex polynomial determines an actual element of the weighted
L²(ν_λ) complex monomial span. The element is *not* a symbolic or
finite-matrix surrogate: its representative equals the polynomial's
ordinary complex evaluation almost everywhere under the concrete
Beta-pushforward ultraspherical probability measure.

These exact algebraic bridges are prerequisites for using uniform
Weierstrass approximation to prove unconditional density in L².
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The actual weighted L² element associated with a complex
polynomial, expressed in terms of the already constructed genuine
Riesz monomials. -/
noncomputable def sourcePolynomial (lam : ℝ) (hlam : 0 < lam)
    (P : Polynomial ℂ) :
    Lp ℂ 2 (Ultraspherical.measure lam) :=
  ∑ n ∈ P.support, P.coeff n • sourceMonomial lam hlam n

/-- Complex polynomial evaluation belongs to the actual closed
Fock source monomial span, without any density assumption. -/
theorem sourcePolynomial_mem_span (lam : ℝ) (hlam : 0 < lam)
    (P : Polynomial ℂ) :
    sourcePolynomial lam hlam P ∈ sourceMonomialSpan lam hlam := by
  classical
  unfold sourcePolynomial
  apply Submodule.sum_mem
  intro n hn
  exact (sourceMonomialSpan lam hlam).smul_mem (P.coeff n)
    (Submodule.subset_span (Set.mem_range_self n))

/-- Almost-everywhere identification of each source monomial with
the corresponding ordinary complex power on the real support. -/
theorem sourceMonomial_ae_eval (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    (sourceMonomial lam hlam n : ℝ → ℂ) =ᵐ[Ultraspherical.measure lam]
      (fun u : ℝ => (u : ℂ) ^ n) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  change
    ((WeightedMoments.monomial
      (Ultraspherical.measure lam) (ae_abs_le_one lam) n :
        Lp ℂ 2 (Ultraspherical.measure lam)) : ℝ → ℂ)
      =ᵐ[Ultraspherical.measure lam] (fun u : ℝ => (u : ℂ) ^ n)
  exact (WeightedMoments.monomial_memLp
    (Ultraspherical.measure lam) (ae_abs_le_one lam) n).coeFn_toLp

/-- The L² polynomial vector genuinely represents P.eval on the
real line, almost everywhere for ν_λ. This is the key exact
identification needed before transferring Stone-Weierstrass density. -/
theorem sourcePolynomial_ae_eval
    (lam : ℝ) (hlam : 0 < lam) (P : Polynomial ℂ) :
    (sourcePolynomial lam hlam P : ℝ → ℂ) =ᵐ[Ultraspherical.measure lam]
      (fun u : ℝ => P.eval (u : ℂ)) := by
  classical
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  have hterm (n : ℕ) :
      ((P.coeff n • sourceMonomial lam hlam n :
          Lp ℂ 2 (Ultraspherical.measure lam)) : ℝ → ℂ)
        =ᵐ[Ultraspherical.measure lam]
          (fun u : ℝ => P.coeff n * (u : ℂ) ^ n) := by
    filter_upwards
      [Lp.coeFn_smul (P.coeff n) (sourceMonomial lam hlam n),
       sourceMonomial_ae_eval lam hlam n] with u hs hm
    simpa only [Pi.smul_apply, smul_eq_mul, hm] using hs
  have hsum := Lp.coeFn_finsetSum P.support
    (fun n : ℕ => (P.coeff n • sourceMonomial lam hlam n :
      Lp ℂ 2 (Ultraspherical.measure lam)))
  have hall : ∀ᵐ u ∂Ultraspherical.measure lam,
      ∀ n ∈ P.support,
        ((P.coeff n • sourceMonomial lam hlam n :
          Lp ℂ 2 (Ultraspherical.measure lam)) : ℝ → ℂ) u =
          P.coeff n * (u : ℂ) ^ n :=
    (Filter.eventually_all_finset P.support).mpr (fun n _ => hterm n)
  filter_upwards [hsum, hall] with u hsu hu
  change (sourcePolynomial lam hlam P : ℝ → ℂ) u =
    P.eval (u : ℂ)
  calc
    (sourcePolynomial lam hlam P : ℝ → ℂ) u =
        ∑ n ∈ P.support,
          ((P.coeff n • sourceMonomial lam hlam n :
            Lp ℂ 2 (Ultraspherical.measure lam)) : ℝ → ℂ) u := by
          simpa only [sourcePolynomial, Finset.sum_apply] using hsu
    _ = ∑ n ∈ P.support, P.coeff n * (u : ℂ) ^ n := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hu n hn
    _ = P.eval (u : ℂ) := by
          simp only [Polynomial.eval_eq_sum, Polynomial.sum]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourcePolynomial_mem_span
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceMonomial_ae_eval
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourcePolynomial_ae_eval

end GegenbauerFock.GeneralUltrasphericalFock
