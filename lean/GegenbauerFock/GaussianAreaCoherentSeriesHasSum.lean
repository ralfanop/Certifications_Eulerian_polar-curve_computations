import GegenbauerFock.GaussianAreaFinitePolynomialEvaluation
import GegenbauerFock.OutputComplexHolomorphy

/-!
# V007 — the same normalized Fock series converges in L² and pointwise

For arbitrary square-summable coefficients, the true Gaussian L²
synthesis and the entire coherent evaluation are separately the
respective sums of precisely the SAME normalized polynomial terms.

The L² and scalar HasSum statements are both unconditional. Their
identification as a.e. representatives (which requires uniqueness
of limits in measure or an equivalent theorem) is NOT asserted here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- For each complex argument the normalized Gaussian monomial
series of an arbitrary ℓ² vector converges to the actual coherent
Fock evaluation. This is a HasSum statement, not just a formal tsum. -/
theorem coefficientFockEvaluation_hasSum_normalizedMonomial
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) (z : ℂ) :
    HasSum (fun n : ℕ => a n * normalizedMonomial alpha n z)
      (FockEvaluation.evaluation alpha ha z a) := by
  have hs : Summable (fun n : ℕ =>
      inner ℂ (FockEvaluation.kernelCoordinate alpha z n) (a n)) := by
    simpa only [show ∀ n : ℕ,
        (FockEvaluation.kernelVector alpha ha z) n =
          FockEvaluation.kernelCoordinate alpha z n from fun _ => rfl] using
      (lp.summable_inner (FockEvaluation.kernelVector alpha ha z) a)
  have hsum : HasSum (fun n : ℕ =>
      inner ℂ (FockEvaluation.kernelCoordinate alpha z n) (a n))
      (FockEvaluation.evaluation alpha ha z a) := by
    rw [FockEvaluation.evaluation_eq_tsum_inner alpha ha z a]
    exact hs.hasSum
  have hterm : (fun n : ℕ => a n * normalizedMonomial alpha n z) =
      (fun n : ℕ =>
        inner ℂ (FockEvaluation.kernelCoordinate alpha z n) (a n)) := by
    funext n
    rw [FockEvaluation.inner_kernelCoordinate_eq_monomial]
    simp [normalizedMonomial, monomialWeight, mul_comm]
  rw [hterm]
  exact hsum

/-- The actual Hilbert L² synthesis and entire coherent evaluation
are sums of the same Gaussian-normalized monomials, respectively in
the L² topology and pointwise in the complex plane. This theorem
does not claim that the two limits are equal almost everywhere. -/
theorem coefficientSynthesisL2_and_coherent_hasSum
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    HasSum (fun n : ℕ =>
        a n • normalizedMonomialL2Vector alpha ha n)
      (coefficientSynthesisL2 alpha ha a) ∧
    (∀ z : ℂ, HasSum (fun n : ℕ =>
        a n * normalizedMonomial alpha n z)
      (FockEvaluation.evaluation alpha ha z a)) := by
  exact ⟨coefficientSynthesisL2_hasSum alpha ha a,
    coefficientFockEvaluation_hasSum_normalizedMonomial alpha ha a⟩

#print axioms GegenbauerFock.GaussianArea.coefficientFockEvaluation_hasSum_normalizedMonomial
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_and_coherent_hasSum

end GegenbauerFock.GaussianArea
