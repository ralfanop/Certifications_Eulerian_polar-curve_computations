import Mathlib.LinearAlgebra.Vandermonde

/-!
# V007 — exact finite coherent Vandermonde separation

The finite power moments of pairwise distinct complex nodes separate
all complex coefficient vectors. The conjugate-node version is the
algebraic bridge needed for linear independence of Gaussian coherent
vectors from their normalized Fock coordinates.
-/

noncomputable section

namespace GegenbauerFock.GaussianArea

/-- Finite power moments at distinct complex nodes uniquely determine
all coefficients. -/
theorem finite_vandermonde_moments_zero_coefficients
    (n : ℕ) (z c : Fin n → ℂ)
    (hz : Function.Injective z)
    (hmom : ∀ k : Fin n,
      ∑ i : Fin n, c i * z i ^ (k : ℕ) = 0) :
    ∀ i : Fin n, c i = 0 := by
  have hc : c = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := z) (v := c) hz hmom
  intro i
  exact congrFun hc i

/-- Complex conjugation preserves the distinctness of Gaussian
coherent nodes, and therefore their finite Vandermonde moments. -/
theorem finite_conjugate_vandermonde_moments_zero_coefficients
    (n : ℕ) (z c : Fin n → ℂ)
    (hz : Function.Injective z)
    (hmom : ∀ k : Fin n,
      ∑ i : Fin n, c i * (star (z i)) ^ (k : ℕ) = 0) :
    ∀ i : Fin n, c i = 0 := by
  have hstar : Function.Injective (fun i : Fin n => star (z i)) := by
    intro i j hij
    apply hz
    have h := congrArg star hij
    simpa using h
  exact finite_vandermonde_moments_zero_coefficients
    n (fun i => star (z i)) c hstar hmom

#print axioms GegenbauerFock.GaussianArea.finite_vandermonde_moments_zero_coefficients
#print axioms GegenbauerFock.GaussianArea.finite_conjugate_vandermonde_moments_zero_coefficients

end GegenbauerFock.GaussianArea
