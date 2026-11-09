import SpecialImaginaryPoint.DirichletFiniteDeterminant
import SpecialImaginaryPoint.Section67ScalarCertificate

/-!
# Manuscript 14.119 — Priority 3: finite/infinite spectral determinant bridge

This module identifies the actual finite Dirichlet matrix products with
the infinite Euler product appearing in Proposition 6.2. The convergence is
proved from the exact sine Euler product already certified in the
Section67ScalarCertificate module, NOT from numerical samples.

We deliberately call the infinite quantity a spectral product: no
zeta-regularised determinant of an unbounded Sturm–Liouville operator or
abstract trace-class Fredholm determinant is defined or identified here.
The zeta/Fredholm operator identification is the next proof obligation.
-/

open Filter Topology

namespace Manuscript14Priority3

/-- The explicit nonzero Dirichlet spectral factor equals the factor in
the Euler product for sinh, at spectral shift t=x². -/
theorem dirichlet_factor_sq (n : ℕ) (x : ℝ) :
    Manuscript14Dirichlet.factor n (x ^ 2) =
      Manuscript14Section67.sinhFac x n := by
  simp only [Manuscript14Dirichlet.factor, Manuscript14Section67.sinhFac,
    Nat.cast_add, Nat.cast_one]

/-- Every finite Fredholm-type product equals the corresponding actual
Dirichlet spectral truncation. -/
theorem finite_dirichlet_product (N : ℕ) (x : ℝ) :
    Manuscript14Dirichlet.finiteFredholm N (x ^ 2) =
      ∏ n ∈ Finset.range N, Manuscript14Section67.sinhFac x n := by
  unfold Manuscript14Dirichlet.finiteFredholm
  exact Finset.prod_congr rfl (fun n _ => dirichlet_factor_sq n x)

/-- The convergent product of positive-shifted Dirichlet spectral factors.
This is a spectral product, NOT by definition a zeta determinant. -/
noncomputable def spectralProduct (t : ℝ) : ℝ :=
  ∏' n : ℕ, Manuscript14Dirichlet.factor n t

/-- Analytic convergence of the genuine Dirichlet finite spectral products,
without truncation errors, for each nonzero real x. -/
theorem finite_dirichlet_product_tendsto (x : ℝ) (hx : x ≠ 0) :
    Tendsto
      (fun N : ℕ => Manuscript14Dirichlet.finiteFredholm N (x ^ 2))
      atTop (𝓝 (Real.sinh x / x)) := by
  have hconv :
      Tendsto (fun N : ℕ =>
        ∏ n ∈ Finset.range N, Manuscript14Section67.sinhFac x n)
        atTop (𝓝 (Real.sinh x / x)) :=
    (Manuscript14Section67.multipliable_sinhFac x).hasProd_iff_tendsto_nat.mp
      (Manuscript14Section67.hasProd_sinh x hx)
  have hfun :
      (fun N : ℕ => Manuscript14Dirichlet.finiteFredholm N (x ^ 2)) =
      (fun N : ℕ =>
        ∏ n ∈ Finset.range N, Manuscript14Section67.sinhFac x n) := by
    funext N
    exact finite_dirichlet_product N x
  rw [hfun]
  exact hconv

/-- The infinite Dirichlet spectral product is the exact hyperbolic
sine quotient (the scalar part of Proposition 6.2). -/
theorem spectralProduct_sq (x : ℝ) (hx : x ≠ 0) :
    spectralProduct (x ^ 2) = Real.sinh x / x := by
  have hfun :
      (fun n : ℕ => Manuscript14Dirichlet.factor n (x ^ 2)) =
        Manuscript14Section67.sinhFac x := by
    funext n
    exact dirichlet_factor_sq n x
  unfold spectralProduct
  rw [hfun]
  exact (Manuscript14Section67.hasProd_sinh x hx).tprod_eq

#print axioms Manuscript14Priority3.dirichlet_factor_sq
#print axioms Manuscript14Priority3.finite_dirichlet_product
#print axioms Manuscript14Priority3.finite_dirichlet_product_tendsto
#print axioms Manuscript14Priority3.spectralProduct_sq

end Manuscript14Priority3
