import Mathlib

/-!
# V007 — exact pointwise spheroidal differential balance of the exponential kernel

With the nonnegative Gegenbauer Sturm differential expression
  D_λ f = -(1-u²) f'' + (2λ+1)u f'
and its bounded spheroidal potential -c² u², the kernel
  K_c(u,v) = exp(cuv)
is bispectral: applying the differential expression in u or v
gives identical pointwise real values.

We certify actual first and second derivatives of the exponential,
not just polynomial expressions standing in for derivatives.

**Scope:** Pointwise real differentiable kernel identity only.
The closed unbounded-operator commutator additionally needs source-domain
invariance, weighted integration by parts, and boundary conditions.
-/

noncomputable section

namespace GegenbauerFock.Spheroidal

/-- The real two-variable exponential Gram kernel. -/
def kernel (c u v : ℝ) : ℝ := Real.exp (c * u * v)

theorem kernel_symm (c u v : ℝ) : kernel c u v = kernel c v u := by
  unfold kernel
  congr 1
  ring

private theorem kernel_hasDerivAt_left (c u v : ℝ) :
    HasDerivAt (fun t : ℝ => kernel c t v)
      ((c * v) * kernel c u v) u := by
  have hlinear : HasDerivAt (fun t : ℝ => c * t * v) (c * v) u := by
    have h : HasDerivAt (fun t : ℝ => (c * v) * t) (c * v) u := by
      simpa using (hasDerivAt_id u).const_mul (c * v)
    convert h using 1
    funext t
    ring
  have hExp := (Real.hasDerivAt_exp (c * u * v)).comp u hlinear
  change HasDerivAt (Real.exp ∘ (fun t : ℝ => c * t * v))
    ((c * v) * Real.exp (c * u * v)) u
  convert hExp using 1 <;> ring

/-- First partial derivative in the first variable of the real kernel. -/
theorem kernel_deriv_left (c u v : ℝ) :
    deriv (fun t : ℝ => kernel c t v) u =
      (c * v) * kernel c u v :=
  (kernel_hasDerivAt_left c u v).deriv

/-- Second partial derivative in the first variable of the real kernel. -/
theorem kernel_second_deriv_left (c u v : ℝ) :
    deriv (fun t : ℝ => deriv (fun r : ℝ => kernel c r v) t) u =
      ((c * v) ^ 2) * kernel c u v := by
  have hfirst :
      (fun t : ℝ => deriv (fun r : ℝ => kernel c r v) t) =
      (fun t : ℝ => (c * v) * kernel c t v) := by
    funext t
    exact kernel_deriv_left c t v
  rw [hfirst]
  have h := (kernel_hasDerivAt_left c u v).const_mul (c * v)
  convert h.deriv using 1 <;> ring

/-- First partial derivative in the second variable. -/
theorem kernel_deriv_right (c u v : ℝ) :
    deriv (fun t : ℝ => kernel c u t) v =
      (c * u) * kernel c u v := by
  have heq : (fun t : ℝ => kernel c u t) =
      (fun t : ℝ => kernel c t u) := by
    funext t
    exact kernel_symm c u t
  rw [heq, kernel_deriv_left, kernel_symm c v u]

/-- Second partial derivative in the second variable. -/
theorem kernel_second_deriv_right (c u v : ℝ) :
    deriv (fun t : ℝ => deriv (fun r : ℝ => kernel c u r) t) v =
      ((c * u) ^ 2) * kernel c u v := by
  have heq : (fun r : ℝ => kernel c u r) =
      (fun r : ℝ => kernel c r u) := by
    funext r
    exact kernel_symm c u r
  rw [heq, kernel_second_deriv_left, kernel_symm c v u]

/-- The actual spheroidal expression in u, including the negative
Sturm second-derivative sign and the negative quadratic potential. -/
def spheroidalLeft (lam c u v : ℝ) : ℝ :=
  -(1 - u ^ 2) *
      deriv (fun t : ℝ => deriv (fun r : ℝ => kernel c r v) t) u +
    (2 * lam + 1) * u * deriv (fun t : ℝ => kernel c t v) u -
    c ^ 2 * u ^ 2 * kernel c u v

/-- The same differential expression in v. -/
def spheroidalRight (lam c u v : ℝ) : ℝ :=
  -(1 - v ^ 2) *
      deriv (fun t : ℝ => deriv (fun r : ℝ => kernel c u r) t) v +
    (2 * lam + 1) * v * deriv (fun t : ℝ => kernel c u t) v -
    c ^ 2 * v ^ 2 * kernel c u v

/-- V007 §6 pointwise bispectral balance, with true derivatives:
the two differential expressions coincide at every real u,v,λ,c. -/
theorem spheroidal_exponential_pointwise_bispectral
    (lam c u v : ℝ) :
    spheroidalLeft lam c u v = spheroidalRight lam c u v := by
  unfold spheroidalLeft spheroidalRight
  rw [kernel_second_deriv_left, kernel_deriv_left,
    kernel_second_deriv_right, kernel_deriv_right]
  ring

#print axioms GegenbauerFock.Spheroidal.kernel_deriv_left
#print axioms GegenbauerFock.Spheroidal.kernel_second_deriv_left
#print axioms GegenbauerFock.Spheroidal.kernel_deriv_right
#print axioms GegenbauerFock.Spheroidal.kernel_second_deriv_right
#print axioms GegenbauerFock.Spheroidal.spheroidal_exponential_pointwise_bispectral

end GegenbauerFock.Spheroidal
