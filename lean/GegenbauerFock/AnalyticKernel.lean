import Mathlib

/-!
# Gegenbauer–Fock: actual differential identities for the real exponential kernel

Unlike the pointwise polynomial identities in KernelCore.lean, this file
uses Mathlib's analytic derivative of Real.exp to prove differentiability
and explicit first and second derivatives. Its final theorem states
equality of the two differential expressions acting on exp(c*u*v).

These are pointwise analytical identities. The commutation of the
corresponding unbounded Sturm–Liouville operator with an *integral*
operator still requires a separate proof of integration by parts and
specification of operator domains.

No sorry/admit/new axioms.
-/

namespace GegenbauerFock.AnalyticKernel

/-- Real exponential kernel K_c(u,v) = exp(c*u*v). -/
noncomputable def K (c u v : ℝ) : ℝ := Real.exp (c*u*v)

theorem hasDerivAt_left (c u v : ℝ) :
    HasDerivAt (fun t : ℝ => K c t v) ((c*v)*K c u v) u := by
  have hbase : HasDerivAt (fun t : ℝ => (c*v)*t) (c*v) u := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id u).const_mul (c*v))
  have hfun : (fun t : ℝ => c*t*v) = (fun t : ℝ => (c*v)*t) := by
    funext t
    ring
  have hlin : HasDerivAt (fun t : ℝ => c*t*v) (c*v) u := by
    rw [hfun]
    exact hbase
  have hexp := (Real.hasDerivAt_exp (c*u*v)).comp u hlin
  have he : HasDerivAt (fun t : ℝ => K c t v)
      (Real.exp (c*u*v)*(c*v)) u := by
    simpa only [K, Function.comp_def] using hexp
  convert he using 1 <;> ring

theorem deriv_left (c u v : ℝ) :
    deriv (fun t : ℝ => K c t v) u = (c*v)*K c u v :=
  (hasDerivAt_left c u v).deriv

theorem hasDerivAt_right (c u v : ℝ) :
    HasDerivAt (fun t : ℝ => K c u t) ((c*u)*K c u v) v := by
  have hfun : (fun t : ℝ => K c u t) = (fun t : ℝ => K c t u) := by
    funext t
    unfold K
    congr 1
    ring
  rw [hfun]
  convert hasDerivAt_left c v u using 1 <;> unfold K <;> ring

theorem deriv_right (c u v : ℝ) :
    deriv (fun t : ℝ => K c u t) v = (c*u)*K c u v :=
  (hasDerivAt_right c u v).deriv

theorem secondDeriv_left (c u v : ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => K c s v) t) u =
      (c*v)^2*K c u v := by
  have hfun :
      (fun t : ℝ => deriv (fun s : ℝ => K c s v) t) =
      (fun t : ℝ => (c*v)*K c t v) := by
    funext t
    exact deriv_left c t v
  rw [hfun]
  have h := (hasDerivAt_left c u v).const_mul (c*v)
  convert h.deriv using 1 <;> ring

theorem secondDeriv_right (c u v : ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => K c u s) t) v =
      (c*u)^2*K c u v := by
  have hfun : (fun s : ℝ => K c u s) = (fun s : ℝ => K c s u) := by
    funext s
    unfold K
    congr 1
    ring
  rw [hfun]
  convert secondDeriv_left c v u using 1 <;> unfold K <;> ring

/--
The pointwise action of the real ultraspherical spheroidal differential
expression in the first variable.
-/
noncomputable def spheroidalLeft (lam c u v : ℝ) : ℝ :=
  -(1-u^2) * deriv (fun t : ℝ => deriv (fun s : ℝ => K c s v) t) u
    + (2*lam+1)*u * deriv (fun t : ℝ => K c t v) u
    - c^2*u^2*K c u v

/-- The same expression acting in the second variable. -/
noncomputable def spheroidalRight (lam c u v : ℝ) : ℝ :=
  -(1-v^2) * deriv (fun t : ℝ => deriv (fun s : ℝ => K c u s) t) v
    + (2*lam+1)*v * deriv (fun t : ℝ => K c u t) v
    - c^2*v^2*K c u v

theorem spheroidalLeft_formula (lam c u v : ℝ) :
    spheroidalLeft lam c u v =
      (-(1-u^2)*(c*v)^2 + (2*lam+1)*u*(c*v) - c^2*u^2) * K c u v := by
  unfold spheroidalLeft
  rw [secondDeriv_left, deriv_left]
  ring

theorem spheroidalRight_formula (lam c u v : ℝ) :
    spheroidalRight lam c u v =
      (-(1-v^2)*(c*u)^2 + (2*lam+1)*v*(c*u) - c^2*v^2) * K c u v := by
  unfold spheroidalRight
  rw [secondDeriv_right, deriv_right]
  ring

/--
Exact *analytic* pointwise intertwining-kernel equation

   L^u_{lam,c} exp(c*u*v) = L^v_{lam,c} exp(c*u*v).

This does not by itself imply the integral-operator commutation law.
-/
theorem spheroidal_kernel_differential_balance (lam c u v : ℝ) :
    spheroidalLeft lam c u v = spheroidalRight lam c u v := by
  rw [spheroidalLeft_formula, spheroidalRight_formula]
  congr 1
  ring

#print axioms GegenbauerFock.AnalyticKernel.hasDerivAt_left
#print axioms GegenbauerFock.AnalyticKernel.secondDeriv_left
#print axioms GegenbauerFock.AnalyticKernel.spheroidal_kernel_differential_balance

end GegenbauerFock.AnalyticKernel
