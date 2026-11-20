import Mathlib

/-!
# M12 §9: complex fourth-order algebra for the critical window

This module certifies the exact polynomial identities underlying the local
Taylor expansion of the standardized uniform moment generating function.
It does NOT assert that the analytic remainder is controlled; that step
remains a separate obligation.
-/

namespace M12QuarticComplex

/-- The degree-four Taylor polynomial of sinh(√3 z)/(√3 z). -/
def mgfTaylor4 (z : ℂ) : ℂ :=
  1 + z^2 / 2 + (3 / 40 : ℂ) * z^4

/-- The degree-four Taylor polynomial of its analytic logarithm. -/
def logTaylor4 (z : ℂ) : ℂ :=
  z^2 / 2 - z^4 / 20

/-- Formal exponentiation of the logarithmic jet reproduces the MGF jet
up to an explicit polynomial remainder of order six. -/
theorem exponential_jet_identity (z : ℂ) :
    1 + logTaylor4 z + (logTaylor4 z)^2 / 2 =
      mgfTaylor4 z - z^6 / 40 + z^8 / 800 := by
  unfold logTaylor4 mgfTaylor4
  ring

/-- Quartic cumulant coefficient for the variance-one uniform law. -/
theorem cumulant_four (variance fourthMoment : ℝ)
    (hv : variance = 1) (hm : fourthMoment = 9/5) :
    fourthMoment - 3 * variance^2 = -6/5 := by
  rw [hv, hm]
  norm_num

/-- Algebraic cancellation of the quadratic mode at the critical value. -/
theorem critical_quadratic_cancellation (z : ℂ) :
    (1/2 : ℂ) * z^2 - (1/12 : ℂ) * (6*z^2) = 0 := by
  ring

end M12QuarticComplex

#print axioms M12QuarticComplex.exponential_jet_identity
#print axioms M12QuarticComplex.cumulant_four
#print axioms M12QuarticComplex.critical_quadratic_cancellation
