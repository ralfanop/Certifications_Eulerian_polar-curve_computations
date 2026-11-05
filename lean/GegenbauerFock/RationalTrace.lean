import Mathlib

/-!
# V007: exact rational arithmetic certificate for a Fock trace-series truncation

At ultraspherical parameter λ=1/2 and Fock parameter α=1, the scalar
integral (1/2)∫_{-1}^1 exp(u²/4) du has the Taylor series
  Σ_{n≥0} 1/(4^n n! (2n+1)).
This file checks the *finite rational sum* through n=14 exactly.
A separate analytic proof of the Taylor remainder bound gives the
full scalar-integral enclosure. It is not yet a Lean certificate of
the infinite series or of the Hilbert–Schmidt operator norm identity.
-/

namespace GegenbauerFock.RationalTrace

def term (n : ℕ) : ℚ :=
  1 / ((4 : ℚ) ^ n * (Nat.factorial n : ℚ) * (((2*n+1 : ℕ) : ℚ)))

def tracePartialSum (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, term n

/-- Exact rational, not a floating point approximation. -/
theorem partial_fifteen :
    tracePartialSum 15 =
      (337212679483569969430703669 : ℚ) /
        309376751206532288348160000 := by
  norm_num [tracePartialSum, term, Finset.sum_range_succ]

/-- Exact rational upper endpoint after adding the proved-on-paper
Taylor majorant (4/3)*4^(-15)/15!. The inequality connecting the
infinite sum to this endpoint is still to be formalized. -/
theorem partial_fifteen_plus_bound :
    tracePartialSum 15 + (1 : ℚ) / 1053078495820775424000 =
      (142666902858433448605421999 : ℚ) /
        130890163971994429685760000 := by
  rw [partial_fifteen]
  norm_num

#print axioms GegenbauerFock.RationalTrace.partial_fifteen
#print axioms GegenbauerFock.RationalTrace.partial_fifteen_plus_bound

end GegenbauerFock.RationalTrace
