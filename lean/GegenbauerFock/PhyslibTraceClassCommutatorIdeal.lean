import GegenbauerFock.PhyslibTraceClassGeneralFinite
import GegenbauerFock.PhyslibTraceClassTwoSidedIdeal

/-!
# V007 — general S₁ commutator and finite bounded-sandwich algebra

A genuine, possibly non-selfadjoint, CFC-trace-class endomorphism is
stable under commutators with arbitrary bounded operators, and under
any finite number of nested commutators. More generally finite sums
of independently bounded left/right multiples remain trace class.

The proofs use the separately kernel-checked *unrestricted* S₁
additive closure and two-sided ideal membership. No positivity,
finite-rank, commutativity or specific Gegenbauer–Fock kernel
hypothesis occurs. The result is only membership: the quantitative
norm bounds and Banach completeness are separate obligations.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Arbitrary bounded commutators preserve the genuine CFC S₁ ideal. -/
theorem isTraceClass_commutator
    (A T : H →L[ℂ] H) (hT : IsTraceClass T) :
    IsTraceClass (A * T - T * A) := by
  exact isTraceClass_sub_general (A * T) (T * A)
    (isTraceClass_mul_left T hT A)
    (isTraceClass_mul_right T hT A)

/-- Successive commutators with A, without any operator-norm
convergence assumption. This definition is purely algebraic. -/
def iteratedCommutator (A T : H →L[ℂ] H) : ℕ → (H →L[ℂ] H)
  | 0 => T
  | n + 1 =>
      A * iteratedCommutator A T n -
        iteratedCommutator A T n * A

@[simp] theorem iteratedCommutator_zero (A T : H →L[ℂ] H) :
    iteratedCommutator A T 0 = T := rfl

@[simp] theorem iteratedCommutator_succ (A T : H →L[ℂ] H)
    (n : ℕ) :
    iteratedCommutator A T (n + 1) =
      A * iteratedCommutator A T n -
        iteratedCommutator A T n * A := rfl

/-- Any number of nested bounded commutators stays in S₁. -/
theorem isTraceClass_iteratedCommutator
    (A T : H →L[ℂ] H) (hT : IsTraceClass T) :
    ∀ n : ℕ, IsTraceClass (iteratedCommutator A T n) := by
  intro n
  induction n with
  | zero => exact hT
  | succ n ih => exact isTraceClass_commutator A _ ih

/-- Finite sums of independently bounded sandwiches of actual S₁
operators are again in the unrestricted CFC trace class. -/
theorem isTraceClass_finset_sandwich_sum
    {ι : Type*} (s : Finset ι)
    (T A B : ι → H →L[ℂ] H)
    (hT : ∀ i ∈ s, IsTraceClass (T i)) :
    IsTraceClass (∑ i ∈ s, A i * T i * B i) := by
  exact isTraceClass_finset_sum_general s
    (fun i => A i * T i * B i)
    (fun i hi => isTraceClass_twoSided
      (T i) (hT i hi) (A i) (B i))

/-- Every finite partial sum of a two-sided bounded conjugation
orbit of T remains S₁. No infinite Neumann/commutator series claim. -/
theorem isTraceClass_sandwich_power_partial_sum
    (A B T : H →L[ℂ] H) (hT : IsTraceClass T)
    (n : ℕ) :
    IsTraceClass
      (∑ k ∈ Finset.range n, (A ^ k) * T * (B ^ k)) := by
  exact isTraceClass_finset_sandwich_sum
    (Finset.range n) (fun _ => T)
    (fun k => A ^ k) (fun k => B ^ k)
    (fun _ _ => hT)

#print axioms ProbabilisticTheory.isTraceClass_commutator
#print axioms ProbabilisticTheory.iteratedCommutator_zero
#print axioms ProbabilisticTheory.iteratedCommutator_succ
#print axioms ProbabilisticTheory.isTraceClass_iteratedCommutator
#print axioms ProbabilisticTheory.isTraceClass_finset_sandwich_sum
#print axioms ProbabilisticTheory.isTraceClass_sandwich_power_partial_sum

end ProbabilisticTheory
