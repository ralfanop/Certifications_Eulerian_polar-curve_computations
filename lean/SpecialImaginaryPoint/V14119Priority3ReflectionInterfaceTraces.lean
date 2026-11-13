import Mathlib

/-!
# Manuscripts 14–15 — exact reflection interface matching conditions

We isolate the pointwise jet algebra underlying the proposed unitary reflection
map from L²(0,2) to L²(0,1) ⊕ L²(0,1):

  U f(t) = ((f(t)-f(2-t))/sqrt(2),
            (f(t)+f(2-t))/sqrt(2)), 0<t<1.

Writing g for the antisymmetric component and h for the symmetric one,
the inverse has left and right branches

  f(t) = (g(t)+h(t))/sqrt(2)            (t<1)
  f(t) = (h(2-t)-g(2-t))/sqrt(2)        (t>1).

The one-sided VALUE traces agree at t=1 iff g(1)=0.
The one-sided FIRST-DERIVATIVE traces agree iff h'(1)=0.

These are *necessary algebraic interface identities*. They are not yet a
construction of the unitary on actual L² equivalence classes, an H² gluing
theorem, or proof of equality of domains of unbounded Laplacians. Those
analytic obligations remain open. No novel-mathematics claim is made.
-/

noncomputable section

namespace Manuscript14Priority3.ReflectionInterfaceTraces

/-- An abstract nonzero normalizer allows reuse with the genuine
complex square-root-of-two normalizer without hiding denominators. -/
def leftValue (c g h : ℂ) : ℂ := (g + h) / c

def rightValue (c g h : ℂ) : ℂ := (h - g) / c

def leftDerivative (c dg dh : ℂ) : ℂ := (dg + dh) / c

def rightDerivative (c dg dh : ℂ) : ℂ := (dg - dh) / c

/-- The reflected branches have equal values at their common
endpoint exactly when the antisymmetric component has zero trace. -/
theorem value_match_iff (c g h : ℂ) (hc : c ≠ 0) :
    leftValue c g h = rightValue c g h ↔ g = 0 := by
  unfold leftValue rightValue
  constructor
  · intro he
    have he' : g + h = h - g := (mul_right_cancel₀ hc ((div_eq_div_iff hc hc).mp he))
    linear_combination (1 / 2 : ℂ) * he'
  · intro hg
    simp [hg]

/-- The reflected branches have equal first derivatives at t=1
exactly when the symmetric component satisfies the Neumann trace. -/
theorem derivative_match_iff (c dg dh : ℂ) (hc : c ≠ 0) :
    leftDerivative c dg dh = rightDerivative c dg dh ↔ dh = 0 := by
  unfold leftDerivative rightDerivative
  constructor
  · intro he
    have he' : dg + dh = dg - dh := (mul_right_cancel₀ hc ((div_eq_div_iff hc hc).mp he))
    linear_combination (1 / 2 : ℂ) * he'
  · intro hh
    simp [hh]

/-- The complete value-and-first-derivative interface matching
criterion, i.e. the exact scalar boundary condition required by
the eventual H² reflection gluing lemma. -/
theorem interface_jet_match_iff
    (c g h dg dh : ℂ) (hc : c ≠ 0) :
    (leftValue c g h = rightValue c g h ∧
     leftDerivative c dg dh = rightDerivative c dg dh) ↔
      (g = 0 ∧ dh = 0) := by
  simp only [value_match_iff c g h hc, derivative_match_iff c dg dh hc]

/-- For the genuine inverse reflection map, g(0)=h(0)=0
implies Dirichlet boundary values at the endpoints t=0, t=2. -/
theorem outer_dirichlet_of_component_traces
    (c g0 h0 : ℂ) (hg : g0 = 0) (hh : h0 = 0) :
    leftValue c g0 h0 = 0 ∧ rightValue c g0 h0 = 0 := by
  simp [leftValue, rightValue, hg, hh]

/-- Pointwise inverse to the two reflected values. This supplies
the algebraic bijection required before defining the L²-level unitary. -/
theorem reflection_values_recover_components
    (c g h : ℂ) (hc : c ≠ 0) :
    c * (leftValue c g h - rightValue c g h) / 2 = g ∧
    c * (leftValue c g h + rightValue c g h) / 2 = h := by
  unfold leftValue rightValue
  constructor
  · field_simp [hc]
    <;> ring
  · field_simp [hc]
    <;> ring

/-- Pointwise inverse for the derivative jets, including the
reflection sign on the right-hand branch. -/
theorem reflection_derivatives_recover_components
    (c dg dh : ℂ) (hc : c ≠ 0) :
    c * (leftDerivative c dg dh + rightDerivative c dg dh) / 2 = dg ∧
    c * (leftDerivative c dg dh - rightDerivative c dg dh) / 2 = dh := by
  unfold leftDerivative rightDerivative
  constructor
  · field_simp [hc]
    <;> ring
  · field_simp [hc]
    <;> ring


/-- The reflected second derivative has no sign reversal, unlike the
first derivative. This is the pointwise differential expression
underlying the desired intertwining of negative Laplacians. -/
def leftSecondDerivative (c ddg ddh : ℂ) : ℂ := (ddg + ddh) / c

def rightSecondDerivative (c ddg ddh : ℂ) : ℂ := (ddh - ddg) / c

/-- Algebraic intertwining of the second derivative with reflection:
taking minus the second derivative commutes with the two-branch
reconstruction, provided the second-derivative jets exist. -/
theorem reflection_second_derivative_intertwining
    (c ddg ddh : ℂ) :
    leftSecondDerivative c (-ddg) (-ddh) =
      -leftSecondDerivative c ddg ddh ∧
    rightSecondDerivative c (-ddg) (-ddh) =
      -rightSecondDerivative c ddg ddh := by
  constructor
  · unfold leftSecondDerivative
    ring
  · unfold rightSecondDerivative
    ring

/-- Recover the two component second derivatives from the reflected
branches. This is the algebraic inverse of the differential expression,
not yet a statement about unbounded-operator domains. -/
theorem reflection_second_derivatives_recover_components
    (c ddg ddh : ℂ) (hc : c ≠ 0) :
    c * (leftSecondDerivative c ddg ddh -
      rightSecondDerivative c ddg ddh) / 2 = ddg ∧
    c * (leftSecondDerivative c ddg ddh +
      rightSecondDerivative c ddg ddh) / 2 = ddh := by
  unfold leftSecondDerivative rightSecondDerivative
  constructor
  · field_simp [hc]
    <;> ring
  · field_simp [hc]
    <;> ring

/-- The bilinear polarization identity for the reflection transform.
Integrating this identity after the measure-preserving change of variable
t ↦ 2-t is the algebraic core of the real L² inner-product proof.
This theorem does not claim the analytic change-of-variables step. -/
theorem reflection_polarization_real (a b x y : ℝ) :
    (a - b) * (x - y) + (a + b) * (x + y) =
      2 * (a * x + b * y) := by
  ring

/-- The normalized transform preserves pointwise quadratic energy
when the square of the real normalizer equals two. This version
makes the normalization hypothesis explicit rather than assuming
an arbitrary nonzero denominator has the correct magnitude. -/
theorem reflection_normalized_energy_real
    (c a b : ℝ) (hc : c ^ 2 = 2) :
    ((a - b) / c) ^ 2 + ((a + b) / c) ^ 2 =
      a ^ 2 + b ^ 2 := by
  rw [div_pow, div_pow, ← add_div, hc]
  apply (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  ring

/-- The corresponding derivative-energy identity, with the
opposite sign on the derivative of the reflected right branch. -/
theorem reflection_derivative_energy_real (a b : ℝ) :
    (a + b) ^ 2 + (a - b) ^ 2 =
      2 * (a ^ 2 + b ^ 2) := by
  ring

/-- The elementary real pointwise energy identity behind the
normalization by sqrt(2), *not* an L² isometry proof. -/
theorem reflection_parallelogram_real (a b : ℝ) :
    (a - b) ^ 2 + (a + b) ^ 2 = 2 * (a ^ 2 + b ^ 2) := by
  ring

#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.value_match_iff
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.derivative_match_iff
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.interface_jet_match_iff
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.outer_dirichlet_of_component_traces
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.reflection_values_recover_components
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.reflection_derivatives_recover_components
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.reflection_second_derivative_intertwining
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.reflection_second_derivatives_recover_components
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.reflection_polarization_real
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.reflection_normalized_energy_real
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.reflection_derivative_energy_real
#print axioms Manuscript14Priority3.ReflectionInterfaceTraces.reflection_parallelogram_real

end Manuscript14Priority3.ReflectionInterfaceTraces
