import Mathlib

/-!
# Manuscript 14.1, Section 6 — bispectral Gram-kernel identities

For Kₐ(u,v)=exp(a*u*v), the second-order expression
  Aₐ = -(1-u²) ∂²ᵤ + 2u∂ᵤ - a²u²
balances in the u and v variables. This module formalizes the exact
kernel algebra, boundary-flux vanishing, and a general closed-graph
limit mechanism. It does NOT yet construct the integral operator,
its trace-class structure, or identify the graph core of the
specific Gegenbauer spectral operator.
-/

namespace Manuscript14Gram

noncomputable def gramKernel (a u v : ℂ) : ℂ :=
  Complex.exp (a * u * v)

/-- The scalar multiplier of Kₐ produced by the u-side differential expression. -/
def gramDifferentialSymbol (a u v : ℂ) : ℂ :=
  -(1 - u ^ 2) * (a * v) ^ 2 + 2 * u * (a * v) - a ^ 2 * u ^ 2

/-- The exact bispectral polynomial balance for every complex parameter. -/
theorem gram_differential_symbol_symmetric (a u v : ℂ) :
    gramDifferentialSymbol a u v = gramDifferentialSymbol a v u := by
  unfold gramDifferentialSymbol
  ring

/-- The Gram kernel is symmetric under interchange of source coordinates. -/
theorem gram_kernel_symmetric (a u v : ℂ) :
    gramKernel a u v = gramKernel a v u := by
  unfold gramKernel
  congr 1
  ring

/-- Kernel-side bispectral balance, before integration by parts. -/
theorem gram_bispectral_kernel_balance (a u v : ℂ) :
    gramDifferentialSymbol a u v * gramKernel a u v =
      gramDifferentialSymbol a v u * gramKernel a v u := by
  calc
    gramDifferentialSymbol a u v * gramKernel a u v =
        gramDifferentialSymbol a v u * gramKernel a u v := by
      rw [gram_differential_symbol_symmetric]
    _ = gramDifferentialSymbol a v u * gramKernel a v u := by
      rw [gram_kernel_symmetric]

/-- The Legendre boundary factor annihilates the exponential-flux
term at u=1, for every complex source coordinate and parameter. -/
theorem gram_endpoint_flux_plus (a v : ℂ) :
    (1 - (1 : ℂ) ^ 2) * (a * v) * gramKernel a 1 v = 0 := by
  ring

/-- The same endpoint cancellation at u=-1. -/
theorem gram_endpoint_flux_minus (a v : ℂ) :
    (1 - (-1 : ℂ) ^ 2) * (a * v) * gramKernel a (-1) v = 0 := by
  ring

#print axioms Manuscript14Gram.gram_differential_symbol_symmetric
#print axioms Manuscript14Gram.gram_kernel_symmetric
#print axioms Manuscript14Gram.gram_bispectral_kernel_balance
#print axioms Manuscript14Gram.gram_endpoint_flux_plus
#print axioms Manuscript14Gram.gram_endpoint_flux_minus


/-!
## Closed-domain graph-core transport

This abstract theorem isolates precisely the functional-analytic step used
in Theorem 6.1 of Manuscript 14.1: a bounded operator S commuting on a
graph core with a closed operator A commutes on the entire closed domain.

An operator is represented by its domain D and total extension A to allow
the unbounded expression A : D → H without a Lean partial-function axiom.
This theorem has genuine domain preservation, but it is conditional on the
core density and concrete commutation hypotheses for the Legendre kernel.
-/

/-- Commutation on a graph core extends to the closed operator's whole domain.
The statement does not posit that S maps the whole Hilbert space into D. -/
theorem closed_graph_core_commutation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D Core : Set E) (A : E → E) (S : E →L[ℂ] E)
    (hcore : ∀ f ∈ D, ∃ p : ℕ → E,
      (∀ n, p n ∈ Core) ∧
      Filter.Tendsto p Filter.atTop (nhds f) ∧
      Filter.Tendsto (fun n => A (p n)) Filter.atTop (nhds (A f)))
    (hclosed : ∀ x y : E,
      (∃ p : ℕ → E,
        (∀ n, p n ∈ D) ∧
        Filter.Tendsto p Filter.atTop (nhds x) ∧
        Filter.Tendsto (fun n => A (p n)) Filter.atTop (nhds y)) →
      x ∈ D ∧ A x = y)
    (hCoreD : Core ⊆ D)
    (hcomm : ∀ p ∈ Core, S p ∈ D ∧ A (S p) = S (A p)) :
    ∀ f ∈ D, S f ∈ D ∧ A (S f) = S (A f) := by
  intro f hf
  obtain ⟨p, hpCore, hp, hAp⟩ := hcore f hf
  have hSpD : ∀ n, S (p n) ∈ D := by
    intro n
    exact (hcomm (p n) (hpCore n)).1
  have hSp : Filter.Tendsto (fun n => S (p n)) Filter.atTop
      (nhds (S f)) :=
    S.continuous.continuousAt.tendsto.comp hp
  have hSAp : Filter.Tendsto (fun n => S (A (p n))) Filter.atTop
      (nhds (S (A f))) :=
    S.continuous.continuousAt.tendsto.comp hAp
  have hASp : Filter.Tendsto (fun n => A (S (p n))) Filter.atTop
      (nhds (S (A f))) := by
    have hfun : (fun n => A (S (p n))) =
        (fun n => S (A (p n))) := by
      funext n
      exact (hcomm (p n) (hpCore n)).2
    rw [hfun]
    exact hSAp
  exact hclosed (S f) (S (A f))
    ⟨fun n => S (p n), hSpD, hSp, hASp⟩

#print axioms Manuscript14Gram.closed_graph_core_commutation


/-- A bounded perturbation does not destroy graph-core approximation.
Here `A` is the unbounded spectral operator and `B` the bounded
quadratic multiplier; the domain remains `D`. -/
theorem bounded_perturbation_preserves_graph_core
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D Core : Set E) (A : E → E) (B : E →L[ℂ] E)
    (hcore : ∀ f ∈ D, ∃ p : ℕ → E,
      (∀ n, p n ∈ Core) ∧
      Filter.Tendsto p Filter.atTop (nhds f) ∧
      Filter.Tendsto (fun n => A (p n)) Filter.atTop (nhds (A f))) :
    ∀ f ∈ D, ∃ p : ℕ → E,
      (∀ n, p n ∈ Core) ∧
      Filter.Tendsto p Filter.atTop (nhds f) ∧
      Filter.Tendsto (fun n => A (p n) + B (p n))
        Filter.atTop (nhds (A f + B f)) := by
  intro f hf
  obtain ⟨p, hpCore, hp, hAp⟩ := hcore f hf
  refine ⟨p, hpCore, hp, ?_⟩
  have hBp : Filter.Tendsto (fun n => B (p n)) Filter.atTop
      (nhds (B f)) :=
    B.continuous.continuousAt.tendsto.comp hp
  exact hAp.add hBp

/-- The graph of A+B remains sequentially closed when A is sequentially
closed and B is bounded, with no change of domain. -/
theorem bounded_perturbation_preserves_sequential_closed_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set E) (A : E → E) (B : E →L[ℂ] E)
    (hclosedA : ∀ x y : E,
      (∃ p : ℕ → E,
        (∀ n, p n ∈ D) ∧
        Filter.Tendsto p Filter.atTop (nhds x) ∧
        Filter.Tendsto (fun n => A (p n)) Filter.atTop (nhds y)) →
      x ∈ D ∧ A x = y) :
    ∀ x y : E,
      (∃ p : ℕ → E,
        (∀ n, p n ∈ D) ∧
        Filter.Tendsto p Filter.atTop (nhds x) ∧
        Filter.Tendsto (fun n => A (p n) + B (p n))
          Filter.atTop (nhds y)) →
      x ∈ D ∧ A x + B x = y := by
  intro x y hxy
  obtain ⟨p, hpD, hp, hpAB⟩ := hxy
  have hBp : Filter.Tendsto (fun n => B (p n)) Filter.atTop
      (nhds (B x)) :=
    B.continuous.continuousAt.tendsto.comp hp
  have hAp : Filter.Tendsto (fun n => A (p n)) Filter.atTop
      (nhds (y - B x)) := by
    have hdifference := hpAB.sub hBp
    have hident : (fun n => A (p n) + B (p n) - B (p n)) =
        (fun n => A (p n)) := by
      funext n
      abel
    rw [hident] at hdifference
    exact hdifference
  obtain ⟨hx, hAx⟩ := hclosedA x (y - B x)
    ⟨p, hpD, hp, hAp⟩
  refine ⟨hx, ?_⟩
  rw [hAx]
  exact sub_add_cancel y (B x)

/-- Complete abstract closed-domain commutation of a boundedly perturbed
spectral generator A+B with a bounded Gram operator S, once the
concrete polynomial-core kernel identity has been established. -/
theorem closed_bounded_perturbation_commutation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D Core : Set E) (A : E → E) (B S : E →L[ℂ] E)
    (hcore : ∀ f ∈ D, ∃ p : ℕ → E,
      (∀ n, p n ∈ Core) ∧
      Filter.Tendsto p Filter.atTop (nhds f) ∧
      Filter.Tendsto (fun n => A (p n)) Filter.atTop (nhds (A f)))
    (hclosedA : ∀ x y : E,
      (∃ p : ℕ → E,
        (∀ n, p n ∈ D) ∧
        Filter.Tendsto p Filter.atTop (nhds x) ∧
        Filter.Tendsto (fun n => A (p n)) Filter.atTop (nhds y)) →
      x ∈ D ∧ A x = y)
    (hCoreD : Core ⊆ D)
    (hcomm : ∀ p ∈ Core,
      S p ∈ D ∧ A (S p) + B (S p) = S (A p + B p)) :
    ∀ f ∈ D,
      S f ∈ D ∧ A (S f) + B (S f) = S (A f + B f) := by
  exact closed_graph_core_commutation D Core
    (fun x => A x + B x) S
    (bounded_perturbation_preserves_graph_core D Core A B hcore)
    (bounded_perturbation_preserves_sequential_closed_graph D A B hclosedA)
    hCoreD hcomm

#print axioms Manuscript14Gram.bounded_perturbation_preserves_graph_core
#print axioms Manuscript14Gram.bounded_perturbation_preserves_sequential_closed_graph
#print axioms Manuscript14Gram.closed_bounded_perturbation_commutation


/-!
## Genuine complex derivatives of the exponential Gram kernel

The following checks turn the polynomial bispectral symbol into the
actual differentiated kernel. They do not yet carry out the Green
integration-by-parts argument under the L² integral.
-/

/-- Actual first complex derivative of Kₐ(u,v) with respect to u. -/
theorem gramKernel_first_derivative (a u v : ℂ) :
    deriv (fun w : ℂ => gramKernel a w v) u =
      (a * v) * gramKernel a u v := by
  have hinner : HasDerivAt (fun w : ℂ => a * w * v) (a * v) u := by
    convert (((hasDerivAt_id u).const_mul a).mul_const v) using 1
      <;> try { funext w; simp only [id_eq] }
      <;> ring
  have h := hinner.cexp
  have hk : HasDerivAt (fun w : ℂ => gramKernel a w v)
      ((a * v) * gramKernel a u v) u := by
    convert h using 1 <;> simp [gramKernel, mul_comm]
  exact hk.deriv

/-- Actual second complex derivative of the entire Gram kernel. -/
theorem gramKernel_second_derivative (a u v : ℂ) :
    deriv (deriv (fun w : ℂ => gramKernel a w v)) u =
      (a * v) ^ 2 * gramKernel a u v := by
  have hfun : deriv (fun w : ℂ => gramKernel a w v) =
      (fun w : ℂ => (a * v) * gramKernel a w v) := by
    funext w
    exact gramKernel_first_derivative a w v
  rw [hfun]
  have hinner : HasDerivAt (fun w : ℂ => a * w * v) (a * v) u := by
    convert (((hasDerivAt_id u).const_mul a).mul_const v) using 1
      <;> try { funext w; simp only [id_eq] }
      <;> ring
  have hk : HasDerivAt (fun w : ℂ => gramKernel a w v)
      ((a * v) * gramKernel a u v) u := by
    convert hinner.cexp using 1 <;> simp [gramKernel, mul_comm]
  have hscaled := (hk.const_mul (a * v)).deriv
  convert hscaled using 1 <;> ring

/-- The genuine second-order differential expression applied to the
exponential kernel, using Mathlib derivatives rather than formal symbols. -/
noncomputable def gramKernelDifferential (a u v : ℂ) : ℂ :=
  -(1 - u ^ 2) * deriv (deriv (fun w : ℂ => gramKernel a w v)) u +
    2 * u * deriv (fun w : ℂ => gramKernel a w v) u -
    a ^ 2 * u ^ 2 * gramKernel a u v

/-- Actual differentiated-kernel expression equals the exact polynomial symbol. -/
theorem gramKernelDifferential_eq_symbol (a u v : ℂ) :
    gramKernelDifferential a u v =
      gramDifferentialSymbol a u v * gramKernel a u v := by
  rw [gramKernelDifferential, gramKernel_second_derivative, gramKernel_first_derivative]
  unfold gramDifferentialSymbol
  ring

/-- Pointwise bispectral balance after differentiating both complex variables. -/
theorem gramKernelDifferential_bispectral (a u v : ℂ) :
    gramKernelDifferential a u v = gramKernelDifferential a v u := by
  rw [gramKernelDifferential_eq_symbol, gramKernelDifferential_eq_symbol]
  exact gram_bispectral_kernel_balance a u v

#print axioms Manuscript14Gram.gramKernel_first_derivative
#print axioms Manuscript14Gram.gramKernel_second_derivative
#print axioms Manuscript14Gram.gramKernelDifferential_eq_symbol
#print axioms Manuscript14Gram.gramKernelDifferential_bispectral

end Manuscript14Gram
