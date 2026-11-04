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

end Manuscript14Gram
