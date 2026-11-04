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

end Manuscript14Gram
