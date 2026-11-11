import Mathlib

/-!
# Priority 3 — independent double-net limiting argument for determinant perturbations

A continuous complex-valued functional on any normed additive group
preserves a uniform-in-indices perturbation upper bound along TWO
independently convergent nets.

Applied to true finite Hilbert-compression determinants, this allows
passing a dimension-free finite-nuclear cost estimate to independent
CFC-S₁ finite nuclear truncations of both base T and perturbation R.

The result is purely topological: it does not assume finite optimal
nuclear presentations, nor does it construct a Fredholm determinant.
Its hypotheses are actual continuity, actual convergence of BOTH
nets, and a bound for every pair of finite approximants. No extra
axioms, compactness, or normality are needed.
-/

noncomputable section

namespace Manuscript14Priority3.TwoNetBoundLimit

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E]
variable {ι κ : Type*}
variable {𝓕 : Filter ι} {𝓖 : Filter κ}
variable [NeBot 𝓕] [NeBot 𝓖]

/-- Pass an actual real upper bound for a complex functional first
through the perturbation net and then through the base net.
The bound stays EXACTLY the same, with no dimension or net factors. -/
theorem continuous_complex_two_net_perturbation_bound
    (f : E → ℂ) (hf : Continuous f)
    (u : ι → E) (v : κ → E) (T R : E)
    (hu : Tendsto u 𝓕 (𝓝 T))
    (hv : Tendsto v 𝓖 (𝓝 R))
    (M : ℝ)
    (hbound : ∀ i j,
      ‖f (u i + v j) - f (u i)‖ ≤ M) :
    ‖f (T + R) - f T‖ ≤ M := by
  have hlimitR (i : ι) :
      ‖f (u i + R) - f (u i)‖ ≤ M := by
    have hc : Continuous
        (fun x : E => ‖f (u i + x) - f (u i)‖) :=
      continuous_norm.comp
        ((hf.comp (continuous_const.add continuous_id)).sub continuous_const)
    have ht : Tendsto
        (fun j : κ => ‖f (u i + v j) - f (u i)‖)
        𝓖 (𝓝 (‖f (u i + R) - f (u i)‖)) :=
      hc.continuousAt.tendsto.comp hv
    exact le_of_tendsto ht (Filter.Eventually.of_forall (hbound i))
  have hcT : Continuous
      (fun x : E => ‖f (x + R) - f x‖) :=
    continuous_norm.comp
      ((hf.comp (continuous_id.add continuous_const)).sub hf)
  have htT : Tendsto
      (fun i : ι => ‖f (u i + R) - f (u i)‖)
      𝓕 (𝓝 (‖f (T + R) - f T‖)) :=
    hcT.continuousAt.tendsto.comp hu
  exact le_of_tendsto htT (Filter.Eventually.of_forall hlimitR)

#print axioms Manuscript14Priority3.TwoNetBoundLimit.continuous_complex_two_net_perturbation_bound

end Manuscript14Priority3.TwoNetBoundLimit
