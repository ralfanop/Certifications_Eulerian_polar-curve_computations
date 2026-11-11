import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Priority 3 — Weierstrass holomorphy from pointwise complex convergence
# and complex-spectral equicontinuity, with no unproved analyticity claim

For an equicontinuous sequence Fₙ:ℂ→ℂ converging pointwise
to F, Ascoli's compact-domain theorem upgrades the convergence to
UNIFORM convergence on every compact subset of ℂ, hence to locally
uniform convergence throughout the complex plane.

If each Fₙ is holomorphic, Mathlib's Weierstrass theorem then proves
the limit F is entire. This is a formal bridge for the true CFC-S₁
Fredholm determinant, conditioned only on spectral equicontinuity
and holomorphy of the genuine finite-compression polynomials.
The assumptions are explicit, not axioms.
-/

noncomputable section
namespace Manuscript14Priority3.EquicontinuousWeierstrass

open Filter Topology Set

/-- Pointwise convergence of an equicontinuous family ℂ→ℂ
upgrades to locally uniform convergence by compact Ascoli.
No global compactness of ℂ is assumed. -/
theorem locally_uniform_of_equicontinuous
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hequi : Equicontinuous F)
    (hpoint : ∀ z : ℂ, Tendsto (fun n : ℕ => F n z) atTop (𝓝 (f z))) :
    TendstoLocallyUniformlyOn F f atTop (univ : Set ℂ) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _hK hcompact
  let fam : Set (Set ℂ) := {K}
  have hcompactFam : ∀ L ∈ fam, IsCompact L := by
    intro L hL
    have h : L = K := Set.mem_singleton_iff.mp hL
    simpa [h] using hcompact
  have hequiFam : ∀ L ∈ fam, EquicontinuousOn F L := by
    intro L hL
    have h : L = K := Set.mem_singleton_iff.mp hL
    subst L
    exact hequi.equicontinuousOn K
  have hpointK :
      Tendsto (K.domRestrict ∘ F) atTop
        (𝓝 (K.domRestrict f)) := by
    rw [tendsto_pi_nhds]
    intro x
    exact hpoint x.val
  have hloc :
      Tendsto ((UniformOnFun.ofFun fam) ∘ F) atTop
        (𝓝 (UniformOnFun.ofFun fam f)) := by
    apply (EquicontinuousOn.tendsto_uniformOnFun_iff_pi'
      hcompactFam hequiFam atTop f).2
    simpa [fam] using hpointK
  exact
    (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hloc)
      K (by simp [fam])

/-- A pointwise convergent equicontinuous sequence of entire
complex functions has an entire complex limit. -/
theorem entire_of_equicontinuous_pointwise
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hequi : Equicontinuous F)
    (hpoint : ∀ z : ℂ, Tendsto (fun n : ℕ => F n z) atTop (𝓝 (f z)))
    (hentire : ∀ n : ℕ, Differentiable ℂ (F n)) :
    Differentiable ℂ f := by
  have hloc := locally_uniform_of_equicontinuous F f hequi hpoint
  have hdiff : DifferentiableOn ℂ f (univ : Set ℂ) :=
    hloc.differentiableOn
      (Filter.Eventually.of_forall
        (fun n : ℕ => (hentire n).differentiableOn))
      isOpen_univ
  exact differentiableOn_univ.mp hdiff

#print axioms Manuscript14Priority3.EquicontinuousWeierstrass.locally_uniform_of_equicontinuous
#print axioms Manuscript14Priority3.EquicontinuousWeierstrass.entire_of_equicontinuous_pointwise

end Manuscript14Priority3.EquicontinuousWeierstrass
