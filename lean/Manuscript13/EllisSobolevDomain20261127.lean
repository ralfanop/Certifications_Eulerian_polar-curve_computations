import Mathlib
import Manuscript13.EllisComplexResolvent20261127
open MeasureTheory Filter
namespace Manuscript13.EllisSobolevDomain20261127
noncomputable section
open Manuscript13.EllisComplexResolvent20261127
/-! Fourier characterization of the graph domain by the Bessel-potential
H² condition. The separate weak-derivative equivalence is not asserted
by definition: it remains to be proved using tempered distributions. -/
def frequencySquare (x : ℝ) : ℝ := (2 * Real.pi * x)^2

def besselH2 (u : H) : Prop :=
  MemLp (fun x => ((1 + frequencySquare x : ℝ) : ℂ) * fourier u x) 2 volume

def secondFrequency (u : H) : Prop :=
  MemLp (fun x => (frequencySquare x : ℂ) * fourier u x) 2 volume

theorem secondFrequency_iff_bessel (u : H) : secondFrequency u ↔ besselH2 u := by
  unfold secondFrequency besselH2
  constructor
  · intro h
    apply (h.add (Lp.memLp (fourier u))).congr
    filter_upwards [] with x
    push_cast
    ring
  · intro h
    apply (h.sub (Lp.memLp (fourier u))).congr
    filter_upwards [] with x
    push_cast
    ring

theorem shiftedMem_iff_second (κ : ℝ) (u : H) :
    MemLp (fun x => (symbol κ x : ℂ) * fourier u x) 2 volume ↔ secondFrequency u := by
  unfold secondFrequency
  have hc := (Lp.memLp (fourier u)).const_mul ((κ^2 : ℝ) : ℂ)
  constructor
  · intro h
    apply (h.sub hc).congr
    filter_upwards [] with x
    unfold symbol frequencySquare
    push_cast
    ring
  · intro h
    apply (h.add hc).congr
    filter_upwards [] with x
    unfold symbol frequencySquare
    push_cast
    ring

theorem graph_iff_shiftedMem (κ : ℝ) (u : H) :
    (∃ f : H, shiftedGraph κ u f) ↔
      MemLp (fun x => (symbol κ x : ℂ) * fourier u x) 2 volume := by
  constructor
  · rintro ⟨f,hf⟩
    exact (Lp.memLp (fourier f)).congr hf.symm
  · intro h
    refine ⟨fourier.symm (h.toLp _), ?_⟩
    unfold shiftedGraph
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact h.coeFn_toLp.symm

theorem graph_iff_besselH2 (κ : ℝ) (u : H) :
    (∃ f : H, shiftedGraph κ u f) ↔ besselH2 u :=
  (graph_iff_shiftedMem κ u).trans ((shiftedMem_iff_second κ u).trans (secondFrequency_iff_bessel u))

theorem range_resolvent_iff_besselH2 (κ : ℝ) (hk : 0 < κ) (u : H) :
    u ∈ Set.range (freeResolvent κ hk) ↔ besselH2 u := by
  rw [← graph_iff_besselH2 κ u]
  constructor
  · rintro ⟨f,rfl⟩
    exact ⟨f,freeResolvent_graph κ hk f⟩
  · rintro ⟨f,hf⟩
    exact ⟨f,(freeResolvent_graph_unique κ hk u f hf).symm⟩

theorem resolvent_besselH2 (κ : ℝ) (hk : 0 < κ) (f : H) :
    besselH2 (freeResolvent κ hk f) :=
  (range_resolvent_iff_besselH2 κ hk _).1 ⟨f,rfl⟩

end
end Manuscript13.EllisSobolevDomain20261127
#print axioms Manuscript13.EllisSobolevDomain20261127.frequencySquare
#print axioms Manuscript13.EllisSobolevDomain20261127.besselH2
#print axioms Manuscript13.EllisSobolevDomain20261127.secondFrequency
#print axioms Manuscript13.EllisSobolevDomain20261127.secondFrequency_iff_bessel
#print axioms Manuscript13.EllisSobolevDomain20261127.shiftedMem_iff_second
#print axioms Manuscript13.EllisSobolevDomain20261127.graph_iff_shiftedMem
#print axioms Manuscript13.EllisSobolevDomain20261127.graph_iff_besselH2
#print axioms Manuscript13.EllisSobolevDomain20261127.range_resolvent_iff_besselH2
#print axioms Manuscript13.EllisSobolevDomain20261127.resolvent_besselH2
