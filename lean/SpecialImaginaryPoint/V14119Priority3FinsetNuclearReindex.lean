import SpecialImaginaryPoint.V14119Priority3FiniteNuclearFredholm
import SpecialImaginaryPoint.V14119Priority3OptimalNuclearTruncations
import Mathlib.Data.Fintype.EquivFin

/-!
# Priority 3 — reindex optimal S₁ nuclear truncations by ordinary Fin m

The certified polar nuclear theorem gives, for every genuine CFC-S₁
operator T, a summable rank-one family indexed by an arbitrary
Hilbert-basis witness set w, with EXACT total nuclear mass ‖T‖₁.
Its arbitrary finite-index truncations are norm-controlled and
converge in the true trace norm.

This module turns EACH finite truncation on Finset w into a
canonical Fin m presentation — the exact domain of the previously
certified finite Gram Fredholm determinant estimates. It certifies:
  1. exact reindexing of finite sums as genuine CFC-S₁ operators;
  2. exact reindexing of finite nuclear presentation masses;
  3. for every CFC-S₁ operator, a trace-norm-convergent net of
     actual finiteNuclear(Fin m) operators, ALL with presentation
     mass at most ‖T‖₁.

This avoids assuming a nonexistent optimal finite rank-one
decomposition. The remaining step is passing finite-compression
determinant inequalities through these nets, using the certified
continuity of each fixed-N finite compression.
-/

noncomputable section
namespace Manuscript14Priority3.FinsetNuclearReindex

open Filter Topology InnerProductSpace
open scoped InnerProductSpace
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.FiniteNuclearFredholm

/-- Reindex a vector family restricted to an arbitrary finite subset
using the canonical equivalence with Fin s.card. -/
def finsetVectors {ι : Type*} (s : Finset ι) (u : ι → H) :
    Fin s.card → H :=
  fun i => u ((s.equivFin).symm i).val

/-- Any finite rank-one CFC-S₁ sum on an arbitrary index type
is EXACTLY a finiteNuclear m operator with a Fin m presentation. -/
theorem finiteNuclear_finset_eq {ι : Type*}
    (s : Finset ι) (u v : ι → H) :
    finiteNuclear s.card (finsetVectors s u) (finsetVectors s v) =
      ∑ i ∈ s, rankOneS1 (u i) (v i) := by
  classical
  unfold finiteNuclear finsetVectors
  rw [← Finset.sum_attach, Finset.attach_eq_univ]
  exact Fintype.sum_equiv (s.equivFin).symm
    (fun i : Fin s.card =>
      rankOneS1 (u ((s.equivFin).symm i).val)
        (v ((s.equivFin).symm i).val))
    (fun j : s => rankOneS1 (u j.val) (v j.val))
    (fun i => rfl)

/-- Exact equality of the sum of nuclear costs under the
same finite reindexing, without any dimension factor. -/
theorem nuclear_mass_finset_eq {ι : Type*}
    (s : Finset ι) (u v : ι → H) :
    (∑ i : Fin s.card,
      ‖finsetVectors s u i‖ * ‖finsetVectors s v i‖) =
      ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
  classical
  unfold finsetVectors
  rw [← Finset.sum_attach, Finset.attach_eq_univ]
  exact Fintype.sum_equiv (s.equivFin).symm
    (fun i : Fin s.card =>
      ‖u ((s.equivFin).symm i).val‖ *
        ‖v ((s.equivFin).symm i).val‖)
    (fun j : s => ‖u j.val‖ * ‖v j.val‖)
    (fun i => rfl)

/-- Every ACTUAL CFC-S₁ operator T is the trace-norm limit
of concrete finiteNuclear(Fin m) operators, and each
representation has nuclear mass at most the *true norm* ‖T‖₁.
This is unconditional and applies to nonnormal/nonselfadjoint T. -/
theorem traceClass_exists_optimal_fin_presentations
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ (w : Set H) (u v : w → H),
      Summable (fun i : w => ‖u i‖ * ‖v i‖) ∧
      Tendsto
        (fun s : Finset w =>
          finiteNuclear s.card (finsetVectors s u) (finsetVectors s v))
        atTop (𝓝 T) ∧
      (∀ s : Finset w,
        (∑ i : Fin s.card,
          ‖finsetVectors s u i‖ * ‖finsetVectors s v i‖) ≤
          ‖T‖) := by
  obtain ⟨w, u, v, hcost, hsum, hmass, hbounds, hlim⟩ :=
    traceClass_exists_optimal_normControlled_truncations T
  refine ⟨w, u, v, hcost, ?_, ?_⟩
  · have heq :
      (fun s : Finset w =>
        finiteNuclear s.card (finsetVectors s u) (finsetVectors s v)) =
        (fun s : Finset w => ∑ i ∈ s, rankOneS1 (u i) (v i)) := by
      funext s
      exact finiteNuclear_finset_eq s u v
    rw [heq]
    exact hlim
  · intro s
    rw [nuclear_mass_finset_eq]
    exact (hcost.sum_le_tsum s (fun i hi => by positivity)).trans_eq hmass

#print axioms Manuscript14Priority3.FinsetNuclearReindex.finiteNuclear_finset_eq
#print axioms Manuscript14Priority3.FinsetNuclearReindex.nuclear_mass_finset_eq
#print axioms Manuscript14Priority3.FinsetNuclearReindex.traceClass_exists_optimal_fin_presentations

end Manuscript14Priority3.FinsetNuclearReindex
