import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventApproximateZero
import Mathlib.Topology.Constructions

/-!
# V007 — inverse instability on the actual closed Sturm resolvent range

A unit Gegenbauer mode sequence has resolvent images tending to zero.
Therefore no exact (even nonlinear) inverse defined on the actual
range subtype can be continuous at zero. This is stronger than failure
of a bounded inverse on the whole Hilbert space.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Filter

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Any exact reconstruction on the range of the genuine closed Sturm
positive resolvent is discontinuous at zero, with the range carrying
its inherited Hilbert-space topology. -/
theorem sturmRealResolvent_inverse_on_range_discontinuous_at_zero
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (r : (sturmRealPositiveResolventFullCLM lam t hlam ht).range → H lam)
    (hleft : ∀ f : H lam,
      r ⟨sturmRealPositiveResolventFullCLM lam t hlam ht f, ⟨f, rfl⟩⟩ = f) :
    ¬ ContinuousAt r (0 :
      (sturmRealPositiveResolventFullCLM lam t hlam ht).range) := by
  let R : H lam →L[ℝ] H lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  let u : ℕ → H lam :=
    fun n => sturmMonicEigenCandidate_realL2_normalized lam hlam n
  have hunit : ∀ n : ℕ, ‖u n‖ = 1 := by
    intro n
    exact sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n
  have himage : Tendsto (fun n : ℕ => R (u n))
      atTop (nhds (0 : H lam)) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    exact sturmRealPositiveResolventFullCLM_normalized_mode_norm_tendsto_zero
      lam t hlam ht
  intro hcont
  have hsub : Tendsto
      (fun n : ℕ => (⟨R (u n), ⟨u n, rfl⟩⟩ : R.range))
      atTop (nhds (0 : R.range)) := by
    apply tendsto_subtype_rng.mpr
    simpa using himage
  have hrec : Tendsto
      (fun n : ℕ => r (⟨R (u n), ⟨u n, rfl⟩⟩ : R.range))
      atTop (nhds (r (0 : R.range))) :=
    hcont.tendsto.comp hsub
  have heq :
      (fun n : ℕ => r (⟨R (u n), ⟨u n, rfl⟩⟩ : R.range)) = u := by
    funext n
    exact hleft (u n)
  rw [heq] at hrec
  have hrzero : r (0 : R.range) = 0 := by
    have hz : (⟨R (0 : H lam), ⟨(0 : H lam), rfl⟩⟩ : R.range) = 0 := by
      apply Subtype.ext
      exact map_zero R
    calc
      r (0 : R.range) =
          r (⟨R (0 : H lam), ⟨(0 : H lam), rfl⟩⟩ : R.range) :=
            congrArg r hz.symm
      _ = 0 := hleft 0
  rw [hrzero] at hrec
  have hnormzero : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (0 : ℝ)) := by
    simpa using hrec.norm
  have hnormone : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (1 : ℝ)) := by
    have hn : (fun n : ℕ => ‖u n‖) = (fun _ : ℕ => (1 : ℝ)) :=
      funext hunit
    rw [hn]
    exact tendsto_const_nhds
  have hcontradiction : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hnormzero hnormone
  norm_num at hcontradiction

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_inverse_on_range_discontinuous_at_zero

end GegenbauerFock.Ultraspherical
