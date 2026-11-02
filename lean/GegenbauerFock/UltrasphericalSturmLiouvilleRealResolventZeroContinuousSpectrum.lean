import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventApproximateZero
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventSelfAdjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Basic

/-!
# V007 — dense proper nonclosed range of the genuine real Sturm resolvent

For lambda,t>0, the genuine closed Sturm positive resolvent is an injective
self-adjoint bounded operator on the whole weighted real L² space. Its
normalized Gegenbauer modes form an approximate null sequence. Applying
the Banach open mapping theorem makes surjectivity impossible. Symmetry
and injectivity make the range dense, hence it is not closed.

The proof concerns the actual infinite-dimensional Hilbert operator,
not a scalar sequence or finite-rank surrogate.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Filter

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- For every positive tolerance, a unit Gegenbauer vector has resolvent
image strictly smaller than that tolerance. -/
theorem sturmRealResolvent_exists_unit_small_image
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ f : H lam, ‖f‖ = 1 ∧
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht f‖ < eps := by
  have hevent : ∀ᶠ n : ℕ in atTop,
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ < eps :=
    (sturmRealPositiveResolventFullCLM_normalized_mode_norm_tendsto_zero
      lam t hlam ht).eventually (eventually_lt_nhds heps)
  obtain ⟨n, hn⟩ := hevent.exists
  exact ⟨sturmMonicEigenCandidate_realL2_normalized lam hlam n,
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n, hn⟩

/-- The genuine resolvent is not bounded below by any positive
multiple of the input norm, even though it is injective. -/
theorem sturmRealResolvent_not_bounded_below
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ f : H lam, c * ‖f‖ ≤
        ‖sturmRealPositiveResolventFullCLM lam t hlam ht f‖ := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨f, hf, hsmall⟩ :=
    sturmRealResolvent_exists_unit_small_image lam t hlam ht c hc
  have hle := hbound f
  rw [hf, mul_one] at hle
  exact (not_lt_of_ge hle) hsmall

/-- The genuine closed Sturm resolvent is not onto weighted real L².
Banach's open mapping theorem would bound inverse preimages and,
by injectivity, contradict the normalized approximate-null modes. -/
theorem sturmRealResolvent_not_surjective
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ¬ Function.Surjective
      (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  let R : H lam →L[ℝ] H lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  intro hsurj
  obtain ⟨C, hC, hpre⟩ := R.exists_preimage_norm_le hsurj
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hC
  obtain ⟨u, hu, hsmall⟩ :=
    sturmRealResolvent_exists_unit_small_image
      lam t hlam ht C⁻¹ hCinv
  obtain ⟨v, hv, hvnorm⟩ := hpre (R u)
  have heq : v = u :=
    (sturmRealPositiveResolventFullCLM_injective lam t hlam ht) hv
  rw [heq, hu] at hvnorm
  have hlt : C * ‖R u‖ < 1 := by
    calc
      C * ‖R u‖ < C * C⁻¹ := mul_lt_mul_of_pos_left hsmall hC
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hC)
  exact (not_lt_of_ge hvnorm) hlt

/-- The self-adjoint injective resolvent has dense range in the entire
weighted real Hilbert space. -/
theorem sturmRealResolvent_dense_range
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (sturmRealPositiveResolventFullCLM lam t hlam ht).range.topologicalClosure =
      (⊤ : Submodule ℝ (H lam)) := by
  let R : H lam →L[ℝ] H lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  have hker : R.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (sturmRealPositiveResolventFullCLM_injective lam t hlam ht)
  apply (Submodule.topologicalClosure_eq_top_iff).2
  rw [R.orthogonal_range,
    sturmRealPositiveResolventFullCLM_isSelfAdjoint lam t hlam ht, hker]

/-- The resolvent range is dense and proper, so it is not closed. -/
theorem sturmRealResolvent_range_not_closed
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ¬ IsClosed ((sturmRealPositiveResolventFullCLM lam t hlam ht).range :
      Set (H lam)) := by
  intro hclosed
  have htop :
      (sturmRealPositiveResolventFullCLM lam t hlam ht).range =
        (⊤ : Submodule ℝ (H lam)) := by
    calc
      (sturmRealPositiveResolventFullCLM lam t hlam ht).range =
        (sturmRealPositiveResolventFullCLM lam t hlam ht).range.topologicalClosure :=
          (hclosed.submodule_topologicalClosure_eq).symm
      _ = ⊤ := sturmRealResolvent_dense_range lam t hlam ht
  exact sturmRealResolvent_not_surjective lam t hlam ht
    (LinearMap.range_eq_top.mp htop)

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_exists_unit_small_image
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_not_bounded_below
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_not_surjective
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_dense_range
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_range_not_closed

end GegenbauerFock.Ultraspherical
