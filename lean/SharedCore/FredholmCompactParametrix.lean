import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Shared Fredholm F8: compact parametrix defects give actual closed range,
finite kernel and finite-dimensional orthogonal cokernel for bounded maps.
No normality assumption. In particular the bound applies at exceptional
spectral points, without assuming injectivity of the original map.
The converse, index invariance and the determinant remain separate. -/
namespace SharedCore.FredholmParametrix

open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- A compact defect and left parametrix force the restriction to the
orthogonal complement of the kernel to be bounded below. -/
theorem lower_bound_on_kernel_orthogonal
    (T : E →L[ℂ] F) (S : F →L[ℂ] E) (C : E →L[ℂ] E)
    (hC : IsCompactOperator C) (hdef : ∀ x, C x + S (T x) = x) :
    ∃ k, AntilipschitzWith k (T.comp T.kerᗮ.subtypeL) := by
  let g : T.kerᗮ →L[ℂ] F := T.comp T.kerᗮ.subtypeL
  change ∃ k, AntilipschitzWith k g
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra! h
  have hb : ∃ c > 0, ∀ ε > 0, ∃ x : T.kerᗮ,
      ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖g x‖ < ε := by
    obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm ℂ
    refine ⟨‖a‖⁻¹, by positivity, fun ε hε ↦ ?_⟩
    obtain ⟨x, hx⟩ := h ε hε
    have hn : x ≠ 0 := by
      intro he
      simp [he] at hx
    obtain ⟨η, hη, h₁, h₂, h₃⟩ := rescale_to_shell ha (ε := 1) (by simp) hn
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc, hsmall⟩ := hb
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have hs (n : ℕ) : ∃ x : T.kerᗮ, ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖g x‖ < φ n :=
    hsmall (φ n) (hφ_pos n)
  choose x hxupper hxlower hxbound using hs
  have hg_lim : Tendsto (fun n ↦ g (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (by grind) hφ
  let y_ (n : ℕ) : E := C (x n : E)
  obtain ⟨K, hK, hK'⟩ := hC.image_closedBall_subset_compact 1
  have hy_mem (n : ℕ) : y_ n ∈ K := by
    apply hK'
    exact ⟨(x n : E), by simpa using hxupper n, rfl⟩
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (x := y_) hy_mem
  have hTs : Tendsto (fun n ↦ T (x (ψ n) : E)) atTop (𝓝 0) := by
    simpa [g] using hg_lim.comp hψ.tendsto_atTop
  have hSs : Tendsto (fun n ↦ S (T (x (ψ n) : E))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using S.continuous.continuousAt.tendsto.comp hTs
  have he : (fun n ↦ y_ (ψ n) + S (T (x (ψ n) : E))) =
      (fun n ↦ (x (ψ n) : E)) := by
    funext n
    exact hdef _
  have hx_lim : Tendsto (fun n ↦ (x (ψ n) : E)) atTop (𝓝 y) := by
    have hh := hψy.add hSs
    rw [he, add_zero] at hh
    exact hh
  have hy_perp : y ∈ T.kerᗮ :=
    T.ker.isClosed_orthogonal.mem_of_tendsto hx_lim
      (Filter.Eventually.of_forall fun n ↦ (x (ψ n)).property)
  have hy_zero : T y = 0 := by
    apply tendsto_nhds_unique _ hTs
    exact T.continuous.continuousAt.tendsto.comp hx_lim
  have hy_ker : y ∈ T.ker := hy_zero
  have hy_bot : y ∈ (⊥ : Submodule ℂ E) := by
    rw [← T.ker.inf_orthogonal_eq_bot]
    exact ⟨hy_ker, hy_perp⟩
  have hy_eq : y = 0 := by simpa using hy_bot
  have hy_lower : c ≤ ‖y‖ := by
    apply le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hx_lim)
    exact Filter.Eventually.of_forall (fun n ↦ by simpa using hxlower (ψ n))
  rw [hy_eq, norm_zero] at hy_lower
  exact (not_le_of_gt hc) hy_lower

/-- The actual range is closed under a compact left parametrix defect. -/
theorem closed_range_of_left_compact_defect
    (T : E →L[ℂ] F) (S : F →L[ℂ] E) (C : E →L[ℂ] E)
    (hC : IsCompactOperator C) (hdef : ∀ x, C x + S (T x) = x) :
    IsClosed (Set.range T) := by
  let U := T.kerᗮ
  letI : CompleteSpace U := T.ker.isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace T.ker := (show IsClosed (T.ker : Set E) from
    isClosed_eq T.continuous continuous_const).completeSpace_coe
  let g : U →L[ℂ] F := T.comp U.subtypeL
  obtain ⟨k, hk⟩ := lower_bound_on_kernel_orthogonal T S C hC hdef
  have hkg : AntilipschitzWith k g := hk
  have he : Set.range g = Set.range T := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : E), rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := T.ker.exists_add_mem_mem_orthogonal x
      refine ⟨⟨b, hb⟩, ?_⟩
      change T b = T x
      have hza : T a = 0 := ha
      rw [hab, map_add, hza, zero_add]
  rw [← he]
  exact hkg.isClosed_range g.uniformContinuous

private theorem finite_dimensional_of_projection_defect
    (U : Submodule ℂ E) [CompleteSpace U] (C : E →L[ℂ] E)
    (hC : IsCompactOperator C)
    (hfix : ∀ x : U, U.orthogonalProjectionOnto (C x) = x) :
    FiniteDimensional ℂ U := by
  have hc : IsCompactOperator (fun x : U ↦ U.orthogonalProjectionOnto (C x)) :=
    (hC.comp_clm U.subtypeL).clm_comp U.orthogonalProjectionOnto
  have he : (fun x : U ↦ U.orthogonalProjectionOnto (C x)) = id := funext hfix
  rw [he] at hc
  letI : LocallyCompactSpace U := LocallyCompactSpace.of_isCompactOperator_id hc
  exact FiniteDimensional.of_locallyCompactSpace ℂ

/-- Finite-dimensional kernel from the actual compact left defect. -/
theorem finite_kernel_of_left_compact_defect
    (T : E →L[ℂ] F) (S : F →L[ℂ] E) (C : E →L[ℂ] E)
    (hC : IsCompactOperator C) (hdef : ∀ x, C x + S (T x) = x) :
    FiniteDimensional ℂ T.ker := by
  letI : CompleteSpace T.ker := (show IsClosed (T.ker : Set E) from
    isClosed_eq T.continuous continuous_const).completeSpace_coe
  apply finite_dimensional_of_projection_defect T.ker C hC
  intro x
  have hx : T (x : E) = 0 := x.property
  have hxC : C (x : E) = x := by simpa [hx] using hdef (x : E)
  rw [hxC]
  exact T.ker.orthogonalProjectionOnto_mem_subspace_eq_self x

/-- Finite-dimensional orthogonal complement of the range from the actual
compact right defect; no adjoint compactness theorem is needed. -/
theorem finite_range_orthogonal_of_right_compact_defect
    (T : E →L[ℂ] F) (S : F →L[ℂ] E) (D : F →L[ℂ] F)
    (hD : IsCompactOperator D) (hdef : ∀ y, D y + T (S y) = y) :
    FiniteDimensional ℂ T.rangeᗮ := by
  let U := T.rangeᗮ
  letI : CompleteSpace U := T.range.isClosed_orthogonal.completeSpace_coe
  change FiniteDimensional ℂ U
  apply finite_dimensional_of_projection_defect U D hD
  intro y
  have hy : T (S (y : F)) ∈ Uᗮ :=
    T.range.le_orthogonal_orthogonal ⟨S (y : F), rfl⟩
  have hz : U.orthogonalProjectionOnto (T (S (y : F))) = 0 :=
    U.orthogonalProjectionOnto_apply_of_mem_orthogonal hy
  have h := congrArg U.orthogonalProjectionOnto (hdef (y : F))
  rw [map_add, hz, add_zero, U.orthogonalProjectionOnto_mem_subspace_eq_self y] at h
  exact h

/-- Forward Hilbert-space compact-parametrix Fredholm criterion, expressed
as closed range, finite kernel, and finite orthogonal cokernel. -/
theorem fredholm_components_of_compact_parametrix
    (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (hL : IsCompactOperator ((1 : E →L[ℂ] E) - S.comp T))
    (hR : IsCompactOperator ((1 : F →L[ℂ] F) - T.comp S)) :
    IsClosed (Set.range T) ∧ FiniteDimensional ℂ T.ker ∧
      FiniteDimensional ℂ T.rangeᗮ := by
  have hleft (x : E) : ((1 : E →L[ℂ] E) - S.comp T) x + S (T x) = x := by
    change x - S (T x) + S (T x) = x
    exact sub_add_cancel _ _
  have hright (y : F) : ((1 : F →L[ℂ] F) - T.comp S) y + T (S y) = y := by
    change y - T (S y) + T (S y) = y
    exact sub_add_cancel _ _
  exact ⟨closed_range_of_left_compact_defect T S _ hL hleft,
    finite_kernel_of_left_compact_defect T S _ hL hleft,
    finite_range_orthogonal_of_right_compact_defect T S _ hR hright⟩

end SharedCore.FredholmParametrix

#print axioms SharedCore.FredholmParametrix.lower_bound_on_kernel_orthogonal
#print axioms SharedCore.FredholmParametrix.closed_range_of_left_compact_defect
#print axioms SharedCore.FredholmParametrix.finite_kernel_of_left_compact_defect
#print axioms SharedCore.FredholmParametrix.finite_range_orthogonal_of_right_compact_defect
#print axioms SharedCore.FredholmParametrix.fredholm_components_of_compact_parametrix
