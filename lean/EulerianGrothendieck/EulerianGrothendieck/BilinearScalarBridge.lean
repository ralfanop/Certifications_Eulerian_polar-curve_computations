import EulerianGrothendieck.ExplicitProjector
import EulerianGrothendieck.ScalarMaximum

/-! # Task C1, part 1: the complex bilinear scalar norm

For a square complex matrix `A`, `bilinearScalarNorm A` is the manuscript's
`g_ℂ(A) = max_{|a_i|,|b_j| ≤ 1} |a^T A b|`, defined as a supremum over the closed polydisc,
with `a^T A b = a ⬝ᵥ (A *ᵥ b)`.

For the explicit matrix `P = V^*(VV^*)^{-1}V` (`explicitFrameProjector`) we prove
`g_ℂ(P) = max_{|u_j| = 1} u^* P u`, i.e. `bilinearScalarNorm P = explicitFrameScalarNorm e z`,
and that both suprema are attained.  The proof is the manuscript's: Cauchy--Schwarz for the
projection, followed by coordinatewise maximisation of the convex function `u ↦ ‖P u‖²`
on the polydisc. -/

noncomputable section
open scoped ComplexConjugate
open Matrix
namespace EulerianGrothendieck
set_option maxHeartbeats 2000000

/-- The values `|a^T A b|` for `a, b` in the closed unit polydisc. -/
def bilinearScalarValues {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Set ℝ :=
  {r | ∃ a b : Fin m → ℂ, (∀ i, ‖a i‖ ≤ 1) ∧ (∀ j, ‖b j‖ ≤ 1) ∧ r = ‖a ⬝ᵥ (A *ᵥ b)‖}

/-- `g_ℂ(A) = sup_{|a_i|,|b_j| ≤ 1} |a^T A b|`. -/
def bilinearScalarNorm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : ℝ := sSup (bilinearScalarValues A)

/-- Coordinatewise step: the convex function `u ↦ ‖T u‖²` does not decrease when one
coordinate in the closed disc is moved to a suitable point of the unit circle. -/
theorem coordinate_unimodular_step (T : FourSpace →ₗ[ℂ] FourSpace) (u : FourSpace) (j : Fin 4)
    (hj : ‖u j‖ ≤ 1) :
    ∃ u' : FourSpace, ‖u' j‖ = 1 ∧ (∀ i, i ≠ j → u' i = u i) ∧ ‖T u‖ ^ 2 ≤ ‖T u'‖ ^ 2 := by
  classical
  -- a unimodular direction `ζ` with `u j = ‖u j‖ ζ`
  obtain ⟨ζ, hζn, hsζ⟩ : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ((‖u j‖ : ℝ) : ℂ) * ζ = u j := by
    by_cases h0 : u j = 0
    · exact ⟨1, norm_one, by simp [h0]⟩
    · have hn : (‖u j‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr h0
      have hn' : ((‖u j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
      refine ⟨u j / (‖u j‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        exact div_self hn
      · field_simp
  set e : FourSpace := EuclideanSpace.single j ζ with he
  set v0 : FourSpace := u - EuclideanSpace.single j (u j) with hv0
  have hu : u = v0 + ((‖u j‖ : ℝ) : ℂ) • e := by
    ext i
    simp only [hv0, he, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      EuclideanSpace.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, hsζ]; ring
    · rw [if_neg hij, if_neg hij]; ring
  have hcoord : ∀ (c : ℂ), (v0 + c • e) j = c * ζ ∧ ∀ i, i ≠ j → (v0 + c • e) i = u i := by
    intro c
    constructor
    · simp [hv0, he, EuclideanSpace.single_apply]
    · intro i hi
      simp [hv0, he, EuclideanSpace.single_apply, hi]
  -- the quadratic polynomial in the real parameter `t`
  have hquad : ∀ t : ℝ, ‖T (v0 + (t : ℂ) • e)‖ ^ 2 =
      ‖T v0‖ ^ 2 + 2 * t * (inner ℂ (T v0) (T e)).re + t ^ 2 * ‖T e‖ ^ 2 := by
    intro t
    rw [map_add, map_smul, norm_add_sq (𝕜 := ℂ), norm_smul, inner_smul_right]
    simp only [RCLike.re_to_complex, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Complex.re_ofReal_mul]
    ring
  have hs0 : 0 ≤ ‖u j‖ := norm_nonneg _
  have hC : 0 ≤ ‖T e‖ ^ 2 := sq_nonneg _
  have hval := hquad ‖u j‖
  rw [← hu] at hval
  by_cases hB : 0 ≤ (inner ℂ (T v0) (T e)).re
  · refine ⟨v0 + ((1:ℝ):ℂ) • e, ?_, ?_, ?_⟩
    · rw [(hcoord _).1]; simp [hζn]
    · exact (hcoord _).2
    · rw [hval, hquad 1]
      have h2 : ‖u j‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith
  · refine ⟨v0 + ((-1:ℝ):ℂ) • e, ?_, ?_, ?_⟩
    · rw [(hcoord _).1]; simp [hζn]
    · exact (hcoord _).2
    · rw [hval, hquad (-1)]
      have h2 : ‖u j‖ ^ 2 ≤ 1 := by nlinarith
      push_neg at hB
      nlinarith

/-- Every point of the closed polydisc is dominated by a point of the torus. -/
theorem exists_torus_ge (T : FourSpace →ₗ[ℂ] FourSpace) (u : FourSpace)
    (hu : ∀ i, ‖u i‖ ≤ 1) : ∃ t : FourSpace, IsTorusPoint t ∧ ‖T u‖ ^ 2 ≤ ‖T t‖ ^ 2 := by
  classical
  have key : ∀ s : Finset (Fin 4), ∀ u : FourSpace, (∀ i, ‖u i‖ ≤ 1) →
      (∀ i, i ∉ s → ‖u i‖ = 1) → ∃ t : FourSpace, IsTorusPoint t ∧ ‖T u‖ ^ 2 ≤ ‖T t‖ ^ 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro u _ h1
      exact ⟨u, fun i => h1 i (Finset.notMem_empty i), le_rfl⟩
    | insert j s hjs ih =>
      intro u hu h1
      obtain ⟨u', hu'j, hu'o, hle⟩ := coordinate_unimodular_step T u j (hu j)
      have hu'd : ∀ i, ‖u' i‖ ≤ 1 := by
        intro i
        by_cases hij : i = j
        · rw [hij, hu'j]
        · rw [hu'o i hij]; exact hu i
      have hu'1 : ∀ i, i ∉ s → ‖u' i‖ = 1 := by
        intro i hi
        by_cases hij : i = j
        · rw [hij, hu'j]
        · rw [hu'o i hij]; exact h1 i (by simp [hij, hi])
      obtain ⟨t, ht, hle'⟩ := ih u' hu'd hu'1
      exact ⟨t, ht, hle.trans hle'⟩
  exact key Finset.univ u hu (fun i hi => absurd (Finset.mem_univ i) hi)

/-- On the polydisc, `‖K u‖²` is bounded by the torus maximum `projectionScalarNorm`. -/
theorem polydisk_projection_le (U : Submodule ℂ FourSpace) (u : FourSpace)
    (hu : ∀ i, ‖u i‖ ≤ 1) : ‖U.starProjection u‖ ^ 2 ≤ projectionScalarNorm U := by
  obtain ⟨t, ht, hle⟩ := exists_torus_ge (U.starProjection : FourSpace →L[ℂ] FourSpace).toLinearMap
    u hu
  exact hle.trans (projectionScalarNorm_ge U t ht)

/-- `a^T A b` is the Euclidean inner product of `conj a` with `A b`. -/
theorem bilinear_eq_inner (A : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4 → ℂ) :
    a ⬝ᵥ (A *ᵥ b) = inner ℂ (WithLp.toLp 2 (star a) : FourSpace)
      (A.toEuclideanLin (WithLp.toLp 2 b : FourSpace)) := by
  simp only [PiLp.inner_apply, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, PiLp.toLp_apply,
    RCLike.inner_apply, Pi.star_apply, Complex.star_def, Complex.conj_conj, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem explicit_bilinear_value_le (e : ℝ) (z : ℂ) (a b : Fin 4 → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ j, ‖b j‖ ≤ 1) :
    ‖a ⬝ᵥ (explicitFrameProjector e z *ᵥ b)‖ ≤ projectionScalarNorm (frameSubspace e z) := by
  set U := frameSubspace e z
  set va : FourSpace := WithLp.toLp 2 (star a)
  set vb : FourSpace := WithLp.toLp 2 b
  rw [bilinear_eq_inner, explicitFrameProjector_eq_projection]
  have hid : U.starProjection vb = U.starProjection (U.starProjection vb) :=
    (U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem vb)).symm
  rw [hid, ← U.inner_starProjection_left_eq_right]
  have hva : ∀ i, ‖va i‖ ≤ 1 := by
    intro i; simpa [va] using ha i
  have hvb : ∀ i, ‖vb i‖ ≤ 1 := by
    intro i; simpa [vb] using hb i
  have h1 := polydisk_projection_le U va hva
  have h2 := polydisk_projection_le U vb hvb
  calc ‖inner ℂ (U.starProjection va) (U.starProjection vb)‖
      ≤ ‖U.starProjection va‖ * ‖U.starProjection vb‖ := norm_inner_le_norm _ _
    _ ≤ (‖U.starProjection va‖ ^ 2 + ‖U.starProjection vb‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖U.starProjection va‖ - ‖U.starProjection vb‖)]
    _ ≤ projectionScalarNorm U := by linarith

theorem explicit_bilinearScalarValues_bddAbove (e : ℝ) (z : ℂ) :
    BddAbove (bilinearScalarValues (explicitFrameProjector e z)) := by
  refine ⟨projectionScalarNorm (frameSubspace e z), ?_⟩
  rintro r ⟨a, b, ha, hb, rfl⟩
  exact explicit_bilinear_value_le e z a b ha hb

/-- The torus quadratic value `u^* P u = ‖P u‖²` is a bilinear value with `a = conj u`, `b = u`. -/
theorem torus_value_mem_bilinear (e : ℝ) (z : ℂ) (u : FourSpace) (hu : IsTorusPoint u) :
    ‖(frameSubspace e z).starProjection u‖ ^ 2 ∈
      bilinearScalarValues (explicitFrameProjector e z) := by
  refine ⟨star (WithLp.ofLp u), WithLp.ofLp u, ?_, ?_, ?_⟩
  · intro i; simp [hu i]
  · intro j; simp [hu j]
  · rw [bilinear_eq_inner, explicitFrameProjector_eq_projection]
    have hst : (WithLp.toLp 2 (star (star (WithLp.ofLp u))) : FourSpace) = u := by simp
    have hu' : (WithLp.toLp 2 (WithLp.ofLp u) : FourSpace) = u := by simp
    rw [hst, hu']
    have hreal : inner ℂ u ((frameSubspace e z).starProjection u) =
        ((‖(frameSubspace e z).starProjection u‖ ^ 2 : ℝ) : ℂ) := by
      have h := (frameSubspace e z).inner_starProjection_left_eq_right u
        ((frameSubspace e z).starProjection u)
      rw [(frameSubspace e z).starProjection_eq_self_iff.mpr
        ((frameSubspace e z).starProjection_apply_mem u)] at h
      rw [← h, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- **`g_ℂ(P) = max_{|u_j|=1} u^* P u`** for the explicit projector `P = V^*(VV^*)^{-1}V`. -/
theorem bilinearScalarNorm_explicit (e : ℝ) (z : ℂ) :
    bilinearScalarNorm (explicitFrameProjector e z) = explicitFrameScalarNorm e z := by
  rw [explicitFrameScalarNorm_eq]
  apply le_antisymm
  · refine csSup_le ⟨_, 0, 0, fun i => by simp, fun j => by simp, rfl⟩ ?_
    rintro r ⟨a, b, ha, hb, rfl⟩
    exact explicit_bilinear_value_le e z a b ha hb
  · obtain ⟨u, hu, hmax⟩ := projectionScalarNorm_attained (frameSubspace e z)
    rw [hmax]
    exact le_csSup (explicit_bilinearScalarValues_bddAbove e z) (torus_value_mem_bilinear e z u hu)

/-- The supremum defining `g_ℂ(P)` is a maximum. -/
theorem bilinearScalarNorm_explicit_attained (e : ℝ) (z : ℂ) :
    ∃ a b : Fin 4 → ℂ, (∀ i, ‖a i‖ ≤ 1) ∧ (∀ j, ‖b j‖ ≤ 1) ∧
      bilinearScalarNorm (explicitFrameProjector e z) = ‖a ⬝ᵥ (explicitFrameProjector e z *ᵥ b)‖ := by
  obtain ⟨u, hu, hmax⟩ := projectionScalarNorm_attained (frameSubspace e z)
  obtain ⟨a, b, ha, hb, hval⟩ := torus_value_mem_bilinear e z u hu
  refine ⟨a, b, ha, hb, ?_⟩
  rw [bilinearScalarNorm_explicit, explicitFrameScalarNorm_eq, hmax, hval]

end EulerianGrothendieck
