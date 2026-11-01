import Bridge.FrameBridge
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Proposition 3.7: the step-function isometry `U_d` and the finite-frame factorisation

Manuscript V173, Proposition 3.7, eqs. (34)–(36).

`I_{d,k} = [-1/2 + k/d, -1/2 + (k+1)/d]` (`k = 0, …, d-1`, i.e. the manuscript's `I_{d,k+1}`),
`U_d e_k = √d 1_{I_{d,k}} ∈ L²(ℝ)`, `c_d = d^{-1/2}(1,…,1)` and `ψ₁ = 1_{[-1/2,1/2]}`.
We prove that the `√d 1_{I_{d,k}}` are orthonormal, `U_d† U_d = I`, `U_d c_d = ψ₁`, and then,
with Hall's unitarity `𝒱†𝒱 = I` and Vourdas's `M M† = I` as cited hypotheses, the conclusions of
Proposition 3.7 for `B = 𝒱 U_d M`.
-/

open MeasureTheory Set ContinuousLinearMap
open scoped ComplexConjugate

namespace EulerianBridge.StepFrame

/-- `L²(ℝ)`. -/
abbrev L2R := ↥(Lp ℂ 2 (volume : Measure ℝ))

variable {d : ℕ}

/-- The closed cell `I_{d,k}`. -/
def cell (d : ℕ) (k : ℕ) : Set ℝ := Icc (-1/2 + k / d) (-1/2 + (k + 1) / d)

theorem volume_cell_ne_top (k : ℕ) : volume (cell d k) ≠ ⊤ := by
  unfold cell; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

theorem volume_real_cell (hd : 0 < d) (k : ℕ) : volume.real (cell d k) = 1 / d := by
  unfold cell; rw [Real.volume_real_Icc]
  have : (0:ℝ) < d := by exact_mod_cast hd
  rw [max_eq_left (by rw [sub_nonneg]; gcongr; linarith)]; field_simp; ring

theorem volume_real_cell_inter (hd : 0 < d) {j k : ℕ} (hjk : j ≠ k) :
    volume.real (cell d j ∩ cell d k) = 0 := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  -- the intersection is contained in a single point
  have key : ∀ {a b : ℕ}, a < b → cell d a ∩ cell d b ⊆ {-1/2 + (b:ℝ) / d} := by
    intro a b hab x ⟨⟨_, h2⟩, ⟨h3, _⟩⟩
    have : ((a:ℝ) + 1) / d ≤ (b:ℝ) / d := by
      apply div_le_div_of_nonneg_right _ hd'.le; exact_mod_cast hab
    exact le_antisymm (by linarith) h3
  have hpt : ∀ x : ℝ, volume.real ({x} : Set ℝ) = 0 := fun x => by simp [measureReal_def]
  have hpt' : ∀ x : ℝ, volume ({x} : Set ℝ) ≠ ⊤ := fun x => by simp
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · exact measureReal_mono_null (key h) (hpt _) (hpt' _)
  · rw [inter_comm]; exact measureReal_mono_null (key h) (hpt _) (hpt' _)

/-- The vectors `√d 1_{I_{d,k}}`. -/
theorem measurableSet_cell (d k : ℕ) : MeasurableSet (cell d k) := by unfold cell; exact measurableSet_Icc

noncomputable def v (d : ℕ) (k : Fin d) : L2R :=
  indicatorConstLp (s := cell d k) 2 (measurableSet_cell d k) (volume_cell_ne_top (d := d) k) (Real.sqrt d : ℂ)

theorem inner_v (hd : 0 < d) (j k : Fin d) : (inner ℂ (v d j) (v d k) : ℂ) = if j = k then 1 else 0 := by
  unfold v
  rw [L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_cell d j) (measurableSet_cell d k)
    (volume_cell_ne_top (d := d) j) (volume_cell_ne_top (d := d) k)]
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hd : (0:ℝ) < d)).ne'
  have hin : (inner ℂ (Real.sqrt d : ℂ) (Real.sqrt d : ℂ) : ℂ) = d := by
    rw [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  rw [hin]
  split_ifs with h
  · subst h
    rw [inter_self, volume_real_cell hd]
    have : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [Complex.real_smul]; push_cast; field_simp
  · rw [volume_real_cell_inter hd (fun h' => h (Fin.ext h'))]; simp

theorem orthonormal_v (hd : 0 < d) : Orthonormal ℂ (v d) := by
  rw [orthonormal_iff_ite]
  intro j k; exact inner_v hd j k

/-- `U_d : ℂ^d → L²(ℝ)`, `U_d x = ∑ x_k √d 1_{I_{d,k}}`. -/
noncomputable def Ulin (d : ℕ) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] L2R where
  toFun x := ∑ k, x k • v d k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

noncomputable def U (d : ℕ) : EuclideanSpace ℂ (Fin d) →L[ℂ] L2R := LinearMap.toContinuousLinearMap (Ulin d)

theorem U_apply (x : EuclideanSpace ℂ (Fin d)) : U d x = ∑ k, x k • v d k := rfl

theorem inner_U (hd : 0 < d) (x y : EuclideanSpace ℂ (Fin d)) :
    (inner ℂ (U d x) (U d y) : ℂ) = inner ℂ x y := by
  rw [U_apply, U_apply, (orthonormal_v hd).inner_sum, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-- `U_d† U_d = I`. -/
theorem U_adj_U (hd : 0 < d) : adjoint (U d) ∘L U d = ContinuousLinearMap.id ℂ _ := by
  ext1 x
  apply ext_inner_right ℂ
  intro y
  rw [comp_apply, adjoint_inner_left, inner_U hd, id_apply]

theorem vol_half_ne_top : volume (Icc (-1/2:ℝ) (1/2)) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

/-- `ψ₁ = 1_{[-1/2,1/2]}`. -/
noncomputable def ψ₁ : L2R :=
  indicatorConstLp 2 (measurableSet_Icc (a := (-1/2:ℝ)) (b := 1/2)) vol_half_ne_top (1 : ℂ)

/-- `c_d = d^{-1/2}(1,…,1)`. -/
noncomputable def cvec (d : ℕ) : EuclideanSpace ℂ (Fin d) := fun _ => ((Real.sqrt d)⁻¹ : ℂ)

theorem cell_subset (k : Fin d) : cell d k ⊆ Icc (-1/2:ℝ) (1/2) := by
  intro x hx
  have hk := k.isLt
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have h1 : (0:ℝ) ≤ (k:ℝ) / d := by positivity
  have h2 : ((k:ℝ) + 1) / d ≤ 1 := by
    rw [div_le_one hd']; exact_mod_cast hk
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- `U_d c_d = ψ₁` (as elements of `L²(ℝ)`). -/
theorem U_c (hd : 0 < d) : U d (cvec d) = ψ₁ := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd'
  -- ⟪U c, ψ₁⟫ = 1, ‖U c‖² = 1, ‖ψ₁‖² = 1
  have h1 : (inner ℂ (U d (cvec d)) ψ₁ : ℂ) = 1 := by
    rw [U_apply, sum_inner]
    have : ∀ k : Fin d, (inner ℂ (cvec d k • v d k) ψ₁ : ℂ) = 1 / d := by
      intro k
      rw [inner_smul_left, v, ψ₁, L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_cell d k)
        measurableSet_Icc (volume_cell_ne_top (d := d) k) vol_half_ne_top,
        inter_eq_left.mpr (cell_subset k), volume_real_cell hd]
      simp only [cvec, RCLike.inner_apply, map_one, Complex.conj_ofReal, map_inv₀]
      rw [Complex.real_smul]
      have : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      push_cast; field_simp
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  have h2 : (inner ℂ (U d (cvec d)) (U d (cvec d)) : ℂ) = 1 := by
    rw [U_apply, (orthonormal_v hd).inner_sum]
    have hc : ∀ k, cvec d k = ((Real.sqrt d)⁻¹ : ℂ) := fun k => rfl
    simp_rw [hc]
    have : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hsq : (Real.sqrt d : ℂ) * Real.sqrt d = d := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hd'.le]; simp
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_inv₀, Complex.conj_ofReal,
      ← mul_inv, hsq]
    have : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  have h3 : (inner ℂ ψ₁ ψ₁ : ℂ) = 1 := by
    rw [ψ₁, L2.inner_indicatorConstLp_indicatorConstLp measurableSet_Icc measurableSet_Icc
      vol_half_ne_top vol_half_ne_top, inter_self, Real.volume_real_Icc]
    norm_num
  have h0 : ‖U d (cvec d) - ψ₁‖ ^ 2 = 0 := by
    have := @norm_sub_sq ℂ _ _ _ _ (U d (cvec d)) ψ₁
    rw [this, ← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h2, h3, h1]
    norm_num
  have : ‖U d (cvec d) - ψ₁‖ = 0 := by
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-! ## Proposition 3.7 -/

open EulerianBridge.FrameBridge

variable {C2d F : Type*}
  [NormedAddCommGroup C2d] [InnerProductSpace ℂ C2d] [CompleteSpace C2d]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Proposition 3.7: for `B = 𝒱_ħ U_d M_V(ζ)`, with Hall's unitarity and Vourdas's semi-unitarity as
hypotheses: `B†B = M†M`, `BB† = 𝒱U_dU_d†𝒱†`, `B M† c_d = 𝒱ψ₁`, and both are orthogonal projections. -/
theorem frame_factorisation (hd : 0 < d) (V : L2R →L[ℂ] F) (M : C2d →L[ℂ] EuclideanSpace ℂ (Fin d))
    (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ L2R)
    (hM : M ∘L adjoint M = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) :
    adjoint (B V (U d) M) ∘L B V (U d) M = adjoint M ∘L M ∧
    B V (U d) M ∘L adjoint (B V (U d) M) = V ∘L U d ∘L adjoint (U d) ∘L adjoint V ∧
    B V (U d) M (adjoint M (cvec d)) = V ψ₁ ∧
    (IsIdempotentElem (adjoint (B V (U d) M) ∘L B V (U d) M) ∧
      IsSelfAdjoint (adjoint (B V (U d) M) ∘L B V (U d) M)) ∧
    (IsIdempotentElem (B V (U d) M ∘L adjoint (B V (U d) M)) ∧
      IsSelfAdjoint (B V (U d) M ∘L adjoint (B V (U d) M))) :=
  ⟨B_adj_B V (U d) M hV (U_adj_U hd), B_B_adj V (U d) M hM,
    B_reconstruction V (U d) M hM (cvec d) ψ₁ (U_c hd),
    B_adj_B_proj V (U d) M hV (U_adj_U hd) hM, B_B_adj_proj V (U d) M hV (U_adj_U hd) hM⟩

end EulerianBridge.StepFrame
