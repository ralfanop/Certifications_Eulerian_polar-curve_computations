import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Spectrum of a bounded operator that is diagonal in a Hilbert basis

Let `b` be a Hilbert basis of a real Hilbert space `H`, indexed by `ℕ`, and let `R` be a bounded
operator acting diagonally, `⟨e_n, R f⟩ = β_n ⟨e_n, f⟩`, with `β_n → 0`. Then

* `spectrum_subset_insert_zero_range`: `spectrum ℝ R ⊆ {0} ∪ {β_n}`; for `μ` outside this set
  the inverse of `μ - R` is the bounded diagonal multiplier `(μ - β_n)⁻¹`;
* `eigen_mem_spectrum`: an eigenvalue lies in the spectrum;
* `isolated_of_ne_zero`: every nonzero point of `{0} ∪ {β_n}` is isolated in it;
* `zero_mem_closure`: if every `β_n` is a nonzero spectral value, `0` is an accumulation point.
-/

noncomputable section

namespace GegenbauerFock.DiagonalSpectrum

open Filter Topology

local notation "ℓ²" => lp (fun _ : ℕ => ℝ) 2

/-- Coefficientwise comparison of `ℓ²` norms. -/
theorem l2_norm_mono {f g : ℓ²} (h : ∀ i, ‖f i‖ ≤ ‖g i‖) : ‖f‖ ≤ ‖g‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  apply lp.norm_le_of_tsum_le hp (norm_nonneg g)
  rw [lp.norm_rpow_eq_tsum hp]
  exact Summable.tsum_le_tsum (fun i => Real.rpow_le_rpow (norm_nonneg _) (h i) hp.le)
    ((lp.memℓp f).summable hp) ((lp.memℓp g).summable hp)

/-- A bounded multiplier preserves `ℓ²`. -/
theorem memℓp_mul (c : ℕ → ℝ) {C : ℝ} (hC : ∀ n, ‖c n‖ ≤ C) (a : ℓ²) :
    Memℓp (fun n => c n * a n) 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  apply memℓp_gen
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (((lp.memℓp a).summable hp).mul_left (C ^ (2 : ENNReal).toReal))
  rw [norm_mul, ← Real.mul_rpow hC0 (norm_nonneg _)]
  exact Real.rpow_le_rpow (by positivity)
    (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)) hp.le

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bounded diagonal multiplier `f ↦ ∑ c_n ⟨e_n, f⟩ e_n`. -/
def mulOp (b : HilbertBasis ℕ ℝ H) (c : ℕ → ℝ) (C : ℝ) (hC : ∀ n, ‖c n‖ ≤ C) : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := fun f => b.repr.symm ⟨fun n => c n * b.repr f n, memℓp_mul c hC (b.repr f)⟩
      map_add' := fun f g => by
        rw [← map_add]; congr 1; ext n
        simp [mul_add]
      map_smul' := fun r f => by
        rw [← map_smul]; congr 1; ext n
        simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    C (fun f => by
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      calc _ ≤ ‖C • b.repr f‖ := l2_norm_mono fun i => by
              simp only [norm_mul, lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg hC0]
              exact mul_le_mul_of_nonneg_right (by simpa using hC i) (abs_nonneg _)
        _ ≤ ‖C‖ * ‖b.repr f‖ := norm_smul_le _ _
        _ = C * ‖f‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hC0, LinearIsometryEquiv.norm_map])

theorem mulOp_repr (b : HilbertBasis ℕ ℝ H) (c : ℕ → ℝ) (C : ℝ) (hC : ∀ n, ‖c n‖ ≤ C)
    (f : H) (n : ℕ) : b.repr (mulOp b c C hC f) n = c n * b.repr f n := by
  simp [mulOp]

/-- Outside `{0} ∪ {β_n}` the operator `μ - R` is invertible. -/
theorem spectrum_subset_insert_zero_range (b : HilbertBasis ℕ ℝ H) (β : ℕ → ℝ)
    (R : H →L[ℝ] H) (hR : ∀ f n, b.repr (R f) n = β n * b.repr f n)
    (hβ : Tendsto β atTop (𝓝 0)) :
    spectrum ℝ R ⊆ insert 0 (Set.range β) := by
  intro μ hμ
  by_contra hno
  simp only [Set.mem_insert_iff, Set.mem_range, not_or, not_exists] at hno
  obtain ⟨hμ0, hμβ⟩ := hno
  have hne : ∀ n, μ - β n ≠ 0 := fun n => sub_ne_zero.mpr fun h => hμβ n h.symm
  let c : ℕ → ℝ := fun n => (μ - β n)⁻¹
  have hc : Tendsto c atTop (𝓝 μ⁻¹) := by
    have := (tendsto_const_nhds (x := μ)).sub hβ
    simpa [c] using this.inv₀ (by simpa using hμ0)
  obtain ⟨C, hC⟩ := hc.norm.bddAbove_range
  have hCn : ∀ n, ‖c n‖ ≤ C := fun n => hC ⟨n, rfl⟩
  have hA : ∀ g n, b.repr ((algebraMap ℝ (H →L[ℝ] H) μ - R) g) n =
      (μ - β n) * b.repr g n := by
    intro g n
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_sub, map_smul, lp.coeFn_sub, lp.coeFn_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hR]
    ring
  apply hμ
  refine ⟨⟨algebraMap ℝ (H →L[ℝ] H) μ - R, mulOp b c C hCn, ?_, ?_⟩, rfl⟩
  · ext1 f
    apply b.repr.injective
    ext n
    rw [ContinuousLinearMap.mul_apply, hA, mulOp_repr, ContinuousLinearMap.one_apply,
      ← mul_assoc, mul_inv_cancel₀ (hne n), one_mul]
  · ext1 f
    apply b.repr.injective
    ext n
    rw [ContinuousLinearMap.mul_apply, mulOp_repr, hA, ContinuousLinearMap.one_apply,
      ← mul_assoc, inv_mul_cancel₀ (hne n), one_mul]

/-- An eigenvalue of a bounded operator lies in its spectrum. -/
theorem eigen_mem_spectrum (R : H →L[ℝ] H) {r : ℝ} {e : H} (he : e ≠ 0) (hRe : R e = r • e) :
    r ∈ spectrum ℝ R := by
  rintro ⟨u, hu⟩
  apply he
  have h0 : (u : H →L[ℝ] H) e = 0 := by
    rw [hu, Algebra.algebraMap_eq_smul_one]
    simp [hRe]
  have : ((↑u⁻¹ * ↑u : H →L[ℝ] H)) e = e := by rw [Units.inv_mul]; rfl
  rw [ContinuousLinearMap.mul_apply, h0, map_zero] at this
  exact this.symm

/-- Every nonzero point of `{0} ∪ {β_n}` is isolated, when `β_n → 0`. -/
theorem isolated_of_ne_zero (β : ℕ → ℝ) (hβ : Tendsto β atTop (𝓝 0)) (S : Set ℝ)
    (hS : S ⊆ insert 0 (Set.range β)) {μ : ℝ} (hμ0 : μ ≠ 0) :
    ∀ᶠ ν in 𝓝[≠] μ, ν ∉ S := by
  have hpos : 0 < |μ| / 2 := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hβ) (|μ| / 2) hpos
  let F : Set ℝ := (β '' {n | n < N}) \ {μ}
  have hF : IsClosed F := ((Set.finite_lt_nat N).image β).diff.isClosed
  have hU : ∀ᶠ ν in 𝓝 μ, ν ∈ Fᶜ ∩ Metric.ball μ (|μ| / 2) :=
    Filter.inter_mem (hF.isOpen_compl.mem_nhds (by simp [F]))
      (Metric.ball_mem_nhds μ hpos)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hU] with ν hν hνμ hνS
  obtain ⟨hνF, hνb⟩ := hν
  rw [Metric.mem_ball, Real.dist_eq] at hνb
  rcases hS hνS with h0 | ⟨n, rfl⟩
  · subst h0; simp at hνb; linarith [abs_nonneg μ]
  · by_cases hn : n < N
    · exact hνF ⟨⟨n, hn, rfl⟩, hνμ⟩
    · have h := hN n (not_lt.mp hn)
      rw [Real.dist_eq, sub_zero] at h
      have : |μ| ≤ |μ - β n| + |β n| := by
        calc |μ| = |(μ - β n) + β n| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [abs_sub_comm] at hνb
      linarith

/-- If every `β_n` is a nonzero spectral value and `β_n → 0`, then `0` is an accumulation
point of the spectrum. -/
theorem zero_mem_closure (β : ℕ → ℝ) (hβ : Tendsto β atTop (𝓝 0)) (S : Set ℝ)
    (hmem : ∀ n, β n ∈ S) (hne : ∀ n, β n ≠ 0) : (0 : ℝ) ∈ closure (S \ {0}) :=
  mem_closure_of_tendsto hβ (Eventually.of_forall fun n => ⟨hmem n, hne n⟩)

end GegenbauerFock.DiagonalSpectrum
