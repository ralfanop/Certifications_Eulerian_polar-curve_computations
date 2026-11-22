/-
Manuscript 15, Section 7.9, Theorem 7.19 -- identification of the triangular density.

Let V₁, V₂ be independent and uniform on [0,1] and U₁, U₂ independent and uniform on
[-1/2, 1/2].  We prove:
* the law of V₁ + V₂ has density 1 - |x - 1| on [0,2] (zero elsewhere), the cardinal
  B-spline of order two;
* the law of 1 + U₁ + U₂ is the same triangular law (1 + U₁ + U₂ = V₁ + V₂, V_k = U_k + 1/2);
* the characteristic function of the triangular law is e^{iθ} r_E(θ)² = e^{iθ} f₂(θ);
* Eq. (265): c_Mand(θ) - 1/4 = (θ²/4) E e^{iθ(1+U₁+U₂)}, for every real θ;
* B(e^{iθ}) = E e^{iθV₁} for -π < θ ≤ π.
-/
import M15Cert.Kernel

open MeasureTheory Complex Set

namespace M15

/-- The uniform law on [0,1]. -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Icc 0 1)

/-- The uniform law on [-1/2, 1/2]. -/
noncomputable def unifC : Measure ℝ := volume.restrict (Icc (-1 / 2) (1 / 2))

instance : IsProbabilityMeasure unif01 := ⟨by simp [unif01, Real.volume_Icc]⟩
instance : IsProbabilityMeasure unifC := ⟨by norm_num [unifC, Real.volume_Icc]⟩

/-- The triangular law with density 1 - |x - 1| on [0,2] (`ENNReal.ofReal` vanishes
outside [0,2], where 1 - |x - 1| ≤ 0). -/
noncomputable def triLaw : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (1 - |x - 1|)

/-- The overlap of [0,1] with [z-1, z] has length 1 - |z - 1| (clipped at 0). -/
theorem volume_overlap (z : ℝ) :
    volume {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ z - x ∈ Icc (0 : ℝ) 1} = ENNReal.ofReal (1 - |z - 1|) := by
  have hset : {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ z - x ∈ Icc (0 : ℝ) 1} =
      Icc (max 0 (z - 1)) (min 1 z) := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, by linarith, by linarith⟩
  rw [hset, Real.volume_Icc]
  congr 1
  rcases le_total z 1 with h | h
  · rw [min_eq_right h, max_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg (by linarith)]

/-- Theorem 7.19: the law of V₁ + V₂ is the triangular law. -/
theorem law_sum_unif01 :
    (unif01.prod unif01).map (fun p : ℝ × ℝ => p.1 + p.2) = triLaw := by
  ext s hs
  have hT : ∀ x : ℝ, MeasurableSet {z : ℝ | z - x ∈ Icc (0 : ℝ) 1} :=
    fun x => measurableSet_Icc.preimage (measurable_id.sub_const x)
  have hT' : ∀ z : ℝ, MeasurableSet {x : ℝ | z - x ∈ Icc (0 : ℝ) 1} :=
    fun z => measurableSet_Icc.preimage (measurable_const.sub measurable_id)
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply ((by fun_prop :
    Measurable fun p : ℝ × ℝ => p.1 + p.2) hs), triLaw, withDensity_apply _ hs]
  -- inner measure, by translation invariance
  have inner : ∀ x : ℝ, unif01 (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' s)) =
      ∫⁻ z in s, {z : ℝ | z - x ∈ Icc (0 : ℝ) 1}.indicator 1 z := by
    intro x
    rw [lintegral_indicator_one (hT x), Measure.restrict_apply (hT x), unif01,
      Measure.restrict_apply (measurable_const_add x hs |> fun h => by
        simpa [Set.preimage] using h)]
    conv_rhs => rw [← measure_preimage_add (μ := (volume : Measure ℝ)) x]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, add_sub_cancel_left]
    tauto
  -- the overlap as an integral over x
  have outer : ∀ z : ℝ, ENNReal.ofReal (1 - |z - 1|) =
      ∫⁻ x in Icc (0 : ℝ) 1, {x : ℝ | z - x ∈ Icc (0 : ℝ) 1}.indicator 1 x := by
    intro z
    rw [← volume_overlap, lintegral_indicator_one (hT' z), Measure.restrict_apply (hT' z)]
    congr 1; ext x; simp only [mem_ofPred_eq, mem_inter_iff]; tauto
  simp_rw [inner, outer]
  change ∫⁻ x in Icc (0 : ℝ) 1, ∫⁻ z in s, _ = _
  have hind : ∀ x z : ℝ, {z : ℝ | z - x ∈ Icc (0 : ℝ) 1}.indicator (1 : ℝ → ENNReal) z =
      {x : ℝ | z - x ∈ Icc (0 : ℝ) 1}.indicator 1 x := by
    intro x z; simp [Set.indicator]
  simp_rw [hind]
  refine lintegral_lintegral_swap ?_
  apply Measurable.aemeasurable
  have : Function.uncurry (fun (x z : ℝ) => {x' : ℝ | z - x' ∈ Icc (0 : ℝ) 1}.indicator
      (1 : ℝ → ENNReal) x) =
      {p : ℝ × ℝ | p.2 - p.1 ∈ Icc (0 : ℝ) 1}.indicator 1 := by
    funext p; simp [Set.indicator, Function.uncurry]
  rw [this]
  exact measurable_one.indicator
    (measurableSet_Icc.preimage (measurable_snd.sub measurable_fst))

/-- The characteristic function of the uniform law on [0,1]: e^{iθ/2} r_E(θ). -/
theorem charFun_unif01 (θ : ℝ) :
    charFun unif01 θ = Complex.exp (θ / 2 * I) * (rE θ : ℂ) := by
  rw [charFun_apply_real, unif01, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  by_cases hθ : θ = 0
  · subst hθ; simp [rE]
  · have hc : (θ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hθ) I_ne_zero
    have e : ∀ x : ℝ, Complex.exp (θ * x * I) = Complex.exp (((θ : ℂ) * I) * x) := by
      intro x; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [exp_sub_one_eq θ]
    have hθ' : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
    field_simp

/-- The characteristic function of the triangular law is e^{iθ} r_E(θ)². -/
theorem charFun_triLaw (θ : ℝ) :
    charFun triLaw θ = Complex.exp (θ * I) * (rE θ : ℂ) ^ 2 := by
  rw [← law_sum_unif01, ProbabilityTheory.charFun_map_add_prod_eq_mul, Pi.mul_apply, charFun_unif01]
  have : Complex.exp (θ / 2 * I) * Complex.exp (θ / 2 * I) = Complex.exp (θ * I) := by
    rw [← Complex.exp_add]; ring_nf
  linear_combination (rE θ : ℂ) ^ 2 * this

/-- The cardioid through the triangular law: c_Mand(θ) - 1/4 = (θ²/4) ∫ e^{iθx} dT(x). -/
theorem cardioid_triLaw (θ : ℝ) : cMand θ - 1 / 4 = (θ : ℂ) ^ 2 / 4 * charFun triLaw θ := by
  rw [charFun_triLaw]
  have h := exp_sub_one_eq θ
  have hsq : Complex.exp (θ / 2 * I) ^ 2 = Complex.exp (θ * I) := by
    rw [← Complex.exp_nat_mul]; ring_nf
  have hc : cMand θ - 1 / 4 = -(Complex.exp (θ * I) - 1) ^ 2 / 4 := by unfold cMand; ring
  rw [hc, h]
  have hI : I ^ 2 = -1 := Complex.I_sq
  rw [← hsq]
  linear_combination (-(θ : ℂ) ^ 2 * (rE θ : ℂ) ^ 2 * Complex.exp (θ / 2 * I) ^ 2 / 4) * hI

/-- The translation x ↦ x + 1/2 carries Unif[-1/2, 1/2] to Unif[0,1]. -/
theorem map_unifC : unifC.map (fun x => x + 1 / 2) = unif01 := by
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA, unifC, unif01,
    Measure.restrict_apply (hA.preimage (by fun_prop)), Measure.restrict_apply hA]
  rw [← measure_preimage_add_right (μ := (volume : Measure ℝ)) (1 / 2) (A ∩ Icc 0 1)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩

/-- The law of 1 + U₁ + U₂ is the triangular law. -/
theorem law_one_add_sum_unifC :
    (unifC.prod unifC).map (fun p : ℝ × ℝ => 1 + p.1 + p.2) = triLaw := by
  rw [← law_sum_unif01, ← map_unifC, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp, Prod.map]
  ring

/-- Eq. (265): c_Mand(θ) - 1/4 = (θ²/4) E e^{iθ(1+U₁+U₂)}, for every real θ. -/
theorem cardioid_probabilistic (θ : ℝ) :
    cMand θ - 1 / 4 =
      (θ : ℂ) ^ 2 / 4 * ∫ p, Complex.exp (θ * (1 + p.1 + p.2) * I) ∂(unifC.prod unifC) := by
  rw [cardioid_triLaw, ← law_one_add_sum_unifC, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop)]
  push_cast
  rfl

/-- On the unit circle the Eulerian factor is the characteristic function of Unif[0,1]:
B(e^{iθ}) = E e^{iθV₁} for -π < θ ≤ π. -/
theorem eulerianB_eq_charFun_unif01 (θ : ℝ) (h1 : -Real.pi < θ) (h2 : θ ≤ Real.pi) :
    eulerianB (Complex.exp (θ * I)) = charFun unif01 θ := by
  rw [charFun_unif01]
  unfold eulerianB
  by_cases hθ : θ = 0
  · subst hθ; simp [rE]
  · have hu : Complex.exp (θ * I) ≠ 1 := by
      intro h
      rcases Complex.exp_eq_one_iff.1 h with ⟨n, hn⟩
      have him := congrArg Complex.im hn
      simp at him
      have hpi := Real.pi_pos
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 hn0
        nlinarith
      · subst hn0; simp at him; exact hθ him
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
        nlinarith
    have hlog : Complex.log (Complex.exp (θ * I)) = θ * I := by
      apply Complex.log_exp <;> simp [h1, h2]
    simp only [hu, ↓reduceIte, hlog]
    rw [exp_sub_one_eq θ]
    have hθ' : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
    field_simp

end M15
