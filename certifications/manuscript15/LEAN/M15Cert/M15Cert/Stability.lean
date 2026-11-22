/-
Manuscript 15, Section 7.9, Remark 7.21 -- the stability inequality (267):
for Borel probability measures μ, ν on ℝ and every real θ,
  |M[f_μ](θ) - M[f_ν](θ)| ≤ (|θ|³/2) W₁(μ, ν),
where M[f](θ) = 1/4 + (θ²/4) f(θ)² e^{iθ} is the polar reconstruction (257),
f_μ(θ) = ∫ e^{iθx} dμ(x) (Mathlib's `charFun`), and W₁ is the Kantorovich
transport distance, defined as the infimum over all couplings of ∫ |x - y|.
W₁ takes values in [0, ∞]; no moment assumption and no symmetry are needed.
-/
import M15Cert.Kernel

open Complex MeasureTheory

namespace M15

/-- The polar reconstruction about the cusp 1/4, Eq. (257). -/
noncomputable def polarM (f : ℝ → ℂ) (θ : ℝ) : ℂ := 1 / 4 + θ ^ 2 / 4 * f θ ^ 2 * Complex.exp (θ * I)

/-- Couplings of two measures on ℝ. -/
def couplings (μ ν : Measure ℝ) : Set (Measure (ℝ × ℝ)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

/-- The Kantorovich–Wasserstein distance W₁ (with values in [0, ∞]). -/
noncomputable def W1 (μ ν : Measure ℝ) : ENNReal :=
  ⨅ π ∈ couplings μ ν, ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂π

lemma norm_cexp_sub_cexp_le (a b : ℝ) :
    ‖Complex.exp (a * I) - Complex.exp (b * I)‖ ≤ |a - b| := by
  have h : Complex.exp (a * I) - Complex.exp (b * I) =
      Complex.exp (b * I) * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

lemma charFun_map_fst (π : Measure (ℝ × ℝ)) (θ : ℝ) :
    charFun (π.map Prod.fst) θ = ∫ p, Complex.exp (θ * p.1 * I) ∂π := by
  rw [charFun_apply_real, integral_map measurable_fst.aemeasurable (by fun_prop)]

lemma charFun_map_snd (π : Measure (ℝ × ℝ)) (θ : ℝ) :
    charFun (π.map Prod.snd) θ = ∫ p, Complex.exp (θ * p.2 * I) ∂π := by
  rw [charFun_apply_real, integral_map measurable_snd.aemeasurable (by fun_prop)]

/-- The coupling estimate: |f_μ(θ) - f_ν(θ)| ≤ |θ| ∫ |x - y| dπ for every coupling π. -/
theorem charFun_sub_le_coupling (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (θ : ℝ) :
    ENNReal.ofReal ‖charFun (π.map Prod.fst) θ - charFun (π.map Prod.snd) θ‖ ≤
      ENNReal.ofReal |θ| * ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂π := by
  have hint : ∀ g : ℝ × ℝ → ℝ, Measurable g →
      Integrable (fun p => Complex.exp (θ * g p * I)) π := by
    intro g hg
    refine (integrable_const (1 : ℂ)).mono (by fun_prop) (Filter.Eventually.of_forall ?_)
    intro p
    rw [show (θ : ℂ) * g p * I = ((θ * g p : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    simp
  rw [charFun_map_fst, charFun_map_snd, ← integral_sub (hint _ measurable_fst)
    (hint _ measurable_snd)]
  calc ENNReal.ofReal ‖∫ p, (Complex.exp (θ * p.1 * I) - Complex.exp (θ * p.2 * I)) ∂π‖
      = ‖∫ p, (Complex.exp (θ * p.1 * I) - Complex.exp (θ * p.2 * I)) ∂π‖ₑ := by
        rw [ofReal_norm]
    _ ≤ ∫⁻ p, ‖Complex.exp (θ * p.1 * I) - Complex.exp (θ * p.2 * I)‖ₑ ∂π :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ p, ENNReal.ofReal |θ| * ENNReal.ofReal |p.1 - p.2| ∂π := by
        refine lintegral_mono fun p => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (abs_nonneg θ)]
        apply ENNReal.ofReal_le_ofReal
        have := norm_cexp_sub_cexp_le (θ * p.1) (θ * p.2)
        push_cast at this
        calc _ ≤ |θ * p.1 - θ * p.2| := this
          _ = |θ| * |p.1 - p.2| := by rw [← mul_sub, abs_mul]
    _ = ENNReal.ofReal |θ| * ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂π := by
        rw [lintegral_const_mul]
        fun_prop

/-- Pointwise algebra: |M[f](θ) - M[g](θ)| ≤ (θ²/2)|f(θ) - g(θ)| when |f(θ)|, |g(θ)| ≤ 1. -/
lemma norm_polarM_sub_le (f g : ℝ → ℂ) (θ : ℝ) (hf : ‖f θ‖ ≤ 1) (hg : ‖g θ‖ ≤ 1) :
    ‖polarM f θ - polarM g θ‖ ≤ θ ^ 2 / 2 * ‖f θ - g θ‖ := by
  have h : polarM f θ - polarM g θ =
      ((θ ^ 2 / 4 : ℝ) : ℂ) * ((f θ - g θ) * (f θ + g θ)) * Complex.exp (θ * I) := by
    unfold polarM; push_cast; ring
  rw [h, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : ‖f θ + g θ‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
  have hd : 0 ≤ ‖f θ - g θ‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hs hd, sq_nonneg θ]

/-- Eq. (267), coupling form: for every coupling π of μ and ν. -/
theorem stability_coupling (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (θ : ℝ) :
    ENNReal.ofReal ‖polarM (charFun (π.map Prod.fst)) θ - polarM (charFun (π.map Prod.snd)) θ‖ ≤
      ENNReal.ofReal (|θ| ^ 3 / 2) * ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂π := by
  have h1 := norm_polarM_sub_le (charFun (π.map Prod.fst)) (charFun (π.map Prod.snd)) θ
    (norm_charFun_le_one θ) (norm_charFun_le_one θ)
  calc ENNReal.ofReal ‖polarM (charFun (π.map Prod.fst)) θ - polarM (charFun (π.map Prod.snd)) θ‖
      ≤ ENNReal.ofReal (θ ^ 2 / 2 * ‖charFun (π.map Prod.fst) θ - charFun (π.map Prod.snd) θ‖) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (θ ^ 2 / 2) *
          ENNReal.ofReal ‖charFun (π.map Prod.fst) θ - charFun (π.map Prod.snd) θ‖ :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (θ ^ 2 / 2) *
          (ENNReal.ofReal |θ| * ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂π) := by
        gcongr; exact charFun_sub_le_coupling π θ
    _ = ENNReal.ofReal (|θ| ^ 3 / 2) * ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂π := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [← sq_abs θ]; ring

/-- Eq. (267): |M[f_μ](θ) - M[f_ν](θ)| ≤ (|θ|³/2) W₁(μ, ν) for all Borel probability
measures μ, ν on ℝ and every real θ (no symmetry assumed; W₁ may be infinite). -/
theorem cardioid_stability (μ ν : Measure ℝ) (θ : ℝ) :
    ENNReal.ofReal ‖polarM (charFun μ) θ - polarM (charFun ν) θ‖ ≤
      ENNReal.ofReal (|θ| ^ 3 / 2) * W1 μ ν := by
  by_cases hθ : θ = 0
  · subst hθ; simp [polarM]
  have hc0 : ENNReal.ofReal (|θ| ^ 3 / 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  unfold W1
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun π => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hπ => ?_
  obtain ⟨hprob, h1, h2⟩ := hπ
  have := hprob
  have := stability_coupling π θ
  rwa [h1, h2] at this

/-- Eq. (267) in real form, when W₁(μ, ν) is finite (e.g. finite first moments). -/
theorem cardioid_stability_real (μ ν : Measure ℝ) (θ : ℝ) (hW : W1 μ ν ≠ ⊤) :
    ‖polarM (charFun μ) θ - polarM (charFun ν) θ‖ ≤ |θ| ^ 3 / 2 * (W1 μ ν).toReal := by
  have h := cardioid_stability μ ν θ
  have h' := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW)).2 h
  rwa [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at h'

/-- The product coupling shows that the set of couplings of two probability measures is
nonempty, so W₁(μ, ν) is the infimum over a nonempty family. -/
theorem prod_mem_couplings (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ.prod ν ∈ couplings μ ν :=
  ⟨inferInstance, by simp, by simp⟩

end M15
