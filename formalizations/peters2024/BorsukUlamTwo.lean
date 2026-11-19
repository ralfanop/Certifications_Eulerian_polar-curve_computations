import Mathlib
import Peters2024

/-!
# Borsuk–Ulam in dimension two, from Mathlib alone

Theorem 1.1 of Peters, Alfano, Smith, Tozzi and Vergili, Filomat 38 (2024), 793–802,
in the dimension used by Sections 5 and 6 of the article: every continuous map
`f : S² → ℝ²` identifies a pair of antipodal points.

This file imports only Mathlib and the base module `Peters2024`. It does not use the
external general-dimensional proof, so the dimension-two results of the article
(5.4, 5.5, 5.6, 6.2, 6.3) obtained here depend on Mathlib only.

## Proof

Write `g x = f x - f (-x)`, read as a complex number; `g` is continuous and odd.
Suppose `g` never vanishes.

* Spherical coordinates `ψ (θ, t) = cos t • (cos θ • e₀ + sin θ • e₁) + sin t • e₂`
  give a continuous map `ℝ × ℝ → S²` with `ψ (θ + π, -t) = -ψ (θ, t)` and
  `ψ (θ, π / 2) = e₂` for every `θ`.
* `G = g ∘ ψ` is a continuous nowhere-vanishing map on the plane. The plane is simply
  connected and locally path connected and `Complex.exp` is a covering map onto
  `{0}ᶜ`, so `G = exp ∘ L` for a continuous `L` (`Complex.isCoveringMapOn_exp` and
  `IsCoveringMapOn.existsUnique_continuousMap_lifts`).
* Uniqueness of lifts gives a constant `c` with `exp c = -1` and
  `L (θ + π, -t) = L (θ, t) + c`, hence `L (θ + 2π, t) = L (θ, t) + 2c`.
* Uniqueness of lifts on the line `t = π / 2`, where `G` is constant, gives
  `L (θ, π / 2) = L (0, π / 2)`.
* Therefore `2c = 0`, so `exp c = 1`, contradicting `exp c = -1`.

Status: written without a local Lean toolchain. The statements below count as proved
only after the workflow `peters2024-borsuk-two.yml` has compiled this file and printed
the standard axioms for every audited declaration.
-/

namespace Peters2024
open Set Metric
open scoped Real
noncomputable section

/-! ## Lifts through the complex exponential -/

/-- Two continuous logarithms of the same map on a simply connected, locally path
connected space coincide as soon as they agree at one point. -/
theorem eq_of_exp_comp_eq {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocPathConnectedSpace A] (F₁ F₂ : C(A, ℂ)) (a₀ : A) (h₀ : F₁ a₀ = F₂ a₀)
    (h : ∀ a, Complex.exp (F₁ a) = Complex.exp (F₂ a)) : F₁ = F₂ := by
  have hu := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨fun a => Complex.exp (F₂ a), Complex.continuous_exp.comp F₂.continuous⟩ : C(A, ℂ))
    (a₀ := a₀) (e₀ := F₂ a₀) rfl
    (fun a => Set.mem_compl_singleton_iff.mpr (Complex.exp_ne_zero (F₂ a)))
  exact hu.unique ⟨h₀, funext h⟩ ⟨rfl, funext fun _ => rfl⟩

/-- The covering-space core of the argument. A continuous complex function on the
plane that changes sign under `(θ, t) ↦ (θ + π, -t)` and is constant along the line
`t = π / 2` has a zero. -/
theorem exists_zero_of_antiperiodic (G : ℝ × ℝ → ℂ) (hG : Continuous G)
    (hanti : ∀ θ t : ℝ, G (θ + π, -t) = -G (θ, t))
    (hpole : ∀ θ : ℝ, G (θ, π / 2) = G (0, π / 2)) :
    ∃ a, G a = 0 := by
  by_contra hne
  have hne' : ∀ a, G a ≠ 0 := fun a ha => hne ⟨a, ha⟩
  -- A continuous logarithm `L` of `G` on the plane.
  obtain ⟨L, -, hL⟩ := (Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨G, hG⟩ : C(ℝ × ℝ, ℂ)) (a₀ := ((0, 0) : ℝ × ℝ)) (e₀ := Complex.log (G (0, 0)))
    (Complex.exp_log (hne' (0, 0)))
    (fun a => Set.mem_compl_singleton_iff.mpr (hne' a))).exists
  have hexp : ∀ a, Complex.exp (L a) = G a := fun a => congrFun hL a
  -- The increment of `L` under the antipodal symmetry of the chart.
  obtain ⟨c, hc_def⟩ : ∃ c : ℂ, c = L (π, 0) - L (0, 0) := ⟨_, rfl⟩
  have hc : Complex.exp c = -1 := by
    have h1 : Complex.exp (L (π, 0)) = -Complex.exp (L (0, 0)) := by
      rw [hexp, hexp]
      have h := hanti 0 0
      rwa [zero_add, neg_zero] at h
    rw [hc_def, Complex.exp_sub, h1, neg_div, div_self (Complex.exp_ne_zero _)]
  -- `L (θ + π, -t) = L (θ, t) + c`, by uniqueness of lifts on the plane.
  have h2 : ∀ θ t : ℝ, L (θ + π, -t) = L (θ, t) + c := by
    have hcont : Continuous fun a : ℝ × ℝ => L (a.1 + π, -a.2) - c := by
      first
        | exact (L.continuous.comp
            ((continuous_fst.add continuous_const).prodMk continuous_snd.neg)).sub
            continuous_const
        | fun_prop
    have key : (⟨fun a : ℝ × ℝ => L (a.1 + π, -a.2) - c, hcont⟩ : C(ℝ × ℝ, ℂ)) = L := by
      refine eq_of_exp_comp_eq _ _ ((0, 0) : ℝ × ℝ) ?_ ?_
      · show L ((0 : ℝ) + π, -(0 : ℝ)) - c = L (0, 0)
        rw [zero_add, neg_zero, hc_def]
        ring
      · rintro ⟨θ, t⟩
        show Complex.exp (L (θ + π, -t) - c) = Complex.exp (L (θ, t))
        rw [Complex.exp_sub, hc, hexp, hexp, hanti, neg_div_neg_eq, div_one]
    intro θ t
    have h' : L (θ + π, -t) - c = L (θ, t) := DFunLike.congr_fun key (θ, t)
    linear_combination h'
  -- `L` is constant along the line `t = π / 2`, by uniqueness of lifts on the real line.
  have h3 : ∀ θ : ℝ, L (θ, π / 2) = L (0, π / 2) := by
    have hcont : Continuous fun θ : ℝ => L (θ, π / 2) := by
      first
        | exact L.continuous.comp (Continuous.prodMk_left (π / 2))
        | fun_prop
    have key : (⟨fun θ : ℝ => L (θ, π / 2), hcont⟩ : C(ℝ, ℂ)) =
        (⟨fun _ : ℝ => L (0, π / 2), continuous_const⟩ : C(ℝ, ℂ)) :=
      eq_of_exp_comp_eq _ _ (0 : ℝ) rfl
        (fun θ => (hexp (θ, π / 2)).trans ((hpole θ).trans (hexp (0, π / 2)).symm))
    intro θ
    exact DFunLike.congr_fun key θ
  -- Going once around: the increment `2c` must vanish.
  have e1 : L (π + π, π / 2) = L (π, -(π / 2)) + c := by
    have h := h2 π (-(π / 2))
    rwa [neg_neg] at h
  have e2 : L (π, -(π / 2)) = L (0, π / 2) + c := by
    have h := h2 0 (π / 2)
    rwa [zero_add] at h
  have e3 : L (π + π, π / 2) = L (0, π / 2) := h3 (π + π)
  have hc0 : c = 0 := by
    linear_combination (1 / 2 : ℂ) * e3 - (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * e2
  rw [hc0, Complex.exp_zero] at hc
  exact absurd hc (by norm_num)

/-! ## Spherical coordinates on the unit sphere of a real inner product space -/

section Chart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A unit vector in the plane of two orthonormal vectors. -/
theorem norm_cos_smul_add_sin_smul {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (huw : inner ℝ u w = 0) (t : ℝ) : ‖Real.cos t • u + Real.sin t • w‖ = 1 := by
  have e1 : ‖Real.cos t • u‖ = |Real.cos t| := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
  have e2 : ‖Real.sin t • w‖ = |Real.sin t| := by
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
  have e3 : inner ℝ (Real.cos t • u) (Real.sin t • w) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, huw, mul_zero, mul_zero]
  have h : ‖Real.cos t • u + Real.sin t • w‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, e1, e2, e3, mul_zero, add_zero, sq_abs, sq_abs]
    exact Real.cos_sq_add_sin_sq t
  rw [← Real.sqrt_sq (norm_nonneg (Real.cos t • u + Real.sin t • w)), h, Real.sqrt_one]

/-- Spherical coordinates built on three vectors: longitude `θ`, latitude `t`. -/
def chartVec (e₀ e₁ e₂ : E) (θ t : ℝ) : E :=
  Real.cos t • (Real.cos θ • e₀ + Real.sin θ • e₁) + Real.sin t • e₂

theorem norm_chartVec {e₀ e₁ e₂ : E} (h₀ : ‖e₀‖ = 1) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₀₁ : inner ℝ e₀ e₁ = 0) (h₀₂ : inner ℝ e₀ e₂ = 0) (h₁₂ : inner ℝ e₁ e₂ = 0)
    (θ t : ℝ) : ‖chartVec e₀ e₁ e₂ θ t‖ = 1 := by
  have hu : ‖Real.cos θ • e₀ + Real.sin θ • e₁‖ = 1 :=
    norm_cos_smul_add_sin_smul h₀ h₁ h₀₁ θ
  have huw : inner ℝ (Real.cos θ • e₀ + Real.sin θ • e₁) e₂ = 0 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h₀₂, h₁₂, mul_zero,
      mul_zero, add_zero]
  exact norm_cos_smul_add_sin_smul hu h₂ huw t

/-- The chart intertwines `(θ, t) ↦ (θ + π, -t)` with the antipodal map. -/
theorem chartVec_add_pi_neg (e₀ e₁ e₂ : E) (θ t : ℝ) :
    chartVec e₀ e₁ e₂ (θ + π) (-t) = -chartVec e₀ e₁ e₂ θ t := by
  unfold chartVec
  rw [Real.cos_neg, Real.sin_neg, Real.cos_add_pi, Real.sin_add_pi]
  first
    | module
    | (simp only [neg_smul, smul_neg, smul_add, neg_add] <;> abel)

/-- The whole line `t = π / 2` is sent to the pole `e₂`. -/
theorem chartVec_pi_div_two (e₀ e₁ e₂ : E) (θ : ℝ) :
    chartVec e₀ e₁ e₂ θ (π / 2) = e₂ := by
  unfold chartVec
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add]

theorem continuous_chartVec (e₀ e₁ e₂ : E) :
    Continuous fun a : ℝ × ℝ => chartVec e₀ e₁ e₂ a.1 a.2 := by
  have h1 : Continuous fun a : ℝ × ℝ => Real.cos a.1 := Real.continuous_cos.comp continuous_fst
  have h2 : Continuous fun a : ℝ × ℝ => Real.sin a.1 := Real.continuous_sin.comp continuous_fst
  have h3 : Continuous fun a : ℝ × ℝ => Real.cos a.2 := Real.continuous_cos.comp continuous_snd
  have h4 : Continuous fun a : ℝ × ℝ => Real.sin a.2 := Real.continuous_sin.comp continuous_snd
  show Continuous fun a : ℝ × ℝ =>
    Real.cos a.2 • (Real.cos a.1 • e₀ + Real.sin a.1 • e₁) + Real.sin a.2 • e₂
  exact (h3.smul ((h1.smul continuous_const).add (h2.smul continuous_const))).add
    (h4.smul continuous_const)

/-- A continuous odd complex function on the unit sphere of a real inner product
space containing three orthonormal vectors has a zero. -/
theorem exists_zero_of_odd_sphere {e₀ e₁ e₂ : E} (h₀ : ‖e₀‖ = 1) (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₀₁ : inner ℝ e₀ e₁ = 0) (h₀₂ : inner ℝ e₀ e₂ = 0)
    (h₁₂ : inner ℝ e₁ e₂ = 0) (g : sphere (0 : E) 1 → ℂ) (hg : Continuous g)
    (hodd : ∀ x, g (-x) = -g x) : ∃ x, g x = 0 := by
  have hmem : ∀ a : ℝ × ℝ, chartVec e₀ e₁ e₂ a.1 a.2 ∈ sphere (0 : E) 1 := fun a =>
    mem_sphere_zero_iff_norm.mpr (norm_chartVec h₀ h₁ h₂ h₀₁ h₀₂ h₁₂ a.1 a.2)
  let ψ : ℝ × ℝ → sphere (0 : E) 1 := fun a => ⟨chartVec e₀ e₁ e₂ a.1 a.2, hmem a⟩
  have hψ : Continuous ψ := Continuous.subtype_mk (continuous_chartVec e₀ e₁ e₂) hmem
  have hanti : ∀ θ t : ℝ, ψ (θ + π, -t) = -ψ (θ, t) := by
    intro θ t
    apply Subtype.ext
    show chartVec e₀ e₁ e₂ (θ + π) (-t) = -chartVec e₀ e₁ e₂ θ t
    exact chartVec_add_pi_neg e₀ e₁ e₂ θ t
  have hpole : ∀ θ : ℝ, ψ (θ, π / 2) = ψ (0, π / 2) := by
    intro θ
    apply Subtype.ext
    show chartVec e₀ e₁ e₂ θ (π / 2) = chartVec e₀ e₁ e₂ 0 (π / 2)
    rw [chartVec_pi_div_two, chartVec_pi_div_two]
  obtain ⟨a, ha⟩ := exists_zero_of_antiperiodic (fun a => g (ψ a)) (hg.comp hψ)
    (fun θ t => (congrArg g (hanti θ t)).trans (hodd (ψ (θ, t))))
    (fun θ => congrArg g (hpole θ))
  exact ⟨ψ a, ha⟩

end Chart

/-! ## Theorem 1.1 in dimension two -/

/-- The antipodal difference of a map into the plane, read as a complex number. -/
def antipodalDiff (f : Sphere 2 → Coordinates 2) (x : Sphere 2) : ℂ :=
  ⟨f x 0 - f (-x) 0, f x 1 - f (-x) 1⟩

theorem antipodalDiff_neg (f : Sphere 2 → Coordinates 2) (x : Sphere 2) :
    antipodalDiff f (-x) = -antipodalDiff f x := by
  apply Complex.ext
  · show f (-x) 0 - f (-(-x)) 0 = -(f x 0 - f (-x) 0)
    rw [neg_neg]
    ring
  · show f (-x) 1 - f (-(-x)) 1 = -(f x 1 - f (-x) 1)
    rw [neg_neg]
    ring

theorem continuous_antipodalDiff {f : Sphere 2 → Coordinates 2} (hf : Continuous f) :
    Continuous (antipodalDiff f) := by
  have c0 : Continuous fun x : Sphere 2 => f x 0 := (continuous_apply (0 : Fin 2)).comp hf
  have c1 : Continuous fun x : Sphere 2 => f x 1 := (continuous_apply (1 : Fin 2)).comp hf
  have d0 : Continuous fun x : Sphere 2 => f x 0 - f (-x) 0 := c0.sub (c0.comp continuous_neg)
  have d1 : Continuous fun x : Sphere 2 => f x 1 - f (-x) 1 := c1.sub (c1.comp continuous_neg)
  have h : Continuous fun x : Sphere 2 =>
      ((f x 0 - f (-x) 0 : ℝ) : ℂ) + ((f x 1 - f (-x) 1 : ℝ) : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp d0).add
      ((Complex.continuous_ofReal.comp d1).mul continuous_const)
  have e : antipodalDiff f = fun x : Sphere 2 =>
      ((f x 0 - f (-x) 0 : ℝ) : ℂ) + ((f x 1 - f (-x) 1 : ℝ) : ℂ) * Complex.I :=
    funext fun x => Complex.mk_eq_add_mul_I _ _
  rw [e]
  exact h

/-- **Theorem 1.1 for `n = 2`** (Borsuk–Ulam for `S² → ℝ²`), proved from Mathlib alone. -/
theorem borsukUlam_two : BorsukUlam 2 := by
  intro f hf
  have hb := (EuclideanSpace.basisFun (Fin (2 + 1)) ℝ).orthonormal
  obtain ⟨x, hx⟩ := exists_zero_of_odd_sphere (hb.1 0) (hb.1 1) (hb.1 2)
    (hb.2 (show (0 : Fin (2 + 1)) ≠ 1 by decide))
    (hb.2 (show (0 : Fin (2 + 1)) ≠ 2 by decide))
    (hb.2 (show (1 : Fin (2 + 1)) ≠ 2 by decide))
    (antipodalDiff f) (continuous_antipodalDiff hf) (antipodalDiff_neg f)
  have h0 : f x 0 - f (-x) 0 = 0 := congrArg Complex.re hx
  have h1 : f x 1 - f (-x) 1 = 0 := congrArg Complex.im hx
  exact ⟨x, funext (Fin.forall_fin_two.mpr ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩)⟩

/-! ## The dimension-two results of the article, without the external dependency -/

theorem thm_5_4_dim2 (α : Sphere 2 → Coordinates 2) (hα : Continuous α) :
    ∃ p, α p = α (-p) := thm_5_4 borsukUlam_two α hα

theorem thm_5_5_dim2 (H : Sphere 2 → Coordinates 2) (hH : Continuous H) :
    ∃ p, H p = H (-p) := thm_5_5 borsukUlam_two H hH

/-- Conditional on continuity of the specified kernel, as in `thm_5_6_continuous_kernel`.
No claim is made about existence of a physical propagator. -/
theorem thm_5_6_continuous_kernel_dim2
    (K : Sphere 2 → Sphere 2 → Coordinates 2) (b : Sphere 2)
    (hK : Continuous (K b)) : ∃ a : Sphere 2,
      K b a = K b (-a) ∧ Nonempty (Path a b) ∧ Nonempty (Path b (-a)) :=
  thm_5_6_continuous_kernel borsukUlam_two K b hK

theorem thm_6_2_dim2 (Φ : Sphere 2 → Coordinates 2) (hΦ : Continuous Φ) :
    ∃ p, Φ p = Φ (-p) := thm_6_2 borsukUlam_two Φ hΦ

theorem cor_6_3_dim2 (Φ : Sphere 2 → Coordinates 2) (hΦ : Continuous Φ) :
    ∃ p : Sphere 2, Φ p = Φ (-p) ∧
      ∃ d : DiscreteArc p (-p), ∃ k : DiscreteArc (Φ p) (Φ p),
        ∀ t : unitInterval, k.path t = Φ (d.path t) :=
  cor_6_3 borsukUlam_two Φ hΦ

end
end Peters2024

#print axioms Peters2024.eq_of_exp_comp_eq
#print axioms Peters2024.exists_zero_of_antiperiodic
#print axioms Peters2024.exists_zero_of_odd_sphere
#print axioms Peters2024.borsukUlam_two
#print axioms Peters2024.thm_5_4_dim2
#print axioms Peters2024.thm_5_5_dim2
#print axioms Peters2024.thm_5_6_continuous_kernel_dim2
#print axioms Peters2024.thm_6_2_dim2
#print axioms Peters2024.cor_6_3_dim2
