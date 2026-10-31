import Bridge.Saddle.Coeffs

/-!
# Lemma 5.5, part 13: `w_M`, `w_M'`, `w_M''` at `y = Mx` through the integrals `I_r`

With `s = s(x)` (so that `Λ'(s) = x`), `P = A(s)^M e^{-sMx}` and `ε` with `Mε² = 1`
(eqs. (70) and the rescaling `u = εz`):
* `w_M(Mx)   = (2π)⁻¹ P (ε I₀)`,
* `w_M'(Mx)  = (2π)⁻¹ P (-s ε I₀ - ε² I₁)`,
* `w_M''(Mx) = (2π)⁻¹ P (s² ε I₀ + 2s ε² I₁ + ε³ I₂)`.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-- `J_r = ∫ (iu)^r χ(s,u)^M du`. -/
noncomputable def Jr (s : ℝ) (M r : ℕ) : ℂ := ∫ u : ℝ, ((u:ℂ) * I) ^ r * χ s u ^ M

theorem integrable_Jr_integrand {M r : ℕ} (hM : r + 2 ≤ M) (s : ℝ) :
    Integrable (fun u : ℝ => ((u:ℂ) * I) ^ r * χ s u ^ M) := by
  refine (integrable_inv_one_add_sq.const_mul (2 ^ r * 8 * Real.exp (|s| / 2) ^ M)).mono'
    ((by have := continuous_χ s; fun_prop : Continuous fun u : ℝ => ((u:ℂ) * I) ^ r * χ s u ^ M).aestronglyMeasurable)
    (Eventually.of_forall (fun u => ?_))
  set w : ℂ := (s:ℂ) + u * I
  rw [norm_mul, norm_pow, norm_uI, norm_pow]
  have h1 : |u| ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w; simpa [w] using this
  have h2 := norm_pow_A_le hM w
  have hre : w.re = s := by simp [w]
  have him : w.im = u := by simp [w]
  rw [hre, him] at h2
  calc |u| ^ r * ‖χ s u‖ ^ M ≤ ‖w‖ ^ r * ‖A w‖ ^ M :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 r)
          (pow_le_pow_left₀ (norm_nonneg _) (norm_χ_le_A s u) M) (by positivity) (by positivity)
    _ ≤ _ := h2

/-- `J_r = ε^{r+1} I_r`. -/
theorem Jr_eq (s : ℝ) (M r : ℕ) {e : ℝ} (he0 : 0 < e) : Jr s M r = (e:ℂ) ^ (r + 1) * Ir s M e r := by
  have h := Measure.integral_comp_mul_left (fun u : ℝ => ((u:ℂ) * I) ^ r * χ s u ^ M) e
  simp only at h
  rw [abs_inv, abs_of_pos he0] at h
  have hfun : (fun z : ℝ => (((e * z : ℝ) : ℂ) * I) ^ r * χ s (e * z) ^ M) =
      fun z : ℝ => (e:ℂ) ^ r * (((z:ℂ) * I) ^ r * χ s (e * z) ^ M) := by
    funext z; push_cast; ring
  rw [hfun, MeasureTheory.integral_const_mul] at h
  unfold Jr Ir
  have he' : (e:ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  rw [Complex.real_smul] at h
  have : ∫ u : ℝ, ((u:ℂ) * I) ^ r * χ s u ^ M = (e:ℂ) * ((e:ℂ) ^ r * ∫ z : ℝ, ((z:ℂ) * I) ^ r * χ s (e * z) ^ M) := by
    rw [h]; push_cast; rw [← mul_assoc, mul_inv_cancel₀ he', one_mul]
  rw [this]; ring

/-- `A(s+iu)^M e^{-(s+iu)Mx} = A(s)^M e^{-sMx} χ(s,u)^M` when `Λ'(s) = x`. -/
theorem factor_tilt (s x u : ℝ) (hx : κ 1 s = x) (M : ℕ) :
    A ((s:ℂ) + u * I) ^ M * cexp (-((s:ℂ) + u * I) * ((M * x : ℝ) : ℂ)) =
      ((Ar s ^ M * Real.exp (-(s * M * x)) : ℝ) : ℂ) * χ s u ^ M := by
  have hAr : ((Ar s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Ar_pos s).ne'
  unfold χ
  rw [κc_ofReal, hx, A_ofReal, mul_pow, div_pow, ← Complex.exp_nat_mul]
  push_cast
  rw [show cexp (-((s:ℂ) + u * I) * ((M:ℂ) * x)) =
    cexp (-((s:ℂ) * M * x)) * cexp ((M:ℂ) * (-((u:ℂ) * I) * x)) by rw [← Complex.exp_add]; ring_nf]
  field_simp

theorem Wint_eq (M r : ℕ) (hM : r + 2 ≤ M) (s x : ℝ) (hx : κ 1 s = x) :
    Wint M r s (M * x) = ((Ar s ^ M * Real.exp (-(s * M * x)) : ℝ) : ℂ) *
      ∫ u : ℝ, (-((s:ℂ) + u * I)) ^ r * χ s u ^ M := by
  unfold Wint Wf
  rw [← MeasureTheory.integral_const_mul]
  congr 1; funext u
  have := factor_tilt s x u hx M
  push_cast at this ⊢
  rw [show A ((s:ℂ) + u * I) ^ M * (-((s:ℂ) + u * I)) ^ r * cexp (-((s:ℂ) + u * I) * ((M:ℂ) * x)) =
    (-((s:ℂ) + u * I)) ^ r * (A ((s:ℂ) + u * I) ^ M * cexp (-((s:ℂ) + u * I) * ((M:ℂ) * x))) by ring,
    this]
  ring

theorem moment_split0 (s : ℝ) (M : ℕ) :
    ∫ u : ℝ, (-((s:ℂ) + u * I)) ^ 0 * χ s u ^ M = Jr s M 0 := by
  unfold Jr; simp

theorem moment_split1 (s : ℝ) {M : ℕ} (hM : 3 ≤ M) :
    ∫ u : ℝ, (-((s:ℂ) + u * I)) ^ 1 * χ s u ^ M = -(s:ℂ) * Jr s M 0 - Jr s M 1 := by
  have h0 := integrable_Jr_integrand (r := 0) (M := M) (by omega) s
  have h1 := integrable_Jr_integrand (r := 1) (M := M) (by omega) s
  have hfun : (fun u : ℝ => (-((s:ℂ) + u * I)) ^ 1 * χ s u ^ M) =
      fun u : ℝ => -(s:ℂ) * (((u:ℂ) * I) ^ 0 * χ s u ^ M) - ((u:ℂ) * I) ^ 1 * χ s u ^ M := by
    funext u; ring
  rw [hfun, integral_sub (h0.const_mul _) h1, MeasureTheory.integral_const_mul]
  rfl

theorem moment_split2 (s : ℝ) {M : ℕ} (hM : 4 ≤ M) :
    ∫ u : ℝ, (-((s:ℂ) + u * I)) ^ 2 * χ s u ^ M =
      (s:ℂ) ^ 2 * Jr s M 0 + 2 * (s:ℂ) * Jr s M 1 + Jr s M 2 := by
  have h0 := integrable_Jr_integrand (r := 0) (M := M) (by omega) s
  have h1 := integrable_Jr_integrand (r := 1) (M := M) (by omega) s
  have h2 := integrable_Jr_integrand (r := 2) (M := M) (by omega) s
  have hfun : (fun u : ℝ => (-((s:ℂ) + u * I)) ^ 2 * χ s u ^ M) =
      fun u : ℝ => ((s:ℂ) ^ 2 * (((u:ℂ) * I) ^ 0 * χ s u ^ M) + 2 * (s:ℂ) * (((u:ℂ) * I) ^ 1 * χ s u ^ M)) +
        ((u:ℂ) * I) ^ 2 * χ s u ^ M := by
    funext u; ring
  rw [hfun, integral_add (f := fun u : ℝ => (s:ℂ) ^ 2 * (((u:ℂ) * I) ^ 0 * χ s u ^ M) +
      2 * (s:ℂ) * (((u:ℂ) * I) ^ 1 * χ s u ^ M)) (g := fun u : ℝ => ((u:ℂ) * I) ^ 2 * χ s u ^ M)
      ((h0.const_mul _).add (h1.const_mul _)) h2,
    integral_add (f := fun u : ℝ => (s:ℂ) ^ 2 * (((u:ℂ) * I) ^ 0 * χ s u ^ M))
      (g := fun u : ℝ => 2 * (s:ℂ) * (((u:ℂ) * I) ^ 1 * χ s u ^ M)) (h0.const_mul _) (h1.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rfl

/-- The three representations at `y = Mx`, `s = s(x)`. -/
theorem w_repr {M : ℕ} (hM : 4 ≤ M) {s x e : ℝ} (hx : κ 1 s = x) (he0 : 0 < e) :
    ((w M (M * x) : ℝ) : ℂ) = (2 * Real.pi : ℂ)⁻¹ * ((Ar s ^ M * Real.exp (-(s * M * x)) : ℝ) : ℂ) *
        ((e:ℂ) * Ir s M e 0) ∧
    ((deriv (w M) (M * x) : ℝ) : ℂ) = (2 * Real.pi : ℂ)⁻¹ * ((Ar s ^ M * Real.exp (-(s * M * x)) : ℝ) : ℂ) *
        (-(s:ℂ) * ((e:ℂ) * Ir s M e 0) - (e:ℂ) ^ 2 * Ir s M e 1) ∧
    ((deriv (deriv (w M)) (M * x) : ℝ) : ℂ) = (2 * Real.pi : ℂ)⁻¹ *
        ((Ar s ^ M * Real.exp (-(s * M * x)) : ℝ) : ℂ) *
        ((s:ℂ) ^ 2 * ((e:ℂ) * Ir s M e 0) + 2 * (s:ℂ) * ((e:ℂ) ^ 2 * Ir s M e 1) +
          (e:ℂ) ^ 3 * Ir s M e 2) := by
  have hJ0 := Jr_eq s M 0 he0
  have hJ1 := Jr_eq s M 1 he0
  have hJ2 := Jr_eq s M 2 he0
  simp only [zero_add, pow_one] at hJ0 hJ1 hJ2
  refine ⟨?_, ?_, ?_⟩
  · rw [w_eq_Wint M (by omega) s, Wint_eq M 0 (by omega) s x hx, moment_split0, hJ0]; ring
  · rw [deriv_w_ofReal M (by omega) s, Wint_eq M 1 (by omega) s x hx, moment_split1 s (by omega),
      hJ0, hJ1]; ring
  · rw [deriv2_w_ofReal M hM s, Wint_eq M 2 (by omega) s x hx, moment_split2 s hM, hJ0, hJ1, hJ2]
    ring

end EulerianBridge.Saddle
