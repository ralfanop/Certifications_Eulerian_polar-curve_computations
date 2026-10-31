import Bridge.Ladder2

/-!
# Proposition 3.8 (continued): integration by parts and the recursion for `J_{nm}`
-/

open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped ComplexConjugate Nat

namespace EulerianBridge.Ladder

open EulerianGrothendieck.Fock

/-! ## Exponentially bounded continuous functions -/

/-- Continuous and bounded by `C e^{K|z|}`. -/
def ExpBdd (f : ℂ → ℂ) : Prop := Continuous f ∧ ∃ C K : ℝ, ∀ z, ‖f z‖ ≤ C * Real.exp (K * ‖z‖)

theorem ExpBdd.mul {f g : ℂ → ℂ} (hf : ExpBdd f) (hg : ExpBdd g) : ExpBdd (fun z => f z * g z) := by
  obtain ⟨hfc, C1, K1, h1⟩ := hf
  obtain ⟨hgc, C2, K2, h2⟩ := hg
  refine ⟨hfc.mul hgc, C1 * C2, K1 + K2, fun z => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  have hC1 : 0 ≤ C1 * Real.exp (K1 * ‖z‖) := (norm_nonneg _).trans (h1 z)
  calc ‖f z‖ * ‖g z‖ ≤ (C1 * Real.exp (K1 * ‖z‖)) * (C2 * Real.exp (K2 * ‖z‖)) :=
        mul_le_mul (h1 z) (h2 z) (norm_nonneg _) hC1
    _ = C1 * C2 * (Real.exp (K1 * ‖z‖) * Real.exp (K2 * ‖z‖)) := by ring

theorem exp_le_exp_abs (K r : ℝ) (hr : 0 ≤ r) : Real.exp (K * r) ≤ Real.exp (|K| * r) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self K) hr)

theorem ExpBdd.add {f g : ℂ → ℂ} (hf : ExpBdd f) (hg : ExpBdd g) : ExpBdd (fun z => f z + g z) := by
  obtain ⟨hfc, C1, K1, h1⟩ := hf
  obtain ⟨hgc, C2, K2, h2⟩ := hg
  refine ⟨hfc.add hgc, |C1| + |C2|, |K1| + |K2|, fun z => ?_⟩
  have e1 : Real.exp (K1 * ‖z‖) ≤ Real.exp ((|K1| + |K2|) * ‖z‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K1, abs_nonneg K2]) (norm_nonneg _))
  have e2 : Real.exp (K2 * ‖z‖) ≤ Real.exp ((|K1| + |K2|) * ‖z‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K2, abs_nonneg K1]) (norm_nonneg _))
  have b1 : C1 * Real.exp (K1 * ‖z‖) ≤ |C1| * Real.exp ((|K1| + |K2|) * ‖z‖) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
  have b2 : C2 * Real.exp (K2 * ‖z‖) ≤ |C2| * Real.exp ((|K1| + |K2|) * ‖z‖) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ |C1| * Real.exp ((|K1| + |K2|) * ‖z‖) + |C2| * Real.exp ((|K1| + |K2|) * ‖z‖) :=
        add_le_add ((h1 z).trans b1) ((h2 z).trans b2)
    _ = (|C1| + |C2|) * Real.exp ((|K1| + |K2|) * ‖z‖) := by ring

theorem ExpBdd.const (c : ℂ) : ExpBdd (fun _ => c) :=
  ⟨continuous_const, ‖c‖, 0, fun z => by simp⟩

theorem ExpBdd.id : ExpBdd (fun z => z) :=
  ⟨continuous_id, 1, 1, fun z => by
    rw [one_mul, one_mul]; linarith [Real.add_one_le_exp ‖z‖]⟩

theorem ExpBdd.conj {f : ℂ → ℂ} (hf : ExpBdd f) : ExpBdd (fun z => conj (f z)) := by
  obtain ⟨hfc, C, K, h⟩ := hf
  exact ⟨Complex.continuous_conj.comp hfc, C, K, fun z => by rw [Complex.norm_conj]; exact h z⟩

theorem ExpBdd.pow {f : ℂ → ℂ} (hf : ExpBdd f) (n : ℕ) : ExpBdd (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using ExpBdd.const 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem ExpBdd.cexp_lin (c : ℂ) : ExpBdd (fun z => cexp (c * z)) := by
  refine ⟨by fun_prop, 1, ‖c‖, fun z => ?_⟩
  rw [one_mul, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc (c * z).re ≤ ‖c * z‖ := Complex.re_le_norm _
    _ = ‖c‖ * ‖z‖ := norm_mul _ _

theorem expBdd_phi (α : ℝ) (n : ℕ) (t : ℝ) : ExpBdd (phi α n t) := by
  unfold Ladder.phi
  refine ((((ExpBdd.const (α:ℂ)).mul ExpBdd.id.conj).add (ExpBdd.const (-(I * t)))).pow n |>.mul
    (ExpBdd.cexp_lin (I * t))) |> fun h => ?_
  refine ⟨?_, ?_⟩
  · unfold Ladder.phi at *; exact (by fun_prop)
  · obtain ⟨_, C, K, hb⟩ := h
    exact ⟨C, K, fun z => by
      have := hb z; simpa [sub_eq_add_neg] using this⟩

theorem expBdd_P (α : ℝ) (t : ℝ) : ExpBdd (fun z => (α:ℂ) * conj z - I * t) := by
  obtain ⟨_, C, K, hb⟩ := ((ExpBdd.const (α:ℂ)).mul ExpBdd.id.conj).add (ExpBdd.const (-(I * t)))
  refine ⟨by fun_prop, C, K, fun z => ?_⟩
  have := hb z
  simpa [sub_eq_add_neg] using this

theorem Dphi_apply_eq (α : ℝ) (n : ℕ) (t : ℝ) (z v : ℂ) :
    Dphi α n t z v = (((α:ℂ) * conj z - I * t) ^ n * ((I * t) * cexp (I * t * z))) * v +
      (cexp (I * t * z) * (((n:ℂ) * ((α:ℂ) * conj z - I * t) ^ (n - 1)) * (α:ℂ))) * conj v := by
  rw [Dphi_eq, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]

theorem continuous_Dphi_z (α : ℝ) (n : ℕ) (t : ℝ) (v : ℂ) : Continuous (fun z : ℂ => Dphi α n t z v) := by
  have h := (continuous_Dphi_apply α n v).comp (continuous_id.prodMk (continuous_const (y := t)))
  exact h

theorem norm_Dphi_bound (α : ℝ) (n : ℕ) (t : ℝ) (v : ℂ) :
    ∃ C K : ℝ, ∀ z, ‖Dphi α n t z v‖ ≤ C * Real.exp (K * ‖z‖) := by
  have hA := (((expBdd_P α t).pow n).mul ((ExpBdd.const (I * t)).mul (ExpBdd.cexp_lin (I * t)))).mul
    (ExpBdd.const v)
  have hB := ((ExpBdd.cexp_lin (I * t)).mul (((ExpBdd.const (n:ℂ)).mul ((expBdd_P α t).pow (n - 1))).mul
    (ExpBdd.const (α:ℂ)))).mul ((ExpBdd.const v).conj)
  obtain ⟨_, C, K, hb⟩ := hA.add hB
  refine ⟨C, K, fun z => ?_⟩
  rw [Dphi_apply_eq]
  exact hb z

theorem expBdd_Dphi (α : ℝ) (n : ℕ) (t : ℝ) (v : ℂ) : ExpBdd (fun z => Dphi α n t z v) :=
  ⟨continuous_Dphi_z α n t v, norm_Dphi_bound α n t v⟩

theorem ExpBdd.integrable {α : ℝ} (hα : 0 < α) {f : ℂ → ℂ} (hf : ExpBdd f) :
    Integrable (fun z => f z * (fockDensity α z : ℂ)) := by
  obtain ⟨hc, C, K, hb⟩ := hf
  exact integrable_of_exp_bound hα hc C K hb

end EulerianBridge.Ladder
