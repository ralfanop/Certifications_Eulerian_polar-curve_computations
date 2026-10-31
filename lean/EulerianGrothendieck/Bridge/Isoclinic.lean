import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Subsection 9.1: equal principal angles from Vourdas's finite overlap

Manuscript V173, Proposition 9.1, eqs. (174)–(176).

Vourdas [Ann. Physics 482 (2025), Lemma 4.1, Eq. (52)] gives, for `|z₁| = |z₂| = 1`,
`M_V(z₁) M_V(z₂)† = ((1 + z₁ z̄₂)/2) I_d` for `d × 2d` matrices `M_V(z)`.
That overlap identity is the *only* input; here it is a hypothesis on an arbitrary family
`MV : ℂ → Matrix (Fin d) (Fin m) ℂ` (no other property of Vourdas's matrices is used).

With `V_θ := M_V(e^{iθ})†` and `P_θ := V_θ V_θ†` we prove:
* `V_θ† V_θ = I` (isometry);
* `V_θ† V_φ = ((1 + e^{i(θ-φ)})/2) I`, whence `(V_θ† V_φ)† (V_θ† V_φ) = cos²((θ-φ)/2) I`, i.e. all
  singular values of `V_θ† V_φ` equal `|cos((θ-φ)/2)|` (equal principal angles);
* `Tr(P_θ P_φ) = d cos²((θ-φ)/2)` (eq. (175)).
-/

open Matrix Complex
open scoped ComplexConjugate

namespace EulerianBridge.Isoclinic

variable {d m : ℕ} (MV : ℂ → Matrix (Fin d) (Fin m) ℂ)

/-- Vourdas's overlap identity, as a hypothesis on the family `MV`. -/
def VourdasOverlap : Prop :=
  ∀ z₁ z₂ : ℂ, ‖z₁‖ = 1 → ‖z₂‖ = 1 → MV z₁ * (MV z₂)ᴴ = ((1 + z₁ * conj z₂) / 2) • (1 : Matrix (Fin d) (Fin d) ℂ)

/-- `V_θ := M_V(e^{iθ})†`. -/
noncomputable def V (θ : ℝ) : Matrix (Fin m) (Fin d) ℂ := (MV (cexp (θ * I)))ᴴ

/-- `P_θ := V_θ V_θ†`. -/
noncomputable def P (θ : ℝ) : Matrix (Fin m) (Fin m) ℂ := V MV θ * (V MV θ)ᴴ

theorem norm_exp_ofReal_mul_I' (θ : ℝ) : ‖cexp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

theorem exp_mul_conj_exp (θ φ : ℝ) : cexp (θ * I) * conj (cexp (φ * I)) = cexp ((θ - φ : ℝ) * I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_ofReal]
  ring

/-- The overlap matrix `V_θ† V_φ` is the scalar `(1 + e^{i(θ-φ)})/2`. -/
theorem V_adj_mul_V (h : VourdasOverlap MV) (θ φ : ℝ) :
    (V MV θ)ᴴ * V MV φ = ((1 + cexp ((θ - φ : ℝ) * I)) / 2) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  unfold V
  rw [conjTranspose_conjTranspose, h _ _ (norm_exp_ofReal_mul_I' θ) (norm_exp_ofReal_mul_I' φ),
    exp_mul_conj_exp]

/-- `V_θ` is an isometry: `V_θ† V_θ = I`. -/
theorem V_isometry (h : VourdasOverlap MV) (θ : ℝ) :
    (V MV θ)ᴴ * V MV θ = 1 := by
  rw [V_adj_mul_V MV h θ θ, sub_self]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  norm_num

/-- `|(1 + e^{ix})/2|² = cos²(x/2)`, written as `conj c * c`. -/
theorem conj_mul_self_half (x : ℝ) :
    conj ((1 + cexp (x * I)) / 2) * ((1 + cexp (x * I)) / 2) = ((Real.cos (x / 2)) ^ 2 : ℝ) := by
  have hc : Real.cos (x / 2) ^ 2 = 1 / 2 + Real.cos x / 2 := by
    rw [Real.cos_sq (x / 2)]
    ring_nf
  rw [hc]
  have e : cexp (x * I) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [e]
  have key : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      conj ((1 + ((a:ℂ) + (b:ℂ) * I)) / 2) * ((1 + ((a:ℂ) + (b:ℂ) * I)) / 2) = ((1 / 2 + a / 2 : ℝ) : ℂ) := by
    intro a b hab
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq] <;> nlinarith [hab]
  exact key _ _ (by rw [add_comm]; exact Real.sin_sq_add_cos_sq x)

/-- Equal principal angles: `(V_θ†V_φ)† (V_θ†V_φ) = cos²((θ-φ)/2) I`. -/
theorem overlap_gram (h : VourdasOverlap MV) (θ φ : ℝ) :
    ((V MV θ)ᴴ * V MV φ)ᴴ * ((V MV θ)ᴴ * V MV φ)
      = ((Real.cos ((θ - φ) / 2) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rw [V_adj_mul_V MV h, conjTranspose_smul, conjTranspose_one, smul_mul_smul_comm, one_mul,
    ← conj_mul_self_half (θ - φ)]
  rfl

/-- Eq. (175): `Tr(P_θ P_φ) = d cos²((θ-φ)/2)`. -/
theorem trace_P_mul_P (h : VourdasOverlap MV) (θ φ : ℝ) :
    trace (P MV θ * P MV φ) = (d : ℂ) * ((Real.cos ((θ - φ) / 2) ^ 2 : ℝ) : ℂ) := by
  unfold P
  have e1 : V MV θ * (V MV θ)ᴴ * (V MV φ * (V MV φ)ᴴ)
      = V MV θ * (((V MV θ)ᴴ * V MV φ) * (V MV φ)ᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [e1, trace_mul_comm, Matrix.mul_assoc,
    show (V MV φ)ᴴ * V MV θ = ((V MV θ)ᴴ * V MV φ)ᴴ by
      rw [conjTranspose_mul, conjTranspose_conjTranspose], trace_mul_comm,
    overlap_gram MV h, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, mul_comm]

end EulerianBridge.Isoclinic
