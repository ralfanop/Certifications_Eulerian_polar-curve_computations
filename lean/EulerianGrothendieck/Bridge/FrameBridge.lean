import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Proposition 3.7: exact finite-frame factorisation of the Eulerian state

Manuscript V173, Proposition 3.7, eqs. (34)–(36).

Cited inputs, as hypotheses: Hall's transform `𝒱_ħ` is an isometry (`𝒱†𝒱 = I`, Hall, Thm. 14.18) and
Vourdas's `M_V(ζ)` is semi-unitary (`M M† = I_d`, Vourdas, Lemma 4.1). The step-function map
`U_d` is an isometry with `U_d c_d = ψ₁` (proved separately for the concrete `U_d`; here a hypothesis
of the abstract algebra). Then for `B = 𝒱 U_d M`:
`B†B = M†M`, `BB† = 𝒱 U_d U_d† 𝒱†`, `B M† c_d = 𝒱 ψ₁`, and both `B†B`, `BB†` are idempotent and
self-adjoint (orthogonal projections).
-/

open ContinuousLinearMap

namespace EulerianBridge.FrameBridge

variable {Cd C2d L2 F : Type*}
  [NormedAddCommGroup Cd] [InnerProductSpace ℂ Cd] [CompleteSpace Cd]
  [NormedAddCommGroup C2d] [InnerProductSpace ℂ C2d] [CompleteSpace C2d]
  [NormedAddCommGroup L2] [InnerProductSpace ℂ L2] [CompleteSpace L2]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (V : L2 →L[ℂ] F) (U : Cd →L[ℂ] L2) (M : C2d →L[ℂ] Cd)

/-- `B_{d,ħ,ζ} := 𝒱_ħ U_d M_V(ζ)` (eq. (34)). -/
def B : C2d →L[ℂ] F := V ∘L U ∘L M

theorem B_adj_B (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ L2) (hU : adjoint U ∘L U = ContinuousLinearMap.id ℂ Cd) :
    adjoint (B V U M) ∘L B V U M = adjoint M ∘L M := by
  unfold B
  simp only [adjoint_comp]
  calc adjoint M ∘L adjoint U ∘L adjoint V ∘L (V ∘L U ∘L M)
      = adjoint M ∘L (adjoint U ∘L ((adjoint V ∘L V) ∘L U)) ∘L M := by
        simp only [comp_assoc]
    _ = adjoint M ∘L M := by rw [hV, ContinuousLinearMap.id_comp, hU, ContinuousLinearMap.id_comp]

theorem B_B_adj (hM : M ∘L adjoint M = ContinuousLinearMap.id ℂ Cd) :
    B V U M ∘L adjoint (B V U M) = V ∘L U ∘L adjoint U ∘L adjoint V := by
  unfold B
  simp only [adjoint_comp]
  calc V ∘L U ∘L M ∘L (adjoint M ∘L adjoint U ∘L adjoint V)
      = V ∘L U ∘L (M ∘L adjoint M) ∘L adjoint U ∘L adjoint V := by simp only [comp_assoc]
    _ = V ∘L U ∘L adjoint U ∘L adjoint V := by rw [hM, ContinuousLinearMap.id_comp]

/-- Eq. (36): `B M† c_d = 𝒱 ψ₁` when `U c_d = ψ₁`. -/
theorem B_reconstruction (hM : M ∘L adjoint M = ContinuousLinearMap.id ℂ Cd) (c : Cd) (ψ : L2) (hc : U c = ψ) :
    B V U M (adjoint M c) = V ψ := by
  unfold B
  have : M (adjoint M c) = c := by
    have := congrArg (fun T : Cd →L[ℂ] Cd => T c) hM
    simpa using this
  simp [this, hc]

/-- `B†B` is an orthogonal projection (self-adjoint idempotent) when `M M† = I`. -/
theorem B_adj_B_proj (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ L2) (hU : adjoint U ∘L U = ContinuousLinearMap.id ℂ Cd)
    (hM : M ∘L adjoint M = ContinuousLinearMap.id ℂ Cd) :
    IsIdempotentElem (adjoint (B V U M) ∘L B V U M) ∧
      IsSelfAdjoint (adjoint (B V U M) ∘L B V U M) := by
  rw [B_adj_B V U M hV hU]
  refine ⟨?_, ?_⟩
  · show (adjoint M ∘L M) * (adjoint M ∘L M) = adjoint M ∘L M
    change adjoint M ∘L M ∘L adjoint M ∘L M = adjoint M ∘L M
    calc adjoint M ∘L M ∘L adjoint M ∘L M = adjoint M ∘L (M ∘L adjoint M) ∘L M := by
          simp only [comp_assoc]
      _ = adjoint M ∘L M := by rw [hM, ContinuousLinearMap.id_comp]
  · rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_comp, adjoint_adjoint]

/-- `BB†` is an orthogonal projection when `𝒱†𝒱 = I` and `U†U = I`. -/
theorem B_B_adj_proj (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ L2) (hU : adjoint U ∘L U = ContinuousLinearMap.id ℂ Cd)
    (hM : M ∘L adjoint M = ContinuousLinearMap.id ℂ Cd) :
    IsIdempotentElem (B V U M ∘L adjoint (B V U M)) ∧ IsSelfAdjoint (B V U M ∘L adjoint (B V U M)) := by
  rw [B_B_adj V U M hM]
  refine ⟨?_, ?_⟩
  swap
  · rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
    simp only [adjoint_comp, adjoint_adjoint, comp_assoc]
  show (V ∘L U ∘L adjoint U ∘L adjoint V) ∘L (V ∘L U ∘L adjoint U ∘L adjoint V) =
    V ∘L U ∘L adjoint U ∘L adjoint V
  calc (V ∘L U ∘L adjoint U ∘L adjoint V) ∘L (V ∘L U ∘L adjoint U ∘L adjoint V)
      = V ∘L U ∘L (adjoint U ∘L ((adjoint V ∘L V) ∘L U)) ∘L adjoint U ∘L adjoint V := by
        simp only [comp_assoc]
    _ = V ∘L U ∘L adjoint U ∘L adjoint V := by rw [hV, ContinuousLinearMap.id_comp, hU, ContinuousLinearMap.id_comp]

end EulerianBridge.FrameBridge
