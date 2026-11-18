import Mathlib

/-! Rank-nullity lower bound for approximation numbers. Applies to the actual
continuous inverse on spectral subspaces in M16 v16.6 §13, independently of
the approximation envelope ideal transfer in #405. -/
namespace Manuscript16.V166RankMinmax

variable {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup J] [NormedSpace ℂ J]

/-- A rank-n factor cannot be injective on an (n+1)-dimensional subspace. -/
theorem finite_factor_has_kernel (n : ℕ)
    (V : (Fin (n+1) → ℂ) →L[ℂ] H) (hV : Function.Injective V)
    (F : H →L[ℂ] (Fin n → ℂ)) :
    ∃ x : Fin (n+1) → ℂ, V x ≠ 0 ∧ F (V x) = 0 := by
  have hni : ¬ Function.Injective (F.comp V) := by
    intro hi
    have hd := LinearMap.finrank_le_finrank_of_injective
      (f := (F.comp V).toLinearMap) hi
    simp [Module.finrank_pi_fintype] at hd
  obtain ⟨a,b,hab,hne⟩ := Function.not_injective_iff.mp hni
  refine ⟨a-b, ?_, ?_⟩
  · intro hz
    have hz' : V (a-b) = V 0 := by simpa using hz
    exact hne (sub_eq_zero.mp (hV hz'))
  · rw [map_sub, map_sub, sub_eq_zero]
    exact hab

/-- True operator-norm lower bound for every rank-n factorization.
The only spectral input is a lower norm estimate on the given (n+1)-space. -/
theorem rank_error_lower (T : H →L[ℂ] J) (n : ℕ)
    (V : (Fin (n+1) → ℂ) →L[ℂ] H) (hV : Function.Injective V)
    (s : ℝ) (hLower : ∀ x, s * ‖V x‖ ≤ ‖T (V x)‖)
    (F : H →L[ℂ] (Fin n → ℂ)) (G : (Fin n → ℂ) →L[ℂ] J) :
    s ≤ ‖T - G.comp F‖ := by
  obtain ⟨x,hx,hFx⟩ := finite_factor_has_kernel n V hV F
  have hv : 0 < ‖V x‖ := norm_pos_iff.mpr hx
  have hval : (T - G.comp F) (V x) = T (V x) := by
    simp [hFx]
  have hnorm := (T - G.comp F).le_opNorm (V x)
  rw [hval] at hnorm
  exact le_of_mul_le_mul_right ((hLower x).trans hnorm) hv

/-- If a spectral rank-n truncation attains the corresponding lower bound,
its operator norm error is the exact best rank-n approximation error. -/
theorem rank_error_optimal (T : H →L[ℂ] J) (n : ℕ)
    (V : (Fin (n+1) → ℂ) →L[ℂ] H) (hV : Function.Injective V)
    (s : ℝ) (hLower : ∀ x, s * ‖V x‖ ≤ ‖T (V x)‖)
    (F₀ : H →L[ℂ] (Fin n → ℂ)) (G₀ : (Fin n → ℂ) →L[ℂ] J)
    (hUpper : ‖T - G₀.comp F₀‖ ≤ s) :
    ‖T - G₀.comp F₀‖ = s ∧
      ∀ (F : H →L[ℂ] (Fin n → ℂ)) (G : (Fin n → ℂ) →L[ℂ] J),
        ‖T - G₀.comp F₀‖ ≤ ‖T - G.comp F‖ := by
  have heq := le_antisymm hUpper (rank_error_lower T n V hV s hLower F₀ G₀)
  refine ⟨heq, ?_⟩
  intro F G
  rw [heq]
  exact rank_error_lower T n V hV s hLower F G

#print axioms finite_factor_has_kernel
#print axioms rank_error_lower
#print axioms rank_error_optimal
end Manuscript16.V166RankMinmax
