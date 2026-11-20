import UniformLanczos.Theorem59

/-! M12 5.8: uniform interior gap for the normalized squared recurrence
coefficients from the existing proportional limit. The local Jacobi moment
argument and B-spline derivative/Legendre tail bounds remain to be proved. -/

namespace UniformLanczos.Lemma513

open Set UniformLanczos.Theorem59

theorem uniform_interior_gap (hLL : LL_13_4) {K : Set ℝ}
    (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ L : ℕ, ∀ j M : ℕ, L ≤ j →
      (j : ℝ) / M ∈ K →
      betaM M j / (M : ℝ)^2 ≤ 1 / 16 - η := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, by norm_num, 0, ?_⟩
    intro j M hj hmem
    rw [hKe] at hmem
    simp at hmem
  obtain ⟨t, htK, htmax⟩ := hK.exists_isGreatest hKne
  have ht : 0 < t := hK0 htK
  have hF : Profile.F t < 1 / 16 := (Profile.F_bounds ht).2
  let η : ℝ := (1 / 16 - Profile.F t) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨L, hL⟩ := theorem_5_9 hLL hK hK0 η hη
  refine ⟨η, hη, L, ?_⟩
  intro j M hj hmem
  have hm : Profile.F ((j : ℝ) / M) ≤ Profile.F t :=
    Profile.F_strictMonoOn.monotoneOn (hK0 hmem) (hK0 htK) (htmax hmem)
  have he := (abs_lt.mp (hL j M hj hmem)).2
  dsimp [η] at he ⊢
  linarith

end UniformLanczos.Lemma513

#print axioms UniformLanczos.Lemma513.uniform_interior_gap
