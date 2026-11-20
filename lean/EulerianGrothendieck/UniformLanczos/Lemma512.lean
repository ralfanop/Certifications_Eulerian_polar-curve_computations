import UniformLanczos.Theorem59

/-! M12 5.8: positivity of the divided differences and the finite spectral
quadratic form in the Daleckii–Krein calculation. This proves the positivity
step, not the operator differentiation or Fourier decay theorem. -/

namespace UniformLanczos.Lemma512

open Set

noncomputable def dividedDifference (f df : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x = y then df x else (f x - f y) / (x - y)

theorem dividedDifference_nonneg (f df : ℝ → ℝ)
    (hf : MonotoneOn f (Icc (-1 : ℝ) 1))
    (hdf : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ df x)
    {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    0 ≤ dividedDifference f df x y := by
  unfold dividedDifference
  split_ifs with h
  · exact hdf x hx
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact div_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hx hy hlt.le))
        (sub_nonpos.mpr hlt.le)
    · exact div_nonneg (sub_nonneg.mpr (hf hy hx hgt.le))
        (sub_nonneg.mpr hgt.le)

theorem spectral_quadratic_nonneg {n : ℕ} (f df : ℝ → ℝ)
    (hf : MonotoneOn f (Icc (-1 : ℝ) 1))
    (hdf : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ df x)
    (λs : Fin n → ℝ) (hλ : ∀ i, λs i ∈ Icc (-1 : ℝ) 1)
    (E : Fin n → Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, dividedDifference f df (λs i) (λs j) * (E i j)^2 := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (dividedDifference_nonneg f df hf hdf (hλ i) (hλ j))
    (sq_nonneg _)

end UniformLanczos.Lemma512

#print axioms UniformLanczos.Lemma512.dividedDifference_nonneg
#print axioms UniformLanczos.Lemma512.spectral_quadratic_nonneg
