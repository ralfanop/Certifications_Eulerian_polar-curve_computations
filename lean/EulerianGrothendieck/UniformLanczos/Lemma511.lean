import UniformLanczos.Theorem59

/-! M12 5.8: algebraic part of Freud's identity. The B-spline integration by
parts and the lower-degree expansion of the derivative remain separate obligations. -/

namespace UniformLanczos.Lemma511

open Polynomial UniformLanczos.Theorem59

theorem derivative_pairing (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X])
    (m : ℕ) (R : ℝ[X])
    (hder : (P (m + 1)).derivative = Polynomial.C ((m : ℝ) + 1) * P m + R)
    (horth : L (R * P m) = 0) :
    L ((P (m + 1)).derivative * P m) = ((m : ℝ) + 1) * L (P m * P m) := by
  rw [hder, add_mul, map_add, horth, add_zero, mul_assoc,
    ← Polynomial.smul_eq_C_mul, map_smul] <;> rfl

theorem recSq_positive (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X])
    (hd : ∀ i, (P i).natDegree = i) (hm : ∀ i, (P i).Monic)
    (ho : ∀ i j, i ≠ j → L (P i * P j) = 0)
    (hpos : ∀ i, 0 < L (P i * P i)) (m : ℕ) :
    0 < recSq (fun k => L (Polynomial.X ^ k)) m := by
  rw [recSq_eq_norm_ratio L P hd hm ho hpos m]
  exact div_pos (hpos _) (hpos _)

/-- Last normalization step of Freud's identity. The integration-by-parts
equality is expressed on the monic family; it must subsequently be proved
for the cardinal B-spline weight, including endpoint vanishing. -/
theorem freud_of_parts (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X])
    (m : ℕ) (R : ℝ[X]) (M a J : ℝ)
    (ha : 0 < a) (hp : 0 < L (P m * P m))
    (hder : (P (m + 1)).derivative = Polynomial.C ((m : ℝ) + 1) * P m + R)
    (horth : L (R * P m) = 0)
    (hparts : L ((P (m + 1)).derivative * P m) =
      (M * J * a) * L (P m * P m)) :
    ((m : ℝ) + 1) / a = M * J := by
  have h := derivative_pairing L P m R hder horth
  rw [hparts] at h
  have he : M * J * a = (m : ℝ) + 1 :=
    (mul_right_cancel₀ hp.ne' h)
  apply (div_eq_iff ha.ne').2
  exact he.symm

end UniformLanczos.Lemma511

#print axioms UniformLanczos.Lemma511.derivative_pairing
#print axioms UniformLanczos.Lemma511.recSq_positive
#print axioms UniformLanczos.Lemma511.freud_of_parts
