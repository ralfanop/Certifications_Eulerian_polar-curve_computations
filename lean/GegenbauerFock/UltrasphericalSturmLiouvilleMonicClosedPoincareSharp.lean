import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedDirichletPoincare
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedSpectralGap

/-!
# V007 — sharpness of the closed Sturm Poincare constant

The true closed ultraspherical Sturm operator possesses a nonzero
degree-one polynomial eigenvector with eigenvalue -(1+2λ).
The already certified complete Fourier-Gegenbauer diagonalization
implies its degree-zero Fourier coefficient is zero.

Consequently the degree-one eigenvector attains equality in the
closed-operator Dirichlet Poincare inequality. Thus no universally
larger constant can hold on the mean-zero part of the true closed
Sturm domain. This is stronger than optimality on finite formal
Fourier sequences.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The degree-one genuine closed Sturm eigenvector is orthogonal to
the constant normalized Gegenbauer mode. -/
theorem sturmRealClosed_first_nonconstant_eigenmode_zero_constant
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) ≠ 0 ∧
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0 ∧
      (sturmRealPartialOperator lam hlam).closure x =
        -(1 + 2 * lam) • (x : SturmH lam) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let A := (sturmRealPartialOperator lam hlam).closure
  obtain ⟨x, hx, heig⟩ :=
    sturmRealClosed_first_nonconstant_eigenmode lam hlam
  have hdiag0 : (b.repr (A x)) 0 = 0 := by
    have hdiag :=
      (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
        lam hlam).2 x 0
    simpa only [Nat.cast_zero, zero_add, zero_mul, neg_zero] using hdiag
  have hlin : (b.repr (A x)) 0 =
      -(1 + 2 * lam) * (b.repr (x : SturmH lam)) 0 := by
    rw [heig, map_smul]
    rfl
  have hprod :
      -(1 + 2 * lam) * (b.repr (x : SturmH lam)) 0 = 0 := by
    rw [← hlin]
    exact hdiag0
  have hfactor : -(1 + 2 * lam) ≠ 0 := by
    have hpositive : 0 < 1 + 2 * lam := by linarith
    exact neg_ne_zero.mpr hpositive.ne'
  have hzero := (mul_eq_zero.mp hprod).resolve_left hfactor
  exact ⟨x, hx, hzero, heig⟩

/-- The gap 1+2λ is the largest constant valid in the genuine
closed-operator Dirichlet Poincare inequality for all zero-constant
Fourier vectors. -/
theorem sturmMonic_realL2_closed_Dirichlet_poincare_constant_optimal
    (lam C : ℝ) (hlam : 0 < lam)
    (hbound :
      ∀ x : (sturmRealPartialOperator lam hlam).closure.domain,
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
            (x : SturmH lam) 0 = 0 →
        C * ‖(x : SturmH lam)‖ ^ 2 ≤
          -inner ℝ ((sturmRealPartialOperator lam hlam).closure x)
            (x : SturmH lam)) :
    C ≤ 1 + 2 * lam := by
  obtain ⟨x, hx, hzero, heig⟩ :=
    sturmRealClosed_first_nonconstant_eigenmode_zero_constant lam hlam
  have henergy :
      -inner ℝ ((sturmRealPartialOperator lam hlam).closure x)
        (x : SturmH lam) =
        (1 + 2 * lam) * ‖(x : SturmH lam)‖ ^ 2 := by
    rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hh := hbound x hzero
  rw [henergy] at hh
  have hpos : 0 < ‖(x : SturmH lam)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hx) _
  exact (mul_le_mul_iff_of_pos_right hpos).mp hh

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_first_nonconstant_eigenmode_zero_constant
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_realL2_closed_Dirichlet_poincare_constant_optimal

end GegenbauerFock.Ultraspherical
