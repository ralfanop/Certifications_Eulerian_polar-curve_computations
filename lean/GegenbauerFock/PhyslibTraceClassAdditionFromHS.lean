import GegenbauerFock.PhyslibGeneralHSProductTraceClass
import GegenbauerFock.PhyslibTraceClassHSFactorization

/-!
# V007 — unrestricted S₁ addition via the polar-factor/Hilbert–Schmidt bridge

The proof is independent of the ultraspherical model.  Given two
products of genuinely Hilbert–Schmidt endomorphisms, take the polar
factor U of their sum T.  Then |T| = U†T, and the positive diagonal of
|T| is the sum of two scalar products of square-summable families.
Cauchy–Schwarz and the elementary quadratic bound imply diagonal
summability on a complete Hilbert basis.

Finally the already constructed HS factorization of arbitrary trace
class maps gives general closure of the CFC-based Physlib S₁ predicate
under addition.  This does NOT establish the sharp triangle
inequality, a normed-group structure, or completeness.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Any sum of two arbitrary HS products is trace class, without
positivity, dimension, or finite-rank assumptions. -/
theorem isTraceClass_add_of_twoHSProducts
    (R S P Q : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S)
    (hP : HilbertSchmidt.IsHilbertSchmidt P)
    (hQ : HilbertSchmidt.IsHilbertSchmidt Q) :
    IsTraceClass (R * S + P * Q) := by
  let T : H →L[ℂ] H := R * S + P * Q
  let U : H →L[ℂ] H := Polar.polarFactor T
  let A : H →L[ℂ] H := R.adjoint.comp U
  let B : H →L[ℂ] H := P.adjoint.comp U
  have hA : HilbertSchmidt.IsHilbertSchmidt A :=
    HilbertSchmidt.isHilbertSchmidt_comp_right R.adjoint
      (HilbertSchmidt.isHilbertSchmidt_adjoint R hR) U
  have hB : HilbertSchmidt.IsHilbertSchmidt B :=
    HilbertSchmidt.isHilbertSchmidt_comp_right P.adjoint
      (HilbertSchmidt.isHilbertSchmidt_adjoint P hP) U
  obtain ⟨w, b, hAsum⟩ := hA
  have hBsum : Summable (fun i : w => ‖B (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hB
  have hSsum : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hS
  have hQsum : Summable (fun i : w => ‖Q (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hQ
  have hpos : 0 ≤ CFC.abs T := CFC.abs_nonneg T
  have hpolar : U.adjoint.comp T = CFC.abs T := by
    have h := Polar.star_polarFactor_mul_self T
    change star U * T = CFC.abs T at h
    simpa only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_def] using h
  have hdiag (i : w) :
      inner ℂ (b i) (CFC.abs T (b i)) =
        inner ℂ (A (b i)) (S (b i)) +
        inner ℂ (B (b i)) (Q (b i)) := by
    calc
      inner ℂ (b i) (CFC.abs T (b i)) =
          inner ℂ (b i) (U.adjoint
            (R (S (b i)) + P (Q (b i)))) := by
              rw [← hpolar]
              rfl
      _ = inner ℂ (U (b i))
          (R (S (b i)) + P (Q (b i))) :=
        ContinuousLinearMap.adjoint_inner_right U (b i)
          (R (S (b i)) + P (Q (b i)))
      _ = inner ℂ (U (b i)) (R (S (b i))) +
          inner ℂ (U (b i)) (P (Q (b i))) :=
        inner_add_right _ _ _
      _ = inner ℂ (A (b i)) (S (b i)) +
          inner ℂ (B (b i)) (Q (b i)) := by
            rw [← ContinuousLinearMap.adjoint_inner_left R
              (S (b i)) (U (b i)),
              ← ContinuousLinearMap.adjoint_inner_left P
              (Q (b i)) (U (b i))]
            rfl
  have hbound (i : w) :
      (inner ℂ (b i) (CFC.abs T (b i))).re ≤
        (‖A (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2) +
          (‖B (b i)‖ ^ 2 + ‖Q (b i)‖ ^ 2) := by
    rw [hdiag i, Complex.add_re]
    have hfirst :
        (inner ℂ (A (b i)) (S (b i))).re ≤
          ‖A (b i)‖ * ‖S (b i)‖ :=
      (Complex.re_le_norm _).trans
        (norm_inner_le_norm (A (b i)) (S (b i)))
    have hsecond :
        (inner ℂ (B (b i)) (Q (b i))).re ≤
          ‖B (b i)‖ * ‖Q (b i)‖ :=
      (Complex.re_le_norm _).trans
        (norm_inner_le_norm (B (b i)) (Q (b i)))
    nlinarith [sq_nonneg (‖A (b i)‖ - ‖S (b i)‖),
      sq_nonneg (‖B (b i)‖ - ‖Q (b i)‖)]
  have hmajor : Summable (fun i : w =>
      (‖A (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2) +
        (‖B (b i)‖ ^ 2 + ‖Q (b i)‖ ^ 2)) :=
    (hAsum.add hSsum).add (hBsum.add hQsum)
  have hdiagsum : Summable (fun i : w =>
      (inner ℂ (b i) (CFC.abs T (b i))).re) := by
    apply Summable.of_nonneg_of_le
    · intro i
      exact ((ContinuousLinearMap.nonneg_iff_isPositive).mp hpos).re_inner_nonneg_right (b i)
    · exact hbound
    · exact hmajor
  change IsTraceClass T
  exact ⟨w, b, hdiagsum⟩

/-- General additive closure of the actual CFC-absolute Physlib S₁
membership predicate for arbitrary (not necessarily positive)
trace-class operators on a complete complex Hilbert space. -/
theorem isTraceClass_add_via_polarHS
    {T V : H →L[ℂ] H}
    (hT : IsTraceClass T) (hV : IsTraceClass V) :
    IsTraceClass (T + V) := by
  obtain ⟨R, S, hR, hS, hRS⟩ := traceClass_exists_HS_mul_HS T hT
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := traceClass_exists_HS_mul_HS V hV
  have h := isTraceClass_add_of_twoHSProducts R S P Q hR hS hP hQ
  rw [hRS, hPQ] at h
  exact h

#print axioms ProbabilisticTheory.isTraceClass_add_of_twoHSProducts
#print axioms ProbabilisticTheory.isTraceClass_add_via_polarHS

end ProbabilisticTheory
