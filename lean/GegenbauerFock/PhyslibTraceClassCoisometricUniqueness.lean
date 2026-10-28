import GegenbauerFock.PhyslibTraceClassCoisometricDecomposition

/-!
# V007 — uniqueness of the genuine Schatten-S₁ split coordinates

The coisometric CFC trace-normed Banach space has a canonical
splitting T=E(R T)+Q T, where E X=U†XU, R T=UTU†,
Q=id-E∘R and R∘E=id when U U†=1.

This module proves uniqueness of the coordinates: if
T=E(X)+Y with R(Y)=0, then X=R(T) and Y=Q(T).

This does not assume positivity or that E is surjective and
does not identify the distinct ultraspherical/Fock Hilbert spaces.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The source coordinate in any coisometric CFC-S₁ splitting is
uniquely recovered by the continuous retraction. -/
theorem coisometric_split_source_coordinate_unique_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T X Y : TraceClass H)
    (hT : T = sandwichContinuous U.adjoint U X + Y)
    (hY : sandwichContinuous U U.adjoint Y = 0) :
    sandwichContinuous U U.adjoint T = X := by
  rw [hT, map_add, coisometric_sandwich_split_apply_v007 U hUUstar X, hY]
  exact add_zero X

/-- The kernel coordinate is uniquely the continuous complementary
projection Q(T), for any nonpositive or nonnormal trace-class T. -/
theorem coisometric_split_kernel_coordinate_unique_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T X Y : TraceClass H)
    (hT : T = sandwichContinuous U.adjoint U X + Y)
    (hY : sandwichContinuous U U.adjoint Y = 0) :
    coisometric_complementaryProjection_v007 U T = Y := by
  have hEY :
      coisometric_complementaryProjection_v007 U
        (sandwichContinuous U.adjoint U X) = 0 := by
    change sandwichContinuous U.adjoint U X -
      coisometric_sandwich_projection_v007 U
        (sandwichContinuous U.adjoint U X) = 0
    rw [coisometric_projection_fixes_image_v007 U hUUstar X]
    exact sub_self _
  have hQY :
      coisometric_complementaryProjection_v007 U Y = Y :=
    (coisometric_retraction_kernel_iff_complement_fixed_v007
      U hUUstar Y).mp hY
  rw [hT, map_add, hEY, hQY]
  exact zero_add Y

/-- Full uniqueness of both coordinates in the closed algebraic
coisometric Schatten-S₁ decomposition, without positivity. -/
theorem coisometric_split_coordinates_unique_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T X Y : TraceClass H)
    (hT : T = sandwichContinuous U.adjoint U X + Y)
    (hY : sandwichContinuous U U.adjoint Y = 0) :
    X = sandwichContinuous U U.adjoint T ∧
      Y = coisometric_complementaryProjection_v007 U T := by
  constructor
  · exact (coisometric_split_source_coordinate_unique_v007
      U hUUstar T X Y hT hY).symm
  · exact (coisometric_split_kernel_coordinate_unique_v007
      U hUUstar T X Y hT hY).symm

#print axioms ProbabilisticTheory.TraceClass.coisometric_split_source_coordinate_unique_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_split_kernel_coordinate_unique_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_split_coordinates_unique_v007

end ProbabilisticTheory.TraceClass
