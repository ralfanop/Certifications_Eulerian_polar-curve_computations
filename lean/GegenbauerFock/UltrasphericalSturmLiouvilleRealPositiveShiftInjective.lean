import GegenbauerFock.UltrasphericalSturmLiouvilleRealPositiveShiftDenseRange

/-!
# V007 — exact uniqueness of the genuine real L² shifted Sturm equation

The preceding algebraic theorem gives an EXACT polynomial preimage
of each weighted-L² polynomial vector under tI-L, for t>0.

Symmetry of the actual unbounded Sturm domain and these genuine
polynomial preimages imply that the kernel of every positive shifted
operator is trivial, even WITHOUT assuming dissipativity/nonpositivity.
The same argument proves uniqueness for the shifted equation on the
entire original real polynomial-image Hilbert domain.

This is not a surjectivity claim on all L² and not a proof of
self-adjointness of the closure.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial
private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every positive real shifted genuine Sturm operator has trivial
kernel on the true polynomial image domain, by range surjectivity on
polynomials and symmetric Hilbert Green pairing. -/
theorem sturmRealPartialPositiveShift_kernel_eq_zero
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).domain)
    (hx : t • (x : SturmH lam) -
        sturmRealPartialOperator lam hlam x = 0) :
    x = 0 := by
  let p := sturmRealDomainRepresentative lam hlam
    (x : sturmRealPolynomialDomain lam hlam)
  have hrep :
      sturmRealPolynomialLp lam hlam p = (x : SturmH lam) :=
    sturmRealDomainRepresentative_spec lam hlam x
  obtain ⟨y, hy⟩ :=
    sturmRealPartialPositiveShift_polynomial_preimage
      lam t hlam ht p
  have hsym := sturmRealPartialOperator_symmetric lam hlam x y
  have hself : inner ℝ (x : SturmH lam) (x : SturmH lam) = 0 := by
    calc
      inner ℝ (x : SturmH lam) (x : SturmH lam) =
          inner ℝ (x : SturmH lam)
            (t • (y : SturmH lam) -
              sturmRealPartialOperator lam hlam y) := by
        rw [hy, hrep]
      _ = t * inner ℝ (x : SturmH lam) (y : SturmH lam) -
            inner ℝ (x : SturmH lam)
              (sturmRealPartialOperator lam hlam y) := by
        rw [inner_sub_right, real_inner_smul_right]
      _ = t * inner ℝ (x : SturmH lam) (y : SturmH lam) -
            inner ℝ (sturmRealPartialOperator lam hlam x)
              (y : SturmH lam) := by
        rw [hsym]
      _ = inner ℝ
            (t • (x : SturmH lam) -
              sturmRealPartialOperator lam hlam x)
              (y : SturmH lam) := by
        rw [inner_sub_left, real_inner_smul_left]
      _ = 0 := by rw [hx]; simp
  apply Subtype.ext
  exact inner_self_eq_zero.mp hself

/-- The actual positive shifted differential equation on the real
polynomial domain has AT MOST ONE solution for each right-hand side. -/
theorem sturmRealPartialPositiveShift_injective
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Function.Injective
      (fun x : (sturmRealPartialOperator lam hlam).domain =>
        t • (x : SturmH lam) -
          sturmRealPartialOperator lam hlam x) := by
  intro x y hxy
  have hdiff :
      t • ((x - y : (sturmRealPartialOperator lam hlam).domain) :
        SturmH lam) -
          sturmRealPartialOperator lam hlam (x - y) = 0 := by
    change t • ((x : SturmH lam) - (y : SturmH lam)) -
        sturmRealPartialOperator lam hlam (x - y) = 0
    rw [smul_sub, LinearPMap.map_sub]
    calc
      t • (x : SturmH lam) - t • (y : SturmH lam) -
          (sturmRealPartialOperator lam hlam x -
            sturmRealPartialOperator lam hlam y) =
        (t • (x : SturmH lam) -
            sturmRealPartialOperator lam hlam x) -
          (t • (y : SturmH lam) -
            sturmRealPartialOperator lam hlam y) := by abel
      _ = 0 := sub_eq_zero.mpr hxy
  have hz :=
    sturmRealPartialPositiveShift_kernel_eq_zero
      lam t hlam ht (x - y) hdiff
  exact sub_eq_zero.mp hz

#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialPositiveShift_kernel_eq_zero
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialPositiveShift_injective

end GegenbauerFock.Ultraspherical
