import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaGeneratorConvergence
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# V007 — bounded-operator exponential of the ultraspherical Sturm Yosida generator

For each fixed positive Yosida parameter t, the actual bounded generator
A_t on weighted real L² defines an everywhere-defined norm-convergent
operator exponential S_t(s) := exp(s A_t). The exponential is taken in
the complete real Banach algebra of bounded continuous endomorphisms.

The algebraic semigroup law and identity at time zero are established
without assuming a semigroup for the underlying unbounded closure.
This is the bounded-generator stage; passing to the strong limit
t→∞ and identifying the unbounded C₀ generator remain separate steps.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory
private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Operator exponential of the true bounded Sturm Yosida generator. -/
noncomputable def sturmRealYosidaExponential
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (s : ℝ) : SturmH lam →L[ℝ] SturmH lam :=
  NormedSpace.exp (s • sturmRealYosidaGenerator lam t hlam ht)

/-- The bounded Yosida exponential starts at the actual Hilbert identity. -/
theorem sturmRealYosidaExponential_zero
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    sturmRealYosidaExponential lam t hlam ht 0 =
      (1 : SturmH lam →L[ℝ] SturmH lam) := by
  have hz : (0 : ℝ) • sturmRealYosidaGenerator lam t hlam ht =
      (0 : SturmH lam →L[ℝ] SturmH lam) := by
    ext x
    simp
  change NormedSpace.exp ((0 : ℝ) • sturmRealYosidaGenerator lam t hlam ht) = 1
  rw [hz]
  letI : NormedAlgebra ℚ (SturmH lam →L[ℝ] SturmH lam) :=
    .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_zero

/-- Exact additive-time semigroup identity for each fixed bounded
Yosida generator, as a true identity of continuous linear operators. -/
theorem sturmRealYosidaExponential_add
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (s u : ℝ) :
    sturmRealYosidaExponential lam t hlam ht (s + u) =
      sturmRealYosidaExponential lam t hlam ht s *
        sturmRealYosidaExponential lam t hlam ht u := by
  let A := sturmRealYosidaGenerator lam t hlam ht
  have hcomm : Commute (s • A) (u • A) := by
    change (s • A) * (u • A) = (u • A) * (s • A)
    ext f
    simp [ContinuousLinearMap.mul_def, smul_smul, mul_comm]
  have hadd : (s + u) • A = s • A + u • A := by
    ext x
    simp [add_smul]
  change NormedSpace.exp ((s + u) • A) =
    NormedSpace.exp (s • A) * NormedSpace.exp (u • A)
  rw [hadd]
  letI : NormedAlgebra ℚ (SturmH lam →L[ℝ] SturmH lam) :=
    .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_add_of_commute hcomm

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_zero
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_add

end GegenbauerFock.Ultraspherical
