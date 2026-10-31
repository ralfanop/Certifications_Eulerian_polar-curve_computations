import GegenbauerFock.GegenbauerIntrinsicEntireFockOperator
import GegenbauerFock.GaussianAreaIntrinsicCompleteSpace
import GegenbauerFock.HilbertGram

/-!
# V007 — genuine Gaussian Fock Gram pairings with local completeness

Full intrinsic Bargmann–Fock synthesis is an onto Hilbert isometry, and
the analytic submodule is a CLOSED subspace by independently proved
Gaussian planar-moment uniqueness. The local completeness instance
therefore justifies the Hilbert adjoint used in the analytic Gram.

The full ultraspherical compact transform is *not* asserted onto.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The true source Gram formed using the intrinsic holomorphic Gaussian
Fock codomain. The required completeness of that codomain follows from
the analytic polynomial-density theorem, not from an assumption. -/
noncomputable def C_intrinsicEntire_gram
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact HilbertGram.gram (C_intrinsicEntire lam alpha hlam ha)

/-- Exact preservation of the complex Hilbert pairing after passage from
Fock coefficient sequences to actual entire Gaussian L² classes. -/
theorem C_intrinsicEntire_inner_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam)) :
    inner ℂ (C_intrinsicEntire lam alpha hlam ha f)
      (C_intrinsicEntire lam alpha hlam ha g) =
    inner ℂ (C lam alpha hlam ha f) (C lam alpha hlam ha g) := by
  rw [C_intrinsicEntire_apply, C_intrinsicEntire_apply]
  exact (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).inner_map_map
    (C lam alpha hlam ha f) (C lam alpha hlam ha g)

/-- Genuine intrinsic and coefficient Fock source Grams have identical
sesquilinear pairings, without assuming a complete target Hilbert space. -/
theorem C_intrinsicEntire_gram_pairing
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam)) :
    inner ℂ (C_intrinsicEntire_gram lam alpha hlam ha f) g =
      inner ℂ (gram lam alpha hlam ha f) g := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  change inner ℂ (HilbertGram.gram (C_intrinsicEntire lam alpha hlam ha) f) g =
    inner ℂ (HilbertGram.gram (C lam alpha hlam ha) f) g
  rw [HilbertGram.gram_inner, HilbertGram.gram_inner]
  exact C_intrinsicEntire_inner_eq lam alpha hlam ha f g

/-- Invariance of the positive quadratic source-Gram energy. -/
theorem C_intrinsicEntire_gram_energy
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    RCLike.re (inner ℂ (C_intrinsicEntire_gram lam alpha hlam ha f) f) =
    RCLike.re (inner ℂ (gram lam alpha hlam ha f) f) := by
  exact congrArg RCLike.re
    (C_intrinsicEntire_gram_pairing lam alpha hlam ha f f)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_inner_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_pairing
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_energy

end GegenbauerFock.GeneralUltrasphericalFock
