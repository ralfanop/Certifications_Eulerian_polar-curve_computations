import GegenbauerFock.GegenbauerIntrinsicEntireFockOperator
import GegenbauerFock.HilbertGram

/-!
# V007 — equality of genuine ultraspherical Gram pairings in analytic Fock L²

The full Gaussian Bargmann–Fock isometric equivalence preserves the
complex Hilbert inner product of the Gegenbauer transform's outputs.
Hence the actual Gram sesquilinear form on ultraspherical L² coincides
exactly with that of the coefficient-space transform.

This is not merely a Gram estimate or a diagonal norm identity: it
holds for arbitrary two input L² vectors, with their genuine complex
Hilbert inner product.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Transport of the complete complex inner product from coefficient
Fock space to genuine entire Gaussian L² functions. -/
theorem C_intrinsicEntire_inner_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam)) :
    inner ℂ (C_intrinsicEntire lam alpha hlam ha f)
      (C_intrinsicEntire lam alpha hlam ha g) =
    inner ℂ (C lam alpha hlam ha f) (C lam alpha hlam ha g) := by
  rw [C_intrinsicEntire_apply, C_intrinsicEntire_apply]
  exact (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).inner_map_map
    (C lam alpha hlam ha f) (C lam alpha hlam ha g)

/-- The actual intrinsic-Gaussian and coefficient Fock Gram operators
have identical sesquilinear pairings on all pairs of source functions. -/
theorem C_intrinsicEntire_gram_pairing
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam)) :
    inner ℂ (HilbertGram.gram (C_intrinsicEntire lam alpha hlam ha) f) g =
      inner ℂ (gram lam alpha hlam ha f) g := by
  change inner ℂ (HilbertGram.gram (C_intrinsicEntire lam alpha hlam ha) f) g =
    inner ℂ (HilbertGram.gram (C lam alpha hlam ha) f) g
  rw [HilbertGram.gram_inner, HilbertGram.gram_inner]
  exact C_intrinsicEntire_inner_eq lam alpha hlam ha f g

/-- The positive quadratic Gram energy is invariant under the passage
from true ultraspherical coefficients to genuine holomorphic L² data. -/
theorem C_intrinsicEntire_gram_energy
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    RCLike.re (inner ℂ
      (HilbertGram.gram (C_intrinsicEntire lam alpha hlam ha) f) f) =
    RCLike.re (inner ℂ (gram lam alpha hlam ha f) f) := by
  exact congrArg RCLike.re
    (C_intrinsicEntire_gram_pairing lam alpha hlam ha f f)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_inner_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_pairing
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_energy

end GegenbauerFock.GeneralUltrasphericalFock
