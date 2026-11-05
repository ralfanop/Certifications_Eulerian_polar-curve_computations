import GegenbauerFock.GegenbauerIntrinsicEntireGramIdentity
import GegenbauerFock.SingularEigenspaceIsometry

/-!
# V007 — exact singular normalization on genuine analytic Gaussian output

The real ultraspherical source Gram of the genuine transform into
the closed Bargmann–Fock Gaussian L² holomorphic space agrees with the
certified concrete coefficient-side Gram. For every strictly positive
real eigenvalue, the analysis transform into the ACTUAL holomorphic
Hilbert space scales every eigenvector norm by sqrt(mu). Dividing
by that factor gives a norm- and distance-preserving mapping on the
whole corresponding eigenspace, not only on an orthonormal basis.

The argument uses the certified onto isometric Fock synthesis U
solely to transport Hilbert norms; it does not claim C_hol onto.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Exact singular-vector norm identity for the ACTUAL ultraspherical
transform into entire Gaussian L² holomorphic functions. -/
theorem C_intrinsicEntire_positive_gram_eigenvector_norm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : C_intrinsicEntire_gram lam alpha hlam ha f = (mu : ℂ) • f) :
    ‖C_intrinsicEntire lam alpha hlam ha f‖ =
      Real.sqrt mu * ‖f‖ := by
  have hfcoeff : gram lam alpha hlam ha f = (mu : ℂ) • f := by
    simpa only [C_intrinsicEntire_gram_eq lam alpha hlam ha] using hf
  rw [C_intrinsicEntire_norm lam alpha hlam ha]
  exact C_positive_gram_eigenvector_norm lam alpha hlam ha mu hmu f hfcoeff

/-- The normalized REAL Gaussian entire Fock transform preserves
Hilbert norm of every vector in a positive source Gram eigenspace. -/
theorem C_intrinsicEntire_normalized_positive_eigenvector_norm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : C_intrinsicEntire_gram lam alpha hlam ha f = (mu : ℂ) • f) :
    ‖((Real.sqrt mu : ℂ)⁻¹ • C_intrinsicEntire lam alpha hlam ha f)‖ =
      ‖f‖ := by
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  have hfcoeff : gram lam alpha hlam ha f = (mu : ℂ) • f := by
    simpa only [C_intrinsicEntire_gram_eq lam alpha hlam ha] using hf
  calc
    ‖((Real.sqrt mu : ℂ)⁻¹ • C_intrinsicEntire lam alpha hlam ha f)‖ =
        ‖U ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)‖ := by
          rw [C_intrinsicEntire_apply, map_smul]
    _ = ‖((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)‖ :=
      U.norm_map _
    _ = ‖f‖ :=
      C_normalized_positive_eigenvector_norm
        lam alpha hlam ha mu hmu f hfcoeff

/-- The actual intrinsic Gaussian Fock transform divided by sqrt(mu)
is distance-preserving on each full positive ultraspherical-Gram
eigenspace (including arbitrary, non-normalized vectors). -/
theorem C_intrinsicEntire_normalized_positive_eigenspace_dist
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : C_intrinsicEntire_gram lam alpha hlam ha f = (mu : ℂ) • f)
    (hg : C_intrinsicEntire_gram lam alpha hlam ha g = (mu : ℂ) • g) :
    dist ((Real.sqrt mu : ℂ)⁻¹ • C_intrinsicEntire lam alpha hlam ha f)
      ((Real.sqrt mu : ℂ)⁻¹ • C_intrinsicEntire lam alpha hlam ha g) =
      dist f g := by
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  have hfcoeff : gram lam alpha hlam ha f = (mu : ℂ) • f := by
    simpa only [C_intrinsicEntire_gram_eq lam alpha hlam ha] using hf
  have hgcoeff : gram lam alpha hlam ha g = (mu : ℂ) • g := by
    simpa only [C_intrinsicEntire_gram_eq lam alpha hlam ha] using hg
  calc
    dist ((Real.sqrt mu : ℂ)⁻¹ • C_intrinsicEntire lam alpha hlam ha f)
        ((Real.sqrt mu : ℂ)⁻¹ • C_intrinsicEntire lam alpha hlam ha g) =
      dist (U ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f))
        (U ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha g)) := by
          rw [C_intrinsicEntire_apply, C_intrinsicEntire_apply,
            map_smul, map_smul]
    _ = dist ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)
        ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha g) :=
      U.dist_map _ _
    _ = dist f g :=
      C_normalized_positive_eigenspace_dist lam alpha hlam ha
        mu hmu f g hfcoeff hgcoeff

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_positive_gram_eigenvector_norm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_normalized_positive_eigenvector_norm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_normalized_positive_eigenspace_dist

end GegenbauerFock.GeneralUltrasphericalFock
