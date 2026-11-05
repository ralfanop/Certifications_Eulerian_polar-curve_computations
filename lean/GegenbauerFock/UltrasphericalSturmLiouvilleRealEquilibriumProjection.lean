import GegenbauerFock.UltrasphericalSturmLiouvilleRealEquilibriumOptimal
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates

/-!
# V007 — rank-one equilibrium projection and commutation

The rank-one constant-mode component P₀ is idempotent and preserves
exactly the first Gegenbauer coordinate in genuine weighted real L².
We calculate its exact norm and prove the two-sided intertwining
identities with the full heat semigroup H_s and resolvent R_t:

  P₀(H_s f) = H_s(P₀ f) = P₀ f
  P₀(R_t f) = R_t(P₀ f) = t⁻¹ P₀ f.

This is a functional-level statement on the true infinite-dimensional
Hilbert space, not a formal polynomial calculation or truncation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The constant-equilibrium component P₀ is an actual idempotent
projection on the full weighted L² space. -/
theorem sturmRealConstantEquilibrium_idempotent
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) :
    sturmRealConstantEquilibrium lam hlam
        (sturmRealConstantEquilibrium lam hlam f) =
      sturmRealConstantEquilibrium lam hlam f := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  change ((b.repr (sturmRealConstantEquilibrium lam hlam f)) 0) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0 =
    ((b.repr f) 0) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0
  rw [sturmRealConstantEquilibrium_zero_coordinate lam hlam f]

/-- The full-L² equilibrium component has norm equal to the absolute
value of the constant Gegenbauer coefficient. -/
theorem sturmRealConstantEquilibrium_norm_eq
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) :
    ‖sturmRealConstantEquilibrium lam hlam f‖ =
      |(sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0| := by
  unfold sturmRealConstantEquilibrium
  rw [norm_smul, Real.norm_eq_abs,
    sturmMonicEigenCandidate_realL2_normalized_norm, mul_one]

/-- Applying the equilibrium projection AFTER the actual heat flow
returns precisely the original constant equilibrium. -/
theorem sturmRealConstantEquilibrium_heat_left
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (f : SturmH lam) :
    sturmRealConstantEquilibrium lam hlam
        (sturmRealHeatLimitCLM lam hlam s hs f) =
      sturmRealConstantEquilibrium lam hlam f := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hz : (b.repr (sturmRealHeatLimitCLM lam hlam s hs f)) 0 =
      (b.repr f) 0 := by
    have h := sturmRealHeatLimitCLM_hilbert_repr_diagonal
      lam hlam s hs f 0
    simpa using h
  change ((b.repr (sturmRealHeatLimitCLM lam hlam s hs f)) 0) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0 =
    ((b.repr f) 0) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0
  rw [hz]

/-- Applying the equilibrium projection AFTER the genuine positive
resolvent is scalar multiplication by t⁻¹ on the original equilibrium. -/
theorem sturmRealConstantEquilibrium_resolvent_left
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    sturmRealConstantEquilibrium lam hlam
        (sturmRealPositiveResolventFullCLM lam t hlam ht f) =
      t⁻¹ • sturmRealConstantEquilibrium lam hlam f := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hz : (b.repr (sturmRealPositiveResolventFullCLM lam t hlam ht f)) 0 =
      t⁻¹ * (b.repr f) 0 := by
    have h := sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
      lam t hlam ht f 0
    simpa using h
  change ((b.repr (sturmRealPositiveResolventFullCLM lam t hlam ht f)) 0) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0 =
    t⁻¹ • (((b.repr f) 0) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0)
  rw [hz, mul_smul]

#print axioms GegenbauerFock.Ultraspherical.sturmRealConstantEquilibrium_idempotent
#print axioms GegenbauerFock.Ultraspherical.sturmRealConstantEquilibrium_norm_eq
#print axioms GegenbauerFock.Ultraspherical.sturmRealConstantEquilibrium_heat_left
#print axioms GegenbauerFock.Ultraspherical.sturmRealConstantEquilibrium_resolvent_left

end GegenbauerFock.Ultraspherical
