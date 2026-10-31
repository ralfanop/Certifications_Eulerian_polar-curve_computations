import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaGenerator
import Mathlib.Tactic.ModuleNF

/-!
# V007 — exact Yosida eigenvalue on each normalized Gegenbauer L² mode

The true all-L² normalized Gegenbauer vectors are eigenvectors of
the genuine closed positive Sturm resolvent. This proves that they
are also eigenvectors of the actual bounded Yosida generator, with
scalar eigenvalue -t omega_n/(t+omega_n), omega_n=n(n+2lambda).
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Actual bounded Yosida generator on the n-th normalized Gegenbauer
Hilbert vector, with exact scalar eigenvalue. -/
theorem sturmRealYosidaGenerator_normalized_eigen
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmRealYosidaGenerator lam t hlam ht
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
    (-t * ((n : ℝ) * ((n : ℝ) + 2 * lam)) /
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
  let g : SturmH lam := sturmMonicEigenCandidate_realL2_normalized lam hlam n
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  have homega : 0 ≤ omega := by dsimp [omega]; positivity
  have hden : t + omega ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg ht homega)
  have hres : R g = (t + omega)⁻¹ • g :=
    sturmMonicRealHilbertBasis_full_resolvent_eigen lam t hlam ht n
  have hscalar : t * (t * (t + omega)⁻¹ - 1) =
      -t * omega / (t + omega) := by
    field_simp
    ring
  change sturmRealYosidaGenerator lam t hlam ht g =
    (-t * omega / (t + omega)) • g
  calc
    sturmRealYosidaGenerator lam t hlam ht g =
      t • (t • R g - g) := sturmRealYosidaGenerator_apply lam t hlam ht g
    _ = t • (t • ((t + omega)⁻¹ • g) - g) := by rw [hres]
    _ = (t * (t * (t + omega)⁻¹ - 1)) • g := by
      module_nf with ℝ
    _ = (-t * omega / (t + omega)) • g := by rw [hscalar]

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_normalized_eigen

end GegenbauerFock.Ultraspherical
