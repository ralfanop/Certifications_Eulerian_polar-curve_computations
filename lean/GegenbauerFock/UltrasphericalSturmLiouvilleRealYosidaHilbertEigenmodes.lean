import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaGenerator
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertSharpResolventNorm

/-!
# Genuine Gegenbauer eigenmodes of the bounded Sturm Yosida generator

The exact real weighted-L² resolvent is diagonal in the proven
normalized Gegenbauer Hilbert basis. The bounded Yosida generator
therefore acts diagonally on each constructed basis vector, with
the exact rational multiplier obtained by applying its definition.
The normalized zero-degree (constant) mode is an equilibrium.
No unbounded heat semigroup or strong-limit assumption is used.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact rational Yosida-generator eigenvalue on every normalized
Gegenbauer mode in the actual weighted real L² Hilbert space. -/
theorem sturmRealYosidaGenerator_monic_eigenmode
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmRealYosidaGenerator lam t hlam ht
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
      (t * (t * (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ - 1)) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
  let u := sturmMonicEigenCandidate_realL2_normalized lam hlam n
  let r : ℝ := (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have heig :
      sturmRealPositiveResolventFullCLM lam t hlam ht u = r • u := by
    exact sturmMonicEigenCandidate_realL2_normalized_resolvent_diagonal
      lam t hlam ht n
  have hlinear : t • (r • u) - u = (t * r - 1) • u := by
    rw [sub_smul, smul_smul, one_smul]
  change sturmRealYosidaGenerator lam t hlam ht u =
    (t * (t * r - 1)) • u
  calc
    sturmRealYosidaGenerator lam t hlam ht u =
        t • (t • (r • u) - u) := by
          rw [sturmRealYosidaGenerator_apply, heig]
    _ = t • ((t * r - 1) • u) := by rw [hlinear]
    _ = (t * (t * r - 1)) • u := by rw [smul_smul]

/-- The normalized degree-zero mode is fixed infinitesimally by every
bounded Yosida approximation of the closed ultraspherical Sturm operator. -/
theorem sturmRealYosidaGenerator_zero_mode
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    sturmRealYosidaGenerator lam t hlam ht
      (sturmMonicEigenCandidate_realL2_normalized lam hlam 0) = 0 := by
  rw [sturmRealYosidaGenerator_apply,
    sturmRealPositiveResolventFullCLM_zero_mode, smul_smul]
  have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ht)
  rw [hcancel, one_smul, sub_self, smul_zero]

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_monic_eigenmode
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_zero_mode

end GegenbauerFock.Ultraspherical
