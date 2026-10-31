import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaGenerator

/-!
# V007 — exact Fourier coordinate eigenvalues of the bounded Yosida generator

On the genuine normalized complete Gegenbauer Hilbert basis, the
previously certified full-L² resolvent is diagonal:
  (repr (R_t f)) n = (t + omega_n)⁻¹ (repr f) n,
  omega_n = n (n + 2 lambda).

We now identify the actual bounded Yosida generator A_t=t(tR_t-I)
on EVERY weighted-L² vector, not merely on polynomial eigenmodes:
  (repr (A_t f)) n = -t omega_n/(t+omega_n) (repr f) n.
This prepares the strong limit of the Yosida semigroup multipliers.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual all-L² bounded Yosida generator is precisely
the expected spectral diagonal multiplier in the explicit normalized
Gegenbauer Hilbert basis, at every degree and every input vector. -/
theorem sturmRealYosidaGenerator_hilbert_repr_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) (n : ℕ) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (sturmRealYosidaGenerator lam t hlam ht f) n =
    (-t * ((n : ℝ) * ((n : ℝ) + 2 * lam)) /
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))) *
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  have homega : 0 ≤ omega := by
    dsimp [omega]
    positivity
  have hden : t + omega ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg ht homega)
  have hR := sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
    lam t hlam ht f n
  change (b.repr (R f)) n = (t + omega)⁻¹ * (b.repr f) n at hR
  have hs : t * (t * (t + omega)⁻¹ - 1) =
      -t * omega / (t + omega) := by
    field_simp
    ring
  change (b.repr (sturmRealYosidaGenerator lam t hlam ht f)) n =
    (-t * omega / (t + omega)) * (b.repr f) n
  calc
    (b.repr (sturmRealYosidaGenerator lam t hlam ht f)) n =
      t * (t * (b.repr (R f)) n - (b.repr f) n) := by
        rw [sturmRealYosidaGenerator_apply, map_smul, map_sub, map_smul]
        rfl
    _ = t * (t * ((t + omega)⁻¹ * (b.repr f) n) -
          (b.repr f) n) := by rw [hR]
    _ = (t * (t * (t + omega)⁻¹ - 1)) * (b.repr f) n := by ring
    _ = (-t * omega / (t + omega)) * (b.repr f) n := by rw [hs]

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_hilbert_repr_diagonal

end GegenbauerFock.Ultraspherical
