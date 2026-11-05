import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — symmetry and exact mean conservation of the full L² heat limit

The genuine full-space Yosida heat-limit continuous linear operators
have the exact diagonal action in the normalized Gegenbauer Hilbert
basis. Parseval's sesquilinear expansion therefore proves symmetry
for arbitrary pairs of weighted real L² vectors, not just polynomials.

The zero coordinate is preserved exactly for every input, giving the
operator-level conservation law and invariance of mean-zero data.
This does not yet identify the unbounded infinitesimal generator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual weighted L² heat-limit operator is symmetric on ALL
pairs of vectors; no polynomial-core restriction is imposed. -/
theorem sturmRealHeatLimitCLM_inner_symmetric
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f g : SturmH lam) :
    inner ℝ (sturmRealHeatLimitCLM lam hlam s hs f) g =
      inner ℝ f (sturmRealHeatLimitCLM lam hlam s hs g) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let T := sturmRealHeatLimitCLM lam hlam s hs
  have hf (n : ℕ) :
      (b.repr (T f)) n =
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) *
          (b.repr f) n :=
    sturmRealHeatLimitCLM_hilbert_repr_diagonal lam hlam s hs f n
  have hg (n : ℕ) :
      (b.repr (T g)) n =
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) *
          (b.repr g) n :=
    sturmRealHeatLimitCLM_hilbert_repr_diagonal lam hlam s hs g n
  have hterm (n : ℕ) :
      inner ℝ (T f) (b n) * inner ℝ (b n) g =
        inner ℝ f (b n) * inner ℝ (b n) (T g) := by
    have hleft (x : SturmH lam) :
        inner ℝ x (b n) = (b.repr x) n :=
      (real_inner_comm x (b n)).symm.trans
        (HilbertBasis.repr_apply_apply b x n).symm
    have hright (x : SturmH lam) :
        inner ℝ (b n) x = (b.repr x) n :=
      (HilbertBasis.repr_apply_apply b x n).symm
    rw [hleft (T f), hright g, hleft f, hright (T g), hf n, hg n]
    ring
  calc
    inner ℝ (T f) g =
        ∑' n : ℕ, inner ℝ (T f) (b n) * inner ℝ (b n) g :=
      (b.tsum_inner_mul_inner (T f) g).symm
    _ = ∑' n : ℕ, inner ℝ f (b n) * inner ℝ (b n) (T g) :=
      tsum_congr hterm
    _ = inner ℝ f (T g) := b.tsum_inner_mul_inner f (T g)

/-- The full heat semigroup preserves the constant Gegenbauer
Fourier coefficient exactly for arbitrary genuine weighted L² input. -/
theorem sturmRealHeatLimitCLM_constant_coefficient_preserved
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : SturmH lam) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (sturmRealHeatLimitCLM lam hlam s hs f) 0 =
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 := by
  have h := sturmRealHeatLimitCLM_hilbert_repr_diagonal
    lam hlam s hs f 0
  simpa only [Nat.cast_zero, zero_add, zero_mul, mul_zero, neg_zero, Real.exp_zero, one_mul] using h

/-- A zero constant Gegenbauer coefficient stays zero at all times
for the actual full-L² heat-limit contraction. -/
theorem sturmRealHeatLimitCLM_mean_zero_invariant
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : SturmH lam)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (sturmRealHeatLimitCLM lam hlam s hs f) 0 = 0 := by
  rw [sturmRealHeatLimitCLM_constant_coefficient_preserved lam hlam s hs f]
  exact hzero

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_inner_symmetric
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_constant_coefficient_preserved
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_mean_zero_invariant

end GegenbauerFock.Ultraspherical
