import GegenbauerFock.RealNuclearOneCompleteSourceSingularS1
import Mathlib

/-!
# V007 — source-Gram eigenbasis constructs a real singular output family

For an arbitrary bounded real Hilbert-space operator T, a positive
eigenvector of the actual Gram T†T has norm scaling sqrt(mu) under T.
A strictly positive Gram eigensystem that is orthonormal on the source
therefore gives a canonically constructed orthonormal output family,
with no assumption that it is complete and no global unitary phase.

If this source eigensystem is a COMPLETE countable Hilbert basis and
the square roots of its eigenvalues are summable, the existing
one-full-source nuclear theorem constructs the actual norm-convergent
rank-one series and proves its exact universal real nuclear cost.

The complete-source / positive-eigenvalue assumptions are essential.
This does NOT construct the singular basis for an arbitrary compact
operator with a nontrivial kernel. The separate construction of a
spectral basis for the positive part of T†T and of a partial isometry
with arbitrary defects remains to be proved.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
variable [CompleteSpace E] [CompleteSpace F]

/-- A compact real operator has a compact genuine Gram T†T. -/
theorem realGram_compact_of_compact_v007
    (T : E →L[ℝ] F) (hT : IsCompactOperator T) :
    IsCompactOperator (T.adjoint ∘L T) := by
  change IsCompactOperator (fun x : E => T.adjoint (T x))
  exact hT.clm_comp T.adjoint

/-- The squared norm of a real Gram eigenvector is scaled by the
actual eigenvalue. No kernel assumption on T is needed. -/
theorem realGram_eigenvector_norm_sq_v007
    (T : E →L[ℝ] F) (mu : ℝ) (x : E)
    (hx : (T.adjoint ∘L T) x = mu • x) :
    ‖T x‖ ^ 2 = mu * ‖x‖ ^ 2 := by
  calc
    ‖T x‖ ^ 2 = inner ℝ ((T.adjoint ∘L T) x) x := by
      simpa only [ContinuousLinearMap.comp_apply] using
        (T.apply_norm_sq_eq_inner_adjoint_left x)
    _ = mu * ‖x‖ ^ 2 := by
      rw [hx, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- Normalization by 1/sqrt(mu) is norm preserving on each
positive real Gram eigenspace. -/
theorem realGram_normalized_eigenvector_norm_v007
    (T : E →L[ℝ] F) (mu : ℝ) (hmu : 0 < mu)
    (x : E) (hx : (T.adjoint ∘L T) x = mu • x) :
    ‖(Real.sqrt mu)⁻¹ • T x‖ = ‖x‖ := by
  have hroot : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
  have hsq := realGram_eigenvector_norm_sq_v007 T mu x hx
  have hnorm : ‖T x‖ = Real.sqrt mu * ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hmu.le]
    exact hsq
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hroot,
    hnorm, ← mul_assoc, inv_mul_cancel₀ hroot.ne', one_mul]

/-- A source orthonormal family of strictly positive real Gram
eigenvectors gives an actual orthonormal family of normalized
output singular vectors, even if the output family is incomplete. -/
theorem realGram_positiveEigenfamily_output_orthonormal_v007
    {ι : Type*} (T : E →L[ℝ] F)
    (b : ι → E) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 < mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i) :
    Orthonormal ℝ
      (fun i => (Real.sqrt (mu i))⁻¹ • T (b i)) := by
  constructor
  · intro i
    rw [realGram_normalized_eigenvector_norm_v007
      T (mu i) (hmu i) (b i) (heig i)]
    exact hb.norm_eq_one i
  · intro i j hij
    have hzero : inner ℝ (T (b i)) (T (b j)) = 0 := by
      calc
        inner ℝ (T (b i)) (T (b j)) =
            inner ℝ ((T.adjoint ∘L T) (b i)) (b j) := by
          exact (T.adjoint_inner_left (b j) (T (b i))).symm
        _ = 0 := by
          rw [heig i, real_inner_smul_left, hb.inner_eq_zero hij]
          ring
    rw [real_inner_smul_left, real_inner_smul_right, hzero]
    ring

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The complete positive Gram eigensystem produces its own output
singular family and the sharp nuclear infimum, without assuming
either a target orthonormal family or an operator rank-one series.

This applies in particular to a compact injective real Hilbert
operator once a complete positive Gram eigenbasis has been supplied.
The existence of that eigenbasis is NOT proved by this statement. -/
theorem realGram_completePositiveEigenbasis_nuclear_exact_trace_v007
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (mu : ℕ → ℝ) (hmu : ∀ n, 0 < mu n)
    (hs : Summable (fun n => Real.sqrt (mu n)))
    (heig : ∀ n, (T.adjoint ∘L T) (b n) = mu n • b n) :
    HasRealNuclearRankOneSeries T ∧
      realNuclearInfimum T = ∑' n : ℕ, Real.sqrt (mu n) := by
  let c : ℕ → H := fun n =>
    (Real.sqrt (mu n))⁻¹ • T (b n)
  have hc : Orthonormal ℝ c := by
    exact realGram_positiveEigenfamily_output_orthonormal_v007
      T b b.orthonormal mu hmu heig
  have hcoeff (n : ℕ) :
      T (b n) = Real.sqrt (mu n) • c n := by
    dsimp only [c]
    rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 (hmu n)).ne',
      one_smul]
  exact realOneFullSourceSingular_nuclear_exact_trace
    T b c hc (fun n => Real.sqrt (mu n))
    (fun n => Real.sqrt_nonneg _) hs hcoeff

#print axioms GegenbauerFock.Ultraspherical.realGram_compact_of_compact_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_eigenvector_norm_sq_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_normalized_eigenvector_norm_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_positiveEigenfamily_output_orthonormal_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_completePositiveEigenbasis_nuclear_exact_trace_v007

end GegenbauerFock.Ultraspherical
