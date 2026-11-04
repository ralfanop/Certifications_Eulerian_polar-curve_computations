import GegenbauerFock.RealCompactGramActiveSingularModes

/-!
# V007 — pointwise operator reconstruction from the actual Gram eigenbasis

Given a genuine Hilbert basis b of eigenmodes of T†T with μ_i ≥ 0,
T(x) is reconstructed by its positive Gram modes only. The zero
Gram modes are genuinely in ker(T), rather than being divided by zero.

This is an exact HasSum identity in the target Hilbert space for each
x, not a claim that the positive-support operator series converges
in operator norm. The latter follows under singular S₁ summability,
which is certified in another module, but requires an additional
operator-series identification.

No global unitary polar phase is assumed and neither kernel nor
cokernel is assumed trivial or equidimensional.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

/-- Complete actual Gram eigenbasis reconstruction of T, with
zero modes explicitly killed. The summation is unconditional and
covers arbitrary Hilbert basis index types. -/
theorem realGram_fullEigenbasis_active_singular_hasSum
    (T : H →L[ℝ] H) (b : HilbertBasis ι ℝ H)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i)
    (x : H) :
    HasSum
      (fun i : ι =>
        if 0 < mu i then
          (inner ℝ (b i) x) •
            (Real.sqrt (mu i) •
              ((Real.sqrt (mu i))⁻¹ • T (b i)))
        else 0)
      (T x) := by
  classical
  have hrec := (b.hasSum_repr x).mapL T
  convert hrec using 1
  funext i
  have hterm :
      (if 0 < mu i then
          (inner ℝ (b i) x) •
            (Real.sqrt (mu i) •
              ((Real.sqrt (mu i))⁻¹ • T (b i)))
       else 0) =
      (inner ℝ (b i) x) • T (b i) := by
    by_cases hi : 0 < mu i
    · simp only [if_pos hi, smul_smul]
      rw [mul_inv_cancel₀ (Real.sqrt_pos.2 hi).ne', mul_one]
    · have hzero : T (b i) = 0 :=
        realGram_nonpositiveEigenfamily_in_kernel_v007
          T b mu hmu heig i hi
      simp only [if_neg hi, hzero, smul_zero]
  simpa only [HilbertBasis.repr_apply_apply, map_smul] using hterm

/-- Each zero eigenmode in a supplied complete Gram eigenbasis lies
in the kernel of the actual operator, not just in the Gram kernel. -/
theorem realGram_fullEigenbasis_zero_mode_vanishes
    (T : H →L[ℝ] H) (b : HilbertBasis ι ℝ H)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i)
    (i : ι) (hi : ¬ 0 < mu i) :
    T (b i) = 0 :=
  realGram_nonpositiveEigenfamily_in_kernel_v007
    T b mu hmu heig i hi

#print axioms GegenbauerFock.Ultraspherical.realGram_fullEigenbasis_active_singular_hasSum
#print axioms GegenbauerFock.Ultraspherical.realGram_fullEigenbasis_zero_mode_vanishes

end GegenbauerFock.Ultraspherical
