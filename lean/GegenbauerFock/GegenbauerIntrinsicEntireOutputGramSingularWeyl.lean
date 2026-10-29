import GegenbauerFock.GegenbauerIntrinsicEntireOutputGram
import GegenbauerFock.TwoSidedGramSingularWeylZero

/-!
# V007 — genuine holomorphic Gaussian Fock output singular Weyl sequence

The coefficient-output Gram C C† has a certified norm-one,
weakly null approximate-zero singular Weyl sequence. The independently
certified onto Bargmann–Fock linear isometry U maps that sequence to
the actual complete intrinsic entire Gaussian L² Hilbert space.
Pointwise conjugacy H_hol U = U H, complex inner preservation and
strong continuity give a *genuine* holomorphic-output Weyl sequence,
without using finite Gram truncations.

The complete space typeclass is not assumed in the theorem statement:
the conditions are spelled out directly as norm/strong/weak limits.
-/

noncomputable section
open MeasureTheory Filter
open scoped InnerProduct

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- There are unit vectors in the true intrinsic holomorphic Gaussian
L² output space whose Gram images converge strongly to zero, while
the vectors converge weakly to zero against ALL holomorphic Hilbert
test vectors. Thus the actual Fock output Gram has a singular Weyl
sequence at zero, rather than only a coefficient-space witness. -/
theorem C_intrinsicEntire_outputGram_singular_weyl_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → GaussianArea.entireGaussianL2Submodule alpha,
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ =>
        C_intrinsicEntire_outputGram lam alpha hlam ha (u n))
        atTop (nhds (0 : GaussianArea.entireGaussianL2Submodule alpha)) ∧
      (∀ F : GaussianArea.entireGaussianL2Submodule alpha,
        Tendsto (fun n : ℕ => inner ℂ F (u n))
          atTop (nhds (0 : ℂ))) := by
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  obtain ⟨v, hv⟩ :=
    outputGram_has_singular_weyl_sequence_at_zero lam alpha hlam ha
  rcases hv with ⟨hunit, hstrong, hweak⟩
  refine ⟨(fun n => U (v n)), ?_, ?_, ?_⟩
  · intro n
    simpa only [U.norm_map] using hunit n
  · have hpoint :
        (fun n : ℕ =>
          C_intrinsicEntire_outputGram lam alpha hlam ha (U (v n))) =
        (fun n : ℕ => U (outputGram lam alpha hlam ha (v n))) := by
      funext n
      rw [C_intrinsicEntire_outputGram_apply, U.symm_apply_apply]
    rw [hpoint]
    have hlim := U.continuous.continuousAt.tendsto.comp hstrong
    simpa only [Function.comp_def, map_zero] using hlim
  · intro F
    have hp (n : ℕ) :
        inner ℂ F (U (v n)) = inner ℂ (U.symm F) (v n) := by
      have h := U.inner_map_map (U.symm F) (v n)
      simpa only [U.apply_symm_apply] using h
    simpa only [hp] using hweak (U.symm F)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_singular_weyl_zero

end GegenbauerFock.GeneralUltrasphericalFock
