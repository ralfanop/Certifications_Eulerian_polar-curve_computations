import GegenbauerFock.GaussianAreaFockCoherentFiniteIndependent
import GegenbauerFock.GaussianAreaIntrinsicRieszStrictGram

/-!
# V007 — strict positive definiteness of every finite intrinsic Gaussian Fock Gram matrix

The coefficient-model Gaussian coherent kernel vectors are linearly independent
at pairwise distinct complex nodes, as certified by the finite complex
Vandermonde argument. The injective coefficient-to-intrinsic isometry carries
this independence to genuine intrinsic Gaussian-L² Bargmann–Fock Riesz
vectors. The exact exponential Gram norm identity then gives strict positivity
for every nonzero coefficient vector, in arbitrary finite dimension.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Finite intrinsic Riesz coherent vectors at pairwise distinct complex
evaluation points have no nontrivial complex linear relation. -/
theorem finiteIntrinsicRieszKernel_zero_coefficients
    (n : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (z c : Fin n → ℂ) (hz : Function.Injective z)
    (hzero : ∑ i : Fin n,
      c i • intrinsicRieszKernel alpha ha (z i) = 0) :
    ∀ i : Fin n, c i = 0 := by
  have hcoeff :
      (∑ i : Fin n,
        c i • FockEvaluation.kernelVector alpha ha (z i)) = 0 := by
    apply (coefficientSynthesisToIntrinsicEntire alpha ha).injective
    simpa only [map_sum, map_smul, map_zero, intrinsicRieszKernel] using hzero
  exact finiteFockCoherentKernel_zero_coefficients n alpha ha z c hz hcoeff

/-- Intrinsic Gaussian Bargmann–Fock Riesz evaluation vectors are
linearly independent for every finite family of distinct nodes. -/
theorem finiteIntrinsicRieszKernel_linearIndependent
    (n : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (z : Fin n → ℂ) (hz : Function.Injective z) :
    LinearIndependent ℂ (fun i : Fin n => intrinsicRieszKernel alpha ha (z i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  exact finiteIntrinsicRieszKernel_zero_coefficients n alpha ha z c hz hc i

/-- The full Gaussian exponential Gram quadratic form has strictly
positive real part at all nonzero complex coefficient vectors, for every
finite family of pairwise distinct nodes. -/
theorem finiteIntrinsicRieszKernel_exp_gram_pos_of_nonzero
    (n : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (z c : Fin n → ℂ) (hz : Function.Injective z)
    (hc : ∃ i : Fin n, c i ≠ 0) :
    0 < Complex.re
      (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) := by
  apply (intrinsicRieszKernel_exp_gram_re_pos_iff
    (Finset.univ : Finset (Fin n)) z c alpha ha).2
  intro hzero
  obtain ⟨i, hci⟩ := hc
  exact hci (finiteIntrinsicRieszKernel_zero_coefficients
    n alpha ha z c hz hzero i)

/-- Equivalence of positive Gaussian exponential Gram energy and
nonzero finite coefficients for pairwise distinct complex nodes. -/
theorem finiteIntrinsicRieszKernel_exp_gram_pos_iff_nonzero
    (n : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (z c : Fin n → ℂ) (hz : Function.Injective z) :
    0 < Complex.re
      (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) ↔
      ∃ i : Fin n, c i ≠ 0 := by
  constructor
  · intro hpos
    by_contra hno
    push_neg at hno
    have hzero : ∑ i : Fin n,
        c i • intrinsicRieszKernel alpha ha (z i) = 0 := by
      simp [hno]
    exact ((intrinsicRieszKernel_exp_gram_re_pos_iff
      (Finset.univ : Finset (Fin n)) z c alpha ha).1 hpos) hzero
  · exact finiteIntrinsicRieszKernel_exp_gram_pos_of_nonzero
      n alpha ha z c hz

#print axioms GegenbauerFock.GaussianArea.finiteIntrinsicRieszKernel_zero_coefficients
#print axioms GegenbauerFock.GaussianArea.finiteIntrinsicRieszKernel_linearIndependent
#print axioms GegenbauerFock.GaussianArea.finiteIntrinsicRieszKernel_exp_gram_pos_of_nonzero
#print axioms GegenbauerFock.GaussianArea.finiteIntrinsicRieszKernel_exp_gram_pos_iff_nonzero

end GegenbauerFock.GaussianArea
