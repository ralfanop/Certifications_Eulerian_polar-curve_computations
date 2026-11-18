import Manuscript16.V166CompactTransfer

/-! M16 v16.6 Section 13. Operator approximation characterization of Schatten
classes (positive real exponents). The finite-rank approximation formulation
is equivalent to the usual Hilbert-space singular-value definition by the
singular-value min-max principle; that equivalence is not an imported axiom.
This file proves the ideal property directly using bounded finite-dimensional
factorizations. No physical spectral realization is assumed silently. -/
namespace Manuscript16.V166SchattenIdeal

open Manuscript16.V165GraphNeumann
open Manuscript16.V166CompactTransfer

variable {H J K D P X : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup J] [NormedSpace ℂ J]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- An approximation factoring through dimension n (rank at most n). -/
def RankApprox (T : H →L[ℂ] J) (n : ℕ) (e : ℝ) : Prop :=
  ∃ F : H →L[ℂ] (Fin n → ℂ), ∃ G : (Fin n → ℂ) →L[ℂ] J,
    ‖T - G.comp F‖ ≤ e

/-- A summable p-power envelope of actual finite-rank approximation errors.
On Hilbert spaces this characterizes S_p for p>0. -/
def ApproxSchatten (p : ℝ) (T : H →L[ℂ] J) : Prop :=
  0 < p ∧ ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧
    Summable (fun n => a n ^ p) ∧ ∀ n, RankApprox T n (a n)

theorem rankApprox_comp_right (T : H →L[ℂ] J) (C : K →L[ℂ] H)
    (n : ℕ) (e : ℝ) (h : RankApprox T n e) :
    RankApprox (T.comp C) n (e * ‖C‖) := by
  obtain ⟨F,G,hFG⟩ := h
  refine ⟨F.comp C,G,?_⟩
  have heq : T.comp C - G.comp (F.comp C) = (T - G.comp F).comp C := by
    ext x
    rfl
  rw [heq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hFG (norm_nonneg C))

theorem rankApprox_comp_left (T : H →L[ℂ] J) (B : J →L[ℂ] K)
    (n : ℕ) (e : ℝ) (h : RankApprox T n e) :
    RankApprox (B.comp T) n (‖B‖ * e) := by
  obtain ⟨F,G,hFG⟩ := h
  refine ⟨F,B.comp G,?_⟩
  have heq : B.comp T - (B.comp G).comp F = B.comp (T - G.comp F) := by
    ext x
    simp
  rw [heq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left hFG (norm_nonneg B))

theorem approxSchatten_comp_right {p : ℝ} (T : H →L[ℂ] J)
    (C : K →L[ℂ] H) (h : ApproxSchatten p T) :
    ApproxSchatten p (T.comp C) := by
  obtain ⟨hp,a,ha,hs,hA⟩ := h
  refine ⟨hp,fun n => a n * ‖C‖,fun n => mul_nonneg (ha n) (norm_nonneg C),?_,?_⟩
  · simpa only [Real.mul_rpow (ha _) (norm_nonneg C)] using hs.mul_right (‖C‖ ^ p)
  · intro n
    exact rankApprox_comp_right T C n (a n) (hA n)

theorem approxSchatten_comp_left {p : ℝ} (T : H →L[ℂ] J)
    (B : J →L[ℂ] K) (h : ApproxSchatten p T) :
    ApproxSchatten p (B.comp T) := by
  obtain ⟨hp,a,ha,hs,hA⟩ := h
  refine ⟨hp,fun n => ‖B‖ * a n,fun n => mul_nonneg (norm_nonneg B) (ha n),?_,?_⟩
  · simpa only [Real.mul_rpow (norm_nonneg B) (ha _)] using hs.mul_left (‖B‖ ^ p)
  · intro n
    exact rankApprox_comp_left T B n (a n) (hA n)

/-- If s is an attained optimal approximation-error sequence, membership is
exactly summability of its p-th powers. The lower bound quantifies over every
factorization, not simply over a chosen sequence of cutoffs. -/
theorem approxSchatten_iff_optimal {p : ℝ} (hp : 0 < p)
    (T : H →L[ℂ] J) (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n)
    (hupper : ∀ n, RankApprox T n (s n))
    (hlower : ∀ n e, RankApprox T n e → s n ≤ e) :
    ApproxSchatten p T ↔ Summable (fun n => s n ^ p) := by
  constructor
  · rintro ⟨_,a,ha,haSum,hA⟩
    apply Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (hs n) p) _ haSum
    intro n
    exact Real.rpow_le_rpow (hs n) (hlower n (a n) (hA n)) hp.le
  · intro h
    exact ⟨hp,s,hs,h,hupper⟩

theorem ambientInverse_approxSchatten_iff {p : ℝ}
    (j : D →L[ℂ] X) (L₀ : D ≃L[ℂ] X) (U : X ≃L[ℂ] X) :
    ApproxSchatten p (ambientInverse j (L₀.trans U)) ↔
      ApproxSchatten p (ambientInverse j L₀) := by
  constructor
  · intro h
    rw [ambientInverse_trans_cancel j L₀ U]
    exact approxSchatten_comp_right _ _ h
  · intro h
    rw [ambientInverse_trans]
    exact approxSchatten_comp_right _ _ h

theorem perturbed_inverse_approxSchatten_iff [CompleteSpace X] {p : ℝ}
    (j : D →L[ℂ] X) (L₀ : D ≃L[ℂ] X) (E : X →L[ℂ] X)
    (hG : ‖ambientInverse j L₀‖ ≤ (2 : ℝ)/3) (hE : ‖E‖ < (3 : ℝ)/2) :
    ApproxSchatten p (ambientInverse j (perturbedEquiv j L₀ E hG hE)) ↔
      ApproxSchatten p (ambientInverse j L₀) := by
  unfold perturbedEquiv
  apply ambientInverse_approxSchatten_iff

theorem correction_approxSchatten {p : ℝ}
    (j : D →L[ℂ] X) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (L : D ≃L[ℂ] X) (h : ApproxSchatten p (ambientInverse j L)) :
    ApproxSchatten p (correction j B C L) :=
  approxSchatten_comp_left _ B (approxSchatten_comp_right _ C h)

/-- Actual resonant correction in S4 in the approximation characterization,
provided the reference inverse has the fourth-power approximation envelope. -/
theorem resonant_correction_four [CompleteSpace X]
    (j : D →L[ℂ] X) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (L₀ : D ≃L[ℂ] X) (E : X →L[ℂ] X)
    (hG : ‖ambientInverse j L₀‖ ≤ (2 : ℝ)/3) (hE : ‖E‖ < (3 : ℝ)/2)
    (h : ApproxSchatten 4 (ambientInverse j L₀)) :
    ApproxSchatten 4 (correction j B C (perturbedEquiv j L₀ E hG hE)) :=
  correction_approxSchatten j B C _
    ((perturbed_inverse_approxSchatten_iff j L₀ E hG hE).2 h)

#print axioms rankApprox_comp_right
#print axioms rankApprox_comp_left
#print axioms approxSchatten_comp_right
#print axioms approxSchatten_comp_left
#print axioms approxSchatten_iff_optimal
#print axioms ambientInverse_approxSchatten_iff
#print axioms perturbed_inverse_approxSchatten_iff
#print axioms correction_approxSchatten
#print axioms resonant_correction_four
end Manuscript16.V166SchattenIdeal
