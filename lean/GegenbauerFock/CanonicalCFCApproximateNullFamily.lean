import GegenbauerFock.LocalCFCGramSquareRoot
import GegenbauerFock.FockApproximateNullConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# V007 — approximate zero vectors for the canonical CFC polar square root

The canonical Gram square root already has a full-Hilbert unitary polar
factorization. This file transports the independently certified quantitative
approximate-null vectors for the actual Gegenbauer--Fock transform C
to the CFC Gram square root, preserving the exact norms.

The result is stronger than mere non-surjectivity or nonclosed range:
for every n there is a unit vector whose canonical-root image has norm
smaller than 1/(n+1), and these root images tend strongly to zero.
There is no nonzero kernel vector and no artificial spectral gap.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine CFC Gram square root has normalized approximate
null vectors with the same quantitative decay as the true transform. -/
theorem local_cfc_root_exists_normalized_approximate_null_family
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      ∀ n : ℕ,
        ‖u n‖ = 1 ∧
        ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ <
          1 / ((n : ℝ) + 1) := by
  classical
  obtain ⟨ι, w, mu, W, hpos, hsum, hK, hPu, hC⟩ :=
    exists_local_cfc_sqrt_polar_unitary_kummer lam alpha hlam ha
  obtain ⟨u, h⟩ :=
    C_exists_normalized_approximate_null_family lam alpha hlam ha
  refine ⟨u, ?_⟩
  intro n
  refine ⟨(h n).1, ?_⟩
  have heq :
      ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ =
      ‖C lam alpha hlam ha (u n)‖ := by
    calc
      ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ =
          ‖W (localCFCGramSqrt lam alpha hlam ha (u n))‖ :=
        (W.norm_map _).symm
      _ = ‖C lam alpha hlam ha (u n)‖ :=
        congrArg norm (hC (u n)).symm
  rw [heq]
  exact (h n).2

/-- A unit sequence tends to zero after application of the true
canonical CFC square root, although it never tends to zero in norm. -/
theorem local_cfc_root_exists_normalized_approximate_null_sequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n, ‖u n‖ = 1) ∧
      Tendsto
        (fun n => localCFCGramSqrt lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
  obtain ⟨u, h⟩ :=
    local_cfc_root_exists_normalized_approximate_null_family
      lam alpha hlam ha
  refine ⟨u, (fun n => (h n).1), ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero
    (fun n : ℕ =>
      norm_nonneg (localCFCGramSqrt lam alpha hlam ha (u n)))
    (fun n : ℕ => (h n).2.le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

#print axioms GegenbauerFock.GeneralUltrasphericalFock.local_cfc_root_exists_normalized_approximate_null_family
#print axioms GegenbauerFock.GeneralUltrasphericalFock.local_cfc_root_exists_normalized_approximate_null_sequence

end GegenbauerFock.GeneralUltrasphericalFock
