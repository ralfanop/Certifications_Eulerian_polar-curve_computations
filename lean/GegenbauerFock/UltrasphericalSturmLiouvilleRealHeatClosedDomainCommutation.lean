import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure

/-!
# V007 — true heat semigroup invariance of the canonical closed Sturm domain

This theorem acts on the *actual canonical closed differential* Sturm
operator A = closure(L_lambda,0), not on an independent diagonal operator.

For every x in Dom(A) and every s≥0, H_s x again lies in Dom(A).
The exact closed-spectrum identification and the full weighted-L²
diagonal heat coordinate theorem prove the further equality

   A(H_s x) = H_s(A x)

as actual weighted-real-L² vectors. The result does not presuppose an
identification of A with the infinitesimal generator of H.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine full weighted-real-L² heat semigroup preserves the
canonical closed Sturm domain and commutes with its graph action. -/
theorem sturmRealHeatLimitCLM_closed_domain_invariant_commutes
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    ∃ z : (sturmRealPartialOperator lam hlam).closure.domain,
      (z : SturmH lam) =
        sturmRealHeatLimitCLM lam hlam s hs (x : SturmH lam) ∧
      (sturmRealPartialOperator lam hlam).closure z =
        sturmRealHeatLimitCLM lam hlam s hs
          ((sturmRealPartialOperator lam hlam).closure x) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let A := (sturmRealPartialOperator lam hlam).closure
  let T := sturmRealHeatLimitCLM lam hlam s hs
  let y : SturmH lam := T (x : SturmH lam)
  have hdiagAx (n : ℕ) :
      (b.repr (A x)) n =
        (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
          (b.repr (x : SturmH lam)) n :=
    (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
      lam hlam).2 x n
  have hdiagT (v : SturmH lam) (n : ℕ) :
      (b.repr (T v)) n =
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) *
          (b.repr v) n :=
    sturmRealHeatLimitCLM_hilbert_repr_diagonal lam hlam s hs v n
  have hweighted : y ∈ sturmMonicHilbertUnshiftedDomain lam hlam := by
    change ∃ a : lp (fun _ : ℕ => ℝ) 2, ∀ n : ℕ,
      a n = ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr y) n
    refine ⟨-(b.repr (T (A x))), ?_⟩
    intro n
    change -((b.repr (T (A x))) n) =
      ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr y) n
    change -((b.repr (T (A x))) n) =
      ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        (b.repr (T (x : SturmH lam))) n
    rw [hdiagT (A x) n, hdiagAx n, hdiagT (x : SturmH lam) n]
    ring
  have hdomain : y ∈ (A.domain : Set (SturmH lam)) := by
    rw [(sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
      lam hlam).1]
    exact hweighted
  let z : A.domain := ⟨y, hdomain⟩
  refine ⟨z, rfl, ?_⟩
  apply b.repr.injective
  ext n
  change (b.repr (A z)) n = (b.repr (T (A x))) n
  rw [(sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
    lam hlam).2 z n]
  have hz : (z : SturmH lam) = T (x : SturmH lam) := rfl
  rw [hz, hdiagT (x : SturmH lam) n, hdiagT (A x) n, hdiagAx n]
  ring

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_closed_domain_invariant_commutes

end GegenbauerFock.Ultraspherical
