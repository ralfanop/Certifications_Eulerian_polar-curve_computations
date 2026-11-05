import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure

/-!
# V007 — exact canonical Sturm graph from Gegenbauer Fourier coefficients

The exact diagonal-domain theorem has a particularly useful consequence
for identifying the generator of the genuine heat semigroup:

If f,g belong to the actual weighted real L² space and
  <g,e_n> = -n(n+2 lambda) <f,e_n>
for every degree, then f belongs to the domain of the actual
polynomial Sturm graph closure AND its closed operator sends f to g.

The crucial point is that the candidate weighted coefficient sequence
is already an ℓ² vector: the negative Hilbert coefficients of g.
This avoids asserting any abstract spectral extension and provides the
reverse generator-domain inclusion once the heat derivative coordinates
have been established.

This is a standalone proof obligation. The full time-zero derivative
limit for arbitrary closed-domain inputs is separate.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact graph-membership criterion for the CANONICAL closed Sturm
operator, using the already-certified full Gegenbauer Hilbert basis. -/
theorem sturmRealClosed_graph_of_diagonal_coefficients
    (lam : ℝ) (hlam : 0 < lam) (f g : SturmH lam)
    (hcoeff : ∀ n : ℕ,
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g n =
        (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
          (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) = f ∧
        (sturmRealPartialOperator lam hlam).closure x = g := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hdom :
      f ∈ ((sturmRealPartialOperator lam hlam).closure.domain :
        Set (SturmH lam)) := by
    rw [sturmRealClosed_domain_eq_monicHilbert_unshiftedL2 lam hlam]
    change ∃ a : lp (fun _ : ℕ => ℝ) 2, ∀ n : ℕ,
      a n = ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr f) n
    refine ⟨-(b.repr g), ?_⟩
    intro n
    change -((b.repr g) n) =
      ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr f) n
    rw [hcoeff n]
    ring
  refine ⟨⟨f, hdom⟩, rfl, ?_⟩
  apply b.repr.injective
  ext n
  change (b.repr ((sturmRealPartialOperator lam hlam).closure
      ⟨f, hdom⟩)) n = (b.repr g) n
  rw [sturmRealClosed_monicHilbert_diagonal_action
    lam 1 hlam (by norm_num) ⟨f, hdom⟩ n]
  exact (hcoeff n).symm

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_graph_of_diagonal_coefficients

end GegenbauerFock.Ultraspherical
