import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertWeightedDomain

/-!
# V007 — CANONICAL unshifted diagonal domain of the real closed Sturm operator

The previously kernel-certified domain identification uses the
positive shifted eigenvalues t+n(n+2λ). Because the Hilbert-basis
Fourier coefficients of EVERY L² vector already belong to ℓ²,
adding or subtracting the identity multiplier does not change
weighted square summability. Taking t=1 proves the EXACT canonical
unshifted spectral domain:

  Dom(closure L₀) =
    {u : H | (n ↦ n(n+2λ) * (b.repr u n)) ∈ ℓ²}.

This is a genuine ℓ² witness formulation, with no extra
resolvent, extension or polynomial-core hypotheses.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Genuine unshifted Gegenbauer diagonal spectral domain,
defined independently of the closed Sturm graph and resolvent. -/
noncomputable def sturmMonicHilbertUnshiftedDomain
    (lam : ℝ) (hlam : 0 < lam) : Set (SturmH lam) :=
  {u | ∃ a : lp (fun _ : ℕ => ℝ) 2, ∀ n : ℕ,
      a n = ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr u n}

/-- The canonical closed Sturm domain is EXACTLY the diagonal
weighted-ℓ² domain with the unshifted Gegenbauer eigenvalue weights. -/
theorem sturmRealClosed_domain_eq_monicHilbert_unshiftedL2
    (lam : ℝ) (hlam : 0 < lam) :
    ((sturmRealPartialOperator lam hlam).closure.domain :
      Set (SturmH lam)) =
    sturmMonicHilbertUnshiftedDomain lam hlam := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  rw [sturmRealClosed_domain_eq_monicHilbert_weightedL2
    lam 1 hlam (by norm_num)]
  ext u
  change (∃ a : lp (fun _ : ℕ => ℝ) 2, ∀ n : ℕ,
    a n = (1 + (n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr u) n) ↔
    (∃ a : lp (fun _ : ℕ => ℝ) 2, ∀ n : ℕ,
    a n = ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr u) n)
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a - b.repr u, ?_⟩
    intro n
    change a n - (b.repr u) n =
      ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr u) n
    rw [ha n]
    ring
  · rintro ⟨a, ha⟩
    refine ⟨a + b.repr u, ?_⟩
    intro n
    change a n + (b.repr u) n =
      (1 + (n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr u) n
    rw [ha n]
    ring

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_domain_eq_monicHilbert_unshiftedL2

end GegenbauerFock.Ultraspherical
