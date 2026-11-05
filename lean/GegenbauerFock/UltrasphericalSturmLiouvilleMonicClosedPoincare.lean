import GegenbauerFock.UltrasphericalSturmLiouvilleMonicInfiniteSpectralPoincare
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertUnshiftedDomain

/-!
# V007 — Poincare on the domain of the actual closed ultraspherical Sturm operator

The exact spectral graph theorem, previously kernel-certified, says every
domain vector of the canonical *closed differential* Sturm operator has
square-summable weighted Fourier coefficients w_n c_n, with
w_n = n(n+2λ). The product of this ℓ² vector and the original
ℓ² Fourier vector is absolutely summable by the Hilbert-space
Cauchy--Schwarz theorem (lp.summable_inner).

Thus the infinite spectral Dirichlet energy ∑' w_n c_n² is automatically
summable for every actual domain vector. The sharp infinite Poincare
inequality from the preceding module therefore holds without any
extra energy-summability assumption on closed-domain inputs.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The spectral Dirichlet energy is summable for every domain vector
of the ACTUAL canonical closed weighted real Sturm operator. -/
theorem sturmMonic_realL2_closed_spectral_energy_summable
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    Summable (fun n : ℕ =>
      ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (x : SturmH lam) n) ^ 2) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hmem : (x : SturmH lam) ∈
      ((sturmRealPartialOperator lam hlam).closure.domain : Set (SturmH lam)) :=
    x.property
  have hspec :
      (x : SturmH lam) ∈ sturmMonicHilbertUnshiftedDomain lam hlam := by
    rw [← sturmRealClosed_domain_eq_monicHilbert_unshiftedL2 lam hlam]
    exact hmem
  change ∃ a : lp (fun _ : ℕ => ℝ) 2, ∀ n : ℕ,
      a n = ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        (b.repr (x : SturmH lam)) n at hspec
  obtain ⟨a, ha⟩ := hspec
  have hs :
      Summable (fun n : ℕ =>
        inner ℝ (a n) ((b.repr (x : SturmH lam)) n)) :=
    lp.summable_inner a (b.repr (x : SturmH lam))
  have heq (n : ℕ) :
      inner ℝ (a n) ((b.repr (x : SturmH lam)) n) =
        ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
          ((b.repr (x : SturmH lam)) n) ^ 2 := by
    rw [Real.inner_apply, ha n]
    ring
  exact hs.congr heq

/-- Sharp Poincare estimate on the *true domain* of the canonical
closed real Gegenbauer Sturm operator, for vectors with zero
constant Gegenbauer coefficient. No independent energy hypothesis. -/
theorem sturmMonic_realL2_closed_spectral_poincare
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0) :
    (1 + 2 * lam) * ‖(x : SturmH lam)‖ ^ 2 ≤
      ∑' n : ℕ, ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (x : SturmH lam) n) ^ 2 := by
  exact sturmMonic_realL2_infinite_spectral_poincare lam hlam
    (x : SturmH lam) hzero
    (sturmMonic_realL2_closed_spectral_energy_summable lam hlam x)

#print axioms GegenbauerFock.Ultraspherical.sturmMonic_realL2_closed_spectral_energy_summable
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_realL2_closed_spectral_poincare

end GegenbauerFock.Ultraspherical
