import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Unitary

/-!
# Fourier–Gegenbauer synthesis in the genuine weighted real Hilbert space

The explicitly normalized all-degree Gegenbauer Hilbert basis yields
an isometric coefficient transform onto real ℓ². We now identify
both the forward Fourier expansion of every actual weighted L²
vector and the inverse synthesis of every square-summable coefficient
sequence, with unconditional Hilbert convergence.
These are identities in the actual ultraspherical L², rather than
formal power series or coefficientwise equalities.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev SturmL2Coeffs := lp (fun _ : ℕ => ℝ) 2

/-- Every weighted real L² vector is the unconditionally convergent
Hilbert sum of its exact normalized Gegenbauer Fourier coefficients. -/
theorem sturmMonicEigenCandidate_realL2_fourier_reconstruction
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) :
    HasSum
      (fun n : ℕ =>
        (sturmMonicEigenCandidate_realL2_unitary lam hlam f n) •
          sturmMonicEigenCandidate_realL2_normalized lam hlam n)
      f := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  change HasSum (fun n : ℕ => (b.repr f n) • b n) f
  exact b.hasSum_repr f

/-- Every genuine ℓ² sequence synthesizes uniquely into the
weighted real L² space and is recovered by Fourier analysis. -/
theorem sturmMonicEigenCandidate_realL2_fourier_synthesis
    (lam : ℝ) (hlam : 0 < lam) (a : SturmL2Coeffs) :
    HasSum
      (fun n : ℕ =>
        (a n) • sturmMonicEigenCandidate_realL2_normalized lam hlam n)
      ((sturmMonicEigenCandidate_realL2_unitary lam hlam).symm a) := by
  let F := sturmMonicEigenCandidate_realL2_unitary lam hlam
  have h := sturmMonicEigenCandidate_realL2_fourier_reconstruction
    lam hlam (F.symm a)
  have hcoeff : F (F.symm a) = a := F.apply_symm_apply a
  simpa only [F, hcoeff] using h

/-- The complete Fourier–Gegenbauer transform preserves all L² distances,
not only individual norms. -/
theorem sturmMonicEigenCandidate_realL2_fourier_distance
    (lam : ℝ) (hlam : 0 < lam) (f g : SturmH lam) :
    ‖sturmMonicEigenCandidate_realL2_unitary lam hlam f -
      sturmMonicEigenCandidate_realL2_unitary lam hlam g‖ =
      ‖f - g‖ := by
  let F := sturmMonicEigenCandidate_realL2_unitary lam hlam
  change ‖F f - F g‖ = ‖f - g‖
  rw [← map_sub]
  exact F.norm_map (f - g)

/-- The inverse synthesis from real ℓ² is itself an exact isometry. -/
theorem sturmMonicEigenCandidate_realL2_fourier_inverse_norm
    (lam : ℝ) (hlam : 0 < lam) (a : SturmL2Coeffs) :
    ‖(sturmMonicEigenCandidate_realL2_unitary lam hlam).symm a‖ = ‖a‖ :=
  (sturmMonicEigenCandidate_realL2_unitary lam hlam).symm.norm_map a

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_fourier_reconstruction
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_fourier_synthesis
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_fourier_distance
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_fourier_inverse_norm

end GegenbauerFock.Ultraspherical
