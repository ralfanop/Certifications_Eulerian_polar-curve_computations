import GegenbauerFock.UltrasphericalSturmLiouvilleMonicMeanZeroResolventTwoSource
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatSameMeanStability
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitFirstModes

/-!
# V007 — exact sharp same-mean stability for the full Sturm resolvent and heat flow

The resolvent R_t and heat flow H_s act on the genuine weighted real L²
Hilbert space. Equality of the degree-zero Gegenbauer coefficients of two
inputs is enough for the sharp spectral-gap estimates on their difference.

The resolvent same-mean Lipschitz coefficient is exactly
1 / (t + 1 + 2λ). The heat-flow same-mean Lipschitz coefficient is exactly
exp(-s (1 + 2λ)). Their optimality is witnessed by genuine nonzero
Gegenbauer degree-one eigenstates, not by finite-dimensional proxies.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- On full weighted L², the positive Sturm resolvent satisfies the
sharp Lipschitz estimate as soon as the inputs have the SAME mean.
Neither input is individually required to have zero mean. -/
theorem sturmRealPositiveResolventFullCLM_sameMean_twoSource_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f g : SturmH lam)
    (hmean :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 =
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g 0) :
    (t + (1 + 2 * lam)) *
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
        sturmRealPositiveResolventFullCLM lam t hlam ht g‖ ≤
      ‖f - g‖ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hzero : (b.repr (f - g)) 0 = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hmean
  have h := sturmRealPositiveResolventFullCLM_meanZero_sharp_bound
    lam t hlam ht (f - g) hzero
  simpa only [map_sub] using h

/-- No larger prefactor than t+1+2λ is valid uniformly in the
same-mean two-source resolvent inequality. -/
theorem sturmRealPositiveResolventFullCLM_sameMean_twoSource_optimal
    (lam t C : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (hbound :
      ∀ f g : SturmH lam,
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 =
          (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g 0 →
        C * ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
          sturmRealPositiveResolventFullCLM lam t hlam ht g‖ ≤
          ‖f - g‖) :
    C ≤ t + (1 + 2 * lam) := by
  apply sturmRealPositiveResolventFullCLM_meanZero_bound_optimal
    lam t C hlam ht
  intro f hfzero
  have hz :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (0 : SturmH lam) 0 = 0 := by simp
  have h := hbound f 0 (hfzero.trans hz.symm)
  simpa using h

/-- An actual normalized first Gegenbauer mode and the zero input
attain equality in the same-mean heat-flow Lipschitz bound, for
every nonnegative time. -/
theorem sturmRealHeatLimitCLM_same_mean_bound_attained
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) :
    ∃ f g : SturmH lam,
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 =
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g 0 ∧
      f ≠ g ∧
      ‖sturmRealHeatLimitCLM lam hlam s hs f -
        sturmRealHeatLimitCLM lam hlam s hs g‖ =
        Real.exp (-s * (1 + 2 * lam)) * ‖f - g‖ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 1
  let T := sturmRealHeatLimitCLM lam hlam s hs
  have hb1 : b 1 = u := by
    simp only [b, u, sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hu0 : (b.repr u) 0 = 0 := by
    rw [← hb1, HilbertBasis.repr_apply_apply]
    exact b.orthonormal.inner_eq_zero (by decide : (0 : ℕ) ≠ 1)
  have hum : (b.repr u) 0 = (b.repr (0 : SturmH lam)) 0 := by
    simpa using hu0
  have hunorm : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 1
  have hune : u ≠ (0 : SturmH lam) := by
    intro heq
    rw [heq, norm_zero] at hunorm
    norm_num at hunorm
  have hsharp :
      ‖T u - T 0‖ =
        Real.exp (-s * (1 + 2 * lam)) * ‖u - (0 : SturmH lam)‖ := by
    calc
      ‖T u - T 0‖ = ‖T u‖ := by rw [map_zero, sub_zero]
      _ = Real.exp (-s * (1 + 2 * lam)) :=
        sturmRealHeatLimitCLM_first_mode_norm lam hlam s hs
      _ = Real.exp (-s * (1 + 2 * lam)) *
            ‖u - (0 : SturmH lam)‖ := by rw [sub_zero, hunorm, mul_one]
  exact ⟨u, 0, hum, hune, hsharp⟩

/-- The first-gap heat coefficient exp(-s(1+2λ)) is the SMALLEST
uniform Lipschitz factor on equal-mean pairs in the entire L² space. -/
theorem sturmRealHeatLimitCLM_same_mean_lipschitz_optimal
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (C : ℝ)
    (hbound :
      ∀ f g : SturmH lam,
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 =
          (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g 0 →
        ‖sturmRealHeatLimitCLM lam hlam s hs f -
          sturmRealHeatLimitCLM lam hlam s hs g‖ ≤ C * ‖f - g‖) :
    Real.exp (-s * (1 + 2 * lam)) ≤ C := by
  obtain ⟨f, g, hmean, hne, heq⟩ :=
    sturmRealHeatLimitCLM_same_mean_bound_attained lam hlam s hs
  have hh := hbound f g hmean
  rw [heq] at hh
  have hpos : 0 < ‖f - g‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  exact (mul_le_mul_iff_of_pos_right hpos).mp hh

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_sameMean_twoSource_bound
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_sameMean_twoSource_optimal
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_same_mean_bound_attained
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_same_mean_lipschitz_optimal

end GegenbauerFock.Ultraspherical
