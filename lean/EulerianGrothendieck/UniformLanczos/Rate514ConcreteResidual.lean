import UniformLanczos.Rate514ConcreteBridge

/-!
# M12 Theorem 5.14: the *actual* residual identity

This file eliminates a second abstract gap in the proof of (160).
The exact residual R_k(u) = [f(J(u))]_{k,k-1} - k/(M u_k) is represented
by an external entry functional `F`; published Duhamel/Fourier calculus
supplies the entrywise derivative identity for `F`, without any requirement
to reprove classical functional calculus.

Given only the entrywise derivative formula F(a)-F(tilde b)=B*d,
Lean derives the *full* residual identity
R(a)-R(tilde b)=B*d+μ*d with μ_k=k/(M a_k tilde_b_k),
for the ACTUAL M12 bond sequences a, tilde b from Rate514ConcreteBridge.

No rate, residual smallness or target conclusion is assumed in this theorem.
-/

namespace UniformLanczos.Rate514ConcreteResidual

open Finset UniformLanczos.Rate514ConcreteBridge
open UniformLanczos.Rate514Assembly

/-- The manuscript's original residual, parameterised only by the
spectral functional-calculus entry `F(u)_k`. -/
noncomputable def residual (F : (ℤ → ℝ) → ℤ → ℝ) (M : ℕ)
    (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  F u k - (k : ℝ) / ((M : ℝ) * u k)

/-- The literal positive reciprocal-difference coefficient of §5.8. -/
noncomputable def actualMu (M : ℕ) (j : ℤ) (L : ℕ) (k : ℤ) : ℝ :=
  (k : ℝ) / ((M : ℝ) * actualBond M k * hybridBond M j L k)

/-- Exact residual difference for the actual a and hybrid tilde b,
using only the published spectral-calculus derivative relation as input.
The critical μ d term is NOT assumed. -/
theorem residual_difference_actual {M : ℕ} (hM : 0 < M)
    (j : ℤ) (L : ℕ)
    (F : (ℤ → ℝ) → ℤ → ℝ) (B : ℤ → ℤ → ℝ)
    (ha : ∀ k ∈ Finset.Icc (j - L) (j + L), actualBond M k ≠ 0)
    (hb : ∀ k ∈ Finset.Icc (j - L) (j + L), hybridBond M j L k ≠ 0)
    (hF : ∀ k ∈ Finset.Icc (j - L) (j + L),
      F (actualBond M) k - F (hybridBond M j L) k =
      ∑ m ∈ Finset.Icc (j - L) (j + L),
        B k m * actualDifference M j L m) :
    ∀ k ∈ Finset.Icc (j - L) (j + L),
      residual F M (actualBond M) k -
          residual F M (hybridBond M j L) k =
        ∑ m ∈ Finset.Icc (j - L) (j + L),
          B k m * actualDifference M j L m +
            actualMu M j L k * actualDifference M j L k := by
  intro k hk
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  change (F (actualBond M) k - (k : ℝ) / ((M : ℝ) * actualBond M k)) -
      (F (hybridBond M j L) k -
        (k : ℝ) / ((M : ℝ) * hybridBond M j L k)) =
      (∑ m ∈ Finset.Icc (j - L) (j + L),
        B k m * actualDifference M j L m) +
      (k : ℝ) / ((M : ℝ) * actualBond M k * hybridBond M j L k) *
          (actualBond M k - hybridBond M j L k)
  exact Rate514Assembly.residual_difference hMr (ha k hk) (hb k hk)
    (hF k hk)

/-- The uniform positivity of μ is obtained from the actual
denominator bonds, by the already verified `mu_lower` theorem. -/
theorem actualMu_lower {M : ℕ} (hM : 0 < M)
    (j : ℤ) (L : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hk : ∀ k ∈ Finset.Icc (j - L) (j + L),
      t ≤ (k : ℝ) / (M : ℝ))
    (ha : ∀ k ∈ Finset.Icc (j - L) (j + L),
      0 < actualBond M k ∧ actualBond M k ≤ 1 / 2)
    (hb : ∀ k ∈ Finset.Icc (j - L) (j + L),
      0 < hybridBond M j L k ∧ hybridBond M j L k ≤ 1 / 2) :
    ∀ k ∈ Finset.Icc (j - L) (j + L),
      4 * t ≤ actualMu M j L k := by
  intro k hmem
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  exact Rate514Assembly.mu_lower hMr
    (ha k hmem).1 (ha k hmem).2
    (hb k hmem).1 (hb k hmem).2
    ht (hk k hmem)

end UniformLanczos.Rate514ConcreteResidual

#print axioms UniformLanczos.Rate514ConcreteResidual.residual_difference_actual
#print axioms UniformLanczos.Rate514ConcreteResidual.actualMu_lower
