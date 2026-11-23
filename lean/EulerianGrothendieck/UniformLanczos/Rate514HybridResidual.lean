import UniformLanczos.Rate514FrechetPath
import UniformLanczos.Rate514Residual
import Mathlib

/-!
# M12 §5.8: actual hybrid residual bound from the two endpoint bounds

The input consists of the original already formalized bounds (163) on
R(a), R(b) and the *published* Jacobi locality inequality for f(J).
This file derives the original hybrid bound (164) with exponent 3 for
R(a)-R(tilde_b), for the actual betaM, Profile.xi and window hybrid.

In particular, the hybrid bound is a conclusion, not an assumed
hypothesis; the difference between b and tilde_b vanishes on W and
Rate514Assembly.hybrid_tail supplies the off-window decay.
-/

namespace UniformLanczos.Rate514HybridResidual

open Finset UniformLanczos.Rate514
open UniformLanczos.Rate514Assembly
open UniformLanczos.Rate514ConcreteBridge
open UniformLanczos.Rate514ConcreteResidual

/-- On W the hybrid profile bond coincides with the actual limiting
profile. -/
theorem hybrid_on_window (M : ℕ) (j : ℤ) (L : ℕ) (k : ℤ)
    (hk : k ∈ Finset.Icc (j - L) (j + L)) :
    hybridBond M j L k = profileBond M k := by
  simp [hybridBond, hk]

/-- The published locality estimate (153) and the two original residual
bounds (163) imply the *actual hybrid residual bound* (164), with exponent
3. The only uniform inputs are C_a, C_b, C_f and the classical locality
inequality: no hybrid estimate or target central gap is assumed. -/
theorem actual_hybrid_residual_bound
    (M : ℕ) (hM : 0 < M) (j : ℤ) (L : ℕ)
    (F : (ℤ → ℝ) → ℤ → ℝ)
    {Ca Cb Cf : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf)
    (hActualBound : ∀ m : ℤ, 0 ≤ actualBond M m ∧ actualBond M m ≤ 1 / 2)
    (hProfileBound : ∀ m : ℤ, 0 ≤ profileBond M m ∧ profileBond M m ≤ 1 / 2)
    (hRa : ∀ k ∈ Finset.Icc (j - L) (j + L),
      |residual F M (actualBond M) k| ≤ Ca / (M : ℝ))
    (hRb : ∀ k ∈ Finset.Icc (j - L) (j + L),
      |residual F M (profileBond M) k| ≤ Cb / (M : ℝ))
    (hLocality : ∀ k ∈ Finset.Icc (j - L) (j + L),
      |F (profileBond M) k - F (hybridBond M j L) k| ≤
        ∑' m : ℤ,
          |profileBond M m - hybridBond M j L m| *
            (Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹))
    (hSummable : ∀ k ∈ Finset.Icc (j - L) (j + L),
      Summable fun m : ℤ =>
        |profileBond M m - hybridBond M j L m| *
          (Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹)) :
    ∀ k ∈ Finset.Icc (j - L) (j + L),
      |residual F M (actualBond M) k -
        residual F M (hybridBond M j L) k| ≤
        (Ca + Cb + Cf * Z2) *
          (1 / (M : ℝ) +
            ((1 + Rate514.Dist L j k) ^ 3)⁻¹) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hZ : 0 ≤ Z2 :=
    tsum_nonneg fun n => inv_nonneg.mpr (pow_nonneg (by positivity) _)
  have hHybridBound : ∀ m : ℤ,
      0 ≤ hybridBond M j L m ∧ hybridBond M j L m ≤ 1 / 2 := by
    intro m
    by_cases hm : m ∈ Finset.Icc (j - L) (j + L)
    · simpa only [hybridBond, if_pos hm] using hProfileBound m
    · simpa only [hybridBond, if_neg hm] using hActualBound m
  have hCzero : ∀ m ∈ Finset.Icc (j - L) (j + L),
      profileBond M m - hybridBond M j L m = 0 := by
    intro m hm
    rw [hybrid_on_window M j L m hm]
    ring
  have hCbound : ∀ m : ℤ,
      |profileBond M m - hybridBond M j L m| ≤ 1 := by
    intro m
    have hp := hProfileBound m
    have hh := hHybridBound m
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  intro k hk
  let A : ℝ := residual F M (actualBond M) k
  let B : ℝ := residual F M (profileBond M) k
  let G : ℝ := F (profileBond M) k - F (hybridBond M j L) k
  let T : ℝ := ((1 + Rate514.Dist L j k) ^ 3)⁻¹
  have hT : 0 ≤ T := by
    have hD := dist_ge_one j L hk
    dsimp [T]
    positivity
  have hHybrid : |G| ≤ Cf * Z2 * T := by
    have hconv := hybrid_tail j L hk
      (fun m : ℤ => profileBond M m - hybridBond M j L m)
      hCf hCzero hCbound (hSummable k hk)
    exact (hLocality k hk).trans hconv
  have hResDecomp :
      residual F M (actualBond M) k -
          residual F M (hybridBond M j L) k =
        (A - B) + G := by
    have hb := hybrid_on_window M j L k hk
    simp only [A, B, G, Rate514ConcreteResidual.residual]
    rw [hb]
    ring
  have htri : |A - B| ≤ |A| + |B| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le A (-B)
  have hAbs :
      |residual F M (actualBond M) k -
          residual F M (hybridBond M j L) k| ≤
        |A| + |B| + |G| := by
    rw [hResDecomp]
    exact (abs_add_le (A - B) G).trans (add_le_add_right htri _)
  have hAB : |A| ≤ Ca / (M : ℝ) := hRa k hk
  have hBB : |B| ≤ Cb / (M : ℝ) := hRb k hk
  have hSimple :
      |residual F M (actualBond M) k -
        residual F M (hybridBond M j L) k| ≤
        (Ca + Cb) / (M : ℝ) + Cf * Z2 * T := by
    calc
      _ ≤ |A| + |B| + |G| := hAbs
      _ ≤ Ca / (M : ℝ) + Cb / (M : ℝ) + Cf * Z2 * T := by
        linarith [hAB, hBB, hHybrid]
      _ = (Ca + Cb) / (M : ℝ) + Cf * Z2 * T := by rw [add_div]
  have hCross1 : 0 ≤ (Ca + Cb) * T :=
    mul_nonneg (add_nonneg hCa hCb) hT
  have hCross2 : 0 ≤ Cf * Z2 / (M : ℝ) :=
    div_nonneg (mul_nonneg hCf hZ) hMreal.le
  calc
    |residual F M (actualBond M) k -
        residual F M (hybridBond M j L) k|
      ≤ (Ca + Cb) / (M : ℝ) + Cf * Z2 * T := hSimple
    _ ≤ (Ca + Cb + Cf * Z2) * (1 / (M : ℝ) + T) := by
      calc
        (Ca + Cb) / (M : ℝ) + Cf * Z2 * T
          ≤ (Ca + Cb) / (M : ℝ) + Cf * Z2 * T +
              ((Ca + Cb) * T + Cf * Z2 / (M : ℝ)) := by
            linarith [hCross1, hCross2]
        _ = (Ca + Cb + Cf * Z2) * (1 / (M : ℝ) + T) := by ring
    _ = (Ca + Cb + Cf * Z2) *
        (1 / (M : ℝ) +
          ((1 + Rate514.Dist L j k) ^ 3)⁻¹) := rfl

end UniformLanczos.Rate514HybridResidual

#print axioms UniformLanczos.Rate514HybridResidual.hybrid_on_window
#print axioms UniformLanczos.Rate514HybridResidual.actual_hybrid_residual_bound
