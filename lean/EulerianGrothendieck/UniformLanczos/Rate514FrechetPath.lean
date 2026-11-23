import UniformLanczos.Rate514AveragedKernel
import Mathlib

/-!
# M12 §5.8: the actual hybrid Jacobi path and finite-dimensional FTC

Unlike a formal algebraic difference, this module constructs the exact path
u(τ) = tilde_b + τ(a-tilde_b) with the actual M12 betaM and Profile.xi
coefficient sequences. The published Duhamel/Frechet calculus gives the
derivative of the entry F(u(τ))_k; we use the fundamental theorem of
calculus to derive (not assume) the finite-window identity
F(a)_k - F(tilde_b)_k = Σ_m B̄_{km} (a_m - tilde_b_m).
Here B̄ is the *integrated* kernel of Rate514AveragedKernel.

The sole nonclassical content formalized here is the path instantiation,
FTC and exact sum/integral interchange. Duhamel's derivative formula itself
is an explicit, published external input; no convergence-rate estimate is
assumed anywhere.
-/

namespace UniformLanczos.Rate514FrechetPath

open Set MeasureTheory intervalIntegral Finset
open UniformLanczos.Rate514ConcreteBridge
open UniformLanczos.Rate514AveragedKernel

/-- The literal affine interpolation from the profile/actual hybrid to
the actual Eulerian betaM coefficient sequence. -/
noncomputable def jacobiPath (M : ℕ) (j : ℤ) (L : ℕ) (τ : ℝ) (m : ℤ) : ℝ :=
  hybridBond M j L m + τ * actualDifference M j L m

theorem jacobiPath_zero (M : ℕ) (j : ℤ) (L : ℕ) :
    jacobiPath M j L 0 = hybridBond M j L := by
  funext m
  simp [jacobiPath]

theorem jacobiPath_one (M : ℕ) (j : ℤ) (L : ℕ) :
    jacobiPath M j L 1 = actualBond M := by
  funext m
  unfold jacobiPath actualDifference
  ring

/-- The integrated Jacobi entry identity, derived from the published
entrywise Frechet derivative formula along the *actual* interpolating
path, and from the ordinary fundamental theorem of calculus in Mathlib. -/
theorem actual_entry_difference_of_frechet_derivative
    (M : ℕ) (j : ℤ) (L : ℕ)
    (F : (ℤ → ℝ) → ℤ → ℝ) (K : ℝ → ℤ → ℤ → ℝ)
    (hCont : ∀ k m : ℤ, Continuous (fun τ : ℝ => K τ k m))
    (hDuhamel : ∀ k ∈ Finset.Icc (j - L) (j + L),
      ∀ τ ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => F (jacobiPath M j L t) k)
          (∑ m ∈ Finset.Icc (j - L) (j + L),
            K τ k m * actualDifference M j L m) τ) :
    ∀ k ∈ Finset.Icc (j - L) (j + L),
      F (actualBond M) k - F (hybridBond M j L) k =
        ∑ m ∈ Finset.Icc (j - L) (j + L),
          averageKernel K k m * actualDifference M j L m := by
  intro k hk
  let W : Finset ℤ := Finset.Icc (j - L) (j + L)
  let d : ℤ → ℝ := actualDifference M j L
  have hTerm (m : ℤ) :
      IntervalIntegrable (fun τ : ℝ => K τ k m * d m) volume (0 : ℝ) 1 := by
    exact ((hCont k m).mul continuous_const).intervalIntegrable 0 1
  have hInt :
      IntervalIntegrable (fun τ : ℝ => ∑ m ∈ W, K τ k m * d m)
        volume (0 : ℝ) 1 := by
    exact IntervalIntegrable.sum W (fun m _ => hTerm m)
  have hFTC :
      (∫ τ in (0 : ℝ)..1, ∑ m ∈ W, K τ k m * d m) =
        F (actualBond M) k - F (hybridBond M j L) k := by
    have hD : ∀ τ ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => F (jacobiPath M j L t) k)
          (∑ m ∈ W, K τ k m * d m) τ := hDuhamel k hk
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hInt
    simpa only [jacobiPath_zero, jacobiPath_one] using h
  rw [← hFTC]
  change (∫ τ in (0 : ℝ)..1, ∑ m ∈ W, K τ k m * d m) =
    ∑ m ∈ W, averageKernel K k m * d m
  rw [intervalIntegral.integral_finset_sum (fun m _ => hTerm m)]
  apply Finset.sum_congr rfl
  intro m hm
  unfold averageKernel
  rw [intervalIntegral.integral_mul_const]

end UniformLanczos.Rate514FrechetPath

#print axioms UniformLanczos.Rate514FrechetPath.jacobiPath_zero
#print axioms UniformLanczos.Rate514FrechetPath.jacobiPath_one
#print axioms UniformLanczos.Rate514FrechetPath.actual_entry_difference_of_frechet_derivative
