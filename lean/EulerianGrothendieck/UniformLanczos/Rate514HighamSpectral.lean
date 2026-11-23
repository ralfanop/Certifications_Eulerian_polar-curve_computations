import UniformLanczos.Rate514AveragedKernel
import Mathlib

/-!
# Manuscript 12, Theorem 5.14: the ACTUAL finite spectral bond kernel is PSD

Higham, *Functions of Matrices*, SIAM (2008), Theorem 3.11 and
Corollary 3.12, give the Daleckii–Krein derivative of a function
of a real self-adjoint matrix in its eigenbasis.

If U is the finite-compression Jacobi eigenvector matrix (extended by zero
outside the compressed sites), the bond direction
E_m = e_m e_(m-1)^T + e_(m-1) e_m^T has eigenbasis entries

    A(m,r,s) = U(m,r) U(m-1,s) + U(m-1,r) U(m,s).

Consequently, for the actual M12 bond derivative kernel,

    K(k,m) = 1/2 * sum_(r,s) f^[1](lambda_r,lambda_s)
                        * A(k,r,s) * A(m,r,s).

This file proves: (i) scalar monotonicity of f + f' >= 0 on [-1,1]
makes all divided differences nonnegative, (ii) this explicit FINITE
Jacobi bond kernel is symmetric and PSD on ANY finite bond window W,
uniformly in matrix dimension and without any operator-monotonicity
assumption, and (iii) the quadratic trace expression is a sum of squares.

The identification of U and lambda with the spectral decomposition of
a particular finite compression J(u), the finite-to-bilateral limit, and
the uniform off-diagonal Fourier/Duhamel bound remain separate interfaces.
No general PSD property is assumed of K; only scalar monotonicity and the
finite spectral data in Higham's formula are used.
-/

namespace UniformLanczos.Rate514HighamSpectral

open Finset Set

/-- Divided difference used by the self-adjoint Daleckii–Krein formula. -/
noncomputable def dividedDifference (f fp : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x = y then fp x else (f x - f y) / (x - y)

/-- Scalar monotonicity (not operator monotonicity) gives a positive
divided difference on the Jacobi spectral interval. -/
theorem dividedDifference_nonneg (f fp : ℝ → ℝ)
    (hmono : MonotoneOn f (Icc (-1 : ℝ) 1))
    (hfp : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ fp x)
    {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hy : y ∈ Icc (-1 : ℝ) 1) :
    0 ≤ dividedDifference f fp x y := by
  unfold dividedDifference
  split_ifs with hxy
  · exact hfp x hx
  · by_cases hle : x ≤ y
    · have hfxy : f x ≤ f y := hmono hx hy hle
      exact div_nonneg_of_nonpos (sub_nonpos.mpr hfxy)
        (sub_nonpos.mpr hle)
    · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hle)
      have hfyx : f y ≤ f x := hmono hy hx hyx
      exact div_nonneg (sub_nonneg.mpr hfyx)
        (sub_nonneg.mpr hyx)

/-- E_m in a finite orthonormal Jacobi eigenbasis. -/
def bondSpectralAmplitude {n : ℕ} (U : ℤ → Fin n → ℝ)
    (m : ℤ) (r s : Fin n) : ℝ :=
  U m r * U (m - 1) s + U (m - 1) r * U m s

/-- The literal bond-index kernel from Higham 3.11, with factor 1/2:
the trace of E_k Df(J)[E_m] is twice the off-diagonal entry B_{km}. -/
noncomputable def spectralBondKernel (n : ℕ) (U : ℤ → Fin n → ℝ)
    (lambda : Fin n → ℝ) (f fp : ℝ → ℝ) (k m : ℤ) : ℝ :=
  ∑ z : Fin n × Fin n,
    (1 / 2 : ℝ) * dividedDifference f fp (lambda z.1) (lambda z.2) *
      bondSpectralAmplitude U k z.1 z.2 *
      bondSpectralAmplitude U m z.1 z.2

theorem spectralBondKernel_symmetric (n : ℕ)
    (U : ℤ → Fin n → ℝ) (lambda : Fin n → ℝ)
    (f fp : ℝ → ℝ) (k m : ℤ) :
    spectralBondKernel n U lambda f fp k m =
      spectralBondKernel n U lambda f fp m k := by
  unfold spectralBondKernel
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- A single fixed real rank-one bond direction has nonnegative
quadratic form on any finite bond window. -/
private theorem rankOneBondQuadratic (W : Finset ℤ)
    (v x : ℤ → ℝ) (c : ℝ) :
    (∑ k ∈ W, ∑ m ∈ W, (c * v k * v m) * x k * x m) =
      c * (∑ k ∈ W, v k * x k) ^ 2 := by
  calc
    _ = ∑ k ∈ W, ∑ m ∈ W,
          (c * (v k * x k)) * (v m * x m) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = (∑ k ∈ W, c * (v k * x k)) *
          (∑ m ∈ W, v m * x m) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ = c * (∑ k ∈ W, v k * x k) ^ 2 := by
      have hsum : (∑ k ∈ W, c * (v k * x k)) =
          c * (∑ k ∈ W, v k * x k) := by
        rw [Finset.mul_sum]
      rw [hsum, pow_two]
      ring

/-- The actual finite spectral bond kernel has a positive quadratic
form for every real finitely supported bond perturbation. The estimate
is UNIFORM in n: no bound depends on the compression dimension. -/
theorem spectralBondKernel_psd (n : ℕ)
    (U : ℤ → Fin n → ℝ) (lambda : Fin n → ℝ)
    (f fp : ℝ → ℝ)
    (hlambda : ∀ r : Fin n, lambda r ∈ Icc (-1 : ℝ) 1)
    (hmono : MonotoneOn f (Icc (-1 : ℝ) 1))
    (hfp : ∀ t ∈ Icc (-1 : ℝ) 1, 0 ≤ fp t)
    (W : Finset ℤ) (x : ℤ → ℝ) :
    0 ≤ ∑ k ∈ W, ∑ m ∈ W,
      spectralBondKernel n U lambda f fp k m * x k * x m := by
  let S : Finset (Fin n × Fin n) := Finset.univ
  let c : Fin n × Fin n → ℝ :=
    fun z => (1 / 2 : ℝ) * dividedDifference f fp (lambda z.1) (lambda z.2)
  let v : ℤ → Fin n × Fin n → ℝ :=
    fun m z => bondSpectralAmplitude U m z.1 z.2
  have hc : ∀ z : Fin n × Fin n, 0 ≤ c z := by
    intro z
    dsimp [c]
    exact mul_nonneg (by norm_num)
      (dividedDifference_nonneg f fp hmono hfp (hlambda z.1) (hlambda z.2))
  change 0 ≤ ∑ k ∈ W, ∑ m ∈ W,
    (∑ z ∈ S, c z * v k z * v m z) * x k * x m
  have hswap :
      (∑ k ∈ W, ∑ m ∈ W,
        (∑ z ∈ S, c z * v k z * v m z) * x k * x m) =
      ∑ z ∈ S, ∑ k ∈ W, ∑ m ∈ W,
        (c z * v k z * v m z) * x k * x m := by
    calc
      _ = ∑ k ∈ W, ∑ m ∈ W, ∑ z ∈ S,
            (c z * v k z * v m z) * x k * x m := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.sum_mul, Finset.sum_mul]
      _ = ∑ k ∈ W, ∑ z ∈ S, ∑ m ∈ W,
            (c z * v k z * v m z) * x k * x m := by
        apply Finset.sum_congr rfl
        intro k hk
        exact Finset.sum_comm
      _ = ∑ z ∈ S, ∑ k ∈ W, ∑ m ∈ W,
            (c z * v k z * v m z) * x k * x m := by
        exact Finset.sum_comm
  rw [hswap]
  apply Finset.sum_nonneg
  intro z hz
  rw [rankOneBondQuadratic W (fun k => v k z) x (c z)]
  exact mul_nonneg (hc z) (sq_nonneg _)

end UniformLanczos.Rate514HighamSpectral

#print axioms UniformLanczos.Rate514HighamSpectral.dividedDifference_nonneg
#print axioms UniformLanczos.Rate514HighamSpectral.spectralBondKernel_symmetric
#print axioms UniformLanczos.Rate514HighamSpectral.spectralBondKernel_psd
