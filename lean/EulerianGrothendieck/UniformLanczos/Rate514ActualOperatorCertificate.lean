import UniformLanczos.Rate514HybridResidual
import UniformLanczos.Rate514AveragedKernel
import UniformLanczos.Rate514FrechetPath
import Mathlib

/-!
# Manuscript 12, Theorem 5.14 — CONSTRUCTION of the actual operator certificate

Previous PR #531 required an abstract LocalOperatorCertificate (Bbar,h,mu).
This file constructs all of its fields for the *actual* Eulerian
betaM/Profile.xi Jacobi bond sequences:
* Bbar_{km} is the real integral over τ∈[0,1] of the actual Frechet kernel;
* symmetry, PSD, and |Bbar|<=Cf(1+|k-m|)^(-5) are DERIVED via PR #533;
* the entry difference comes from the exact actual hybrid path and FTC (#534);
* h=R(a)-R(tilde_b), μ=k/(M a_k tilde_b_k), and their identity come from #532;
* |h|<=Ch(1/M+(1+D)^(-3)) is DERIVED from the original endpoint residual
  bounds (163) and the published functional-calculus locality inequality (#535).

Only the published instantaneous Duhamel/Daleckii-Krein assumptions and
the original endpoint estimates (163) are explicit hypotheses, *not*
the constructed certificate and not the final squared rate. The proof
does NOT yet establish (163) for the concrete orthogonal polynomials:
those original residual estimates have only conditional earlier Lean
bridges and need their exact gM/Freud specialisation.

No new axioms, no sorry, no claim of unconditional closure.
-/

namespace UniformLanczos.Rate514ActualOperatorCertificate

open Finset Set MeasureTheory
open UniformLanczos.Rate514
open UniformLanczos.Rate514ConcreteBridge
open UniformLanczos.Rate514ConcreteResidual
open UniformLanczos.Rate514AveragedKernel
open UniformLanczos.Rate514FrechetPath
open UniformLanczos.Rate514HybridResidual

/-- This is the **published functional-calculus input**, instantiated on
the ACTUAL M12 coefficient path. In contrast to the old
LocalOperatorCertificate, it does NOT contain a positive/decaying
averaged matrix, any residual identity, a hybrid residual estimate, or
any rate conclusion. Those are new conclusions constructed below.

The two separate original (163) estimates are explicit hypotheses
until their concrete gM/Freud and constant-bond proofs are connected. -/
structure PublishedJacobiInput
    (M j L : ℕ) (c t Ca Cb Cf : ℝ) where
  F : (ℤ → ℝ) → ℤ → ℝ
  K : ℝ → ℤ → ℤ → ℝ
  K_continuous : ∀ k m : ℤ, Continuous (fun τ : ℝ => K τ k m)
  K_symmetric : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ k m : ℤ, K τ k m = K τ m k
  K_positive : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ (W : Finset ℤ) (x : ℤ → ℝ),
    0 ≤ ∑ k ∈ W, ∑ m ∈ W, K τ k m * x k * x m
  K_decay : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ k m : ℤ,
    |K τ k m| ≤ Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹
  derivative : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    ∀ τ ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun z : ℝ => F (jacobiPath M (j : ℤ) L z) k)
        (∑ m ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
          K τ k m * actualDifference M (j : ℤ) L m) τ
  actual_bonds : ∀ m : ℤ,
    0 ≤ actualBond M m ∧ actualBond M m ≤ 1 / 2
  profile_bonds : ∀ m : ℤ,
    0 ≤ profileBond M m ∧ profileBond M m ≤ 1 / 2
  actual_strict : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    0 < actualBond M k
  profile_strict : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    0 < profileBond M k
  index_lower : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    t ≤ (k : ℝ) / (M : ℝ)
  width_two : 2 ≤ L
  width_linear : c * (M : ℝ) ≤ (L : ℝ)
  residual_actual : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    |residual F M (actualBond M) k| ≤ Ca / (M : ℝ)
  residual_profile : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    |residual F M (profileBond M) k| ≤ Cb / (M : ℝ)
  locality : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    |F (profileBond M) k - F (hybridBond M (j : ℤ) L) k| ≤
      ∑' m : ℤ, |profileBond M m - hybridBond M (j : ℤ) L m| *
        (Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹)
  locality_summable : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    Summable fun m : ℤ =>
      |profileBond M m - hybridBond M (j : ℤ) L m| *
        (Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹)

/-- The **actual** averaged matrix and actual residual data satisfy
every requirement of #531's LocalOperatorCertificate.

The averaged kernel's symmetry, PSD, decay are *proved*, not supplied;
the residual identity and (164) are *proved*, not supplied.
Only the exact instantaneous classical calculus and the two original
(163) endpoint bounds remain as named inputs. -/
noncomputable def constructActualCertificate
    {M j L : ℕ} (hM : 0 < M)
    {ε c t Ca Cb Cf : ℝ}
    (ht : 0 < t) (hc : 0 < c)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf)
    (data : PublishedJacobiInput M j L c t Ca Cb Cf) :
    LocalOperatorCertificate M j L ε
      (Ca + Cb + Cf * Z2) c (4 * t) Cf := by
  let W : Finset ℤ := Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L)
  let Bbar : ℤ → ℤ → ℝ := averageKernel data.K
  let h : ℤ → ℝ :=
    fun k => residual data.F M (actualBond M) k -
      residual data.F M (hybridBond M (j : ℤ) L) k
  let μ : ℤ → ℝ := actualMu M (j : ℤ) L
  have hMatrix := averageKernel_matrix_certificate
    data.K hCf data.K_continuous data.K_symmetric
    data.K_positive data.K_decay W
  have hEntry := actual_entry_difference_of_frechet_derivative
    M (j : ℤ) L data.F data.K data.K_continuous data.derivative
  have ha : ∀ k ∈ W, actualBond M k ≠ 0 := by
    intro k hk
    exact (data.actual_strict k hk).ne'
  have hb : ∀ k ∈ W, hybridBond M (j : ℤ) L k ≠ 0 := by
    intro k hk
    rw [hybrid_on_window M (j : ℤ) L k hk]
    exact (data.profile_strict k hk).ne'
  have hIdentity := residual_difference_actual hM (j : ℤ) L
    data.F Bbar ha hb hEntry
  have hHybrid : ∀ k ∈ W,
      0 < hybridBond M (j : ℤ) L k ∧
        hybridBond M (j : ℤ) L k ≤ 1 / 2 := by
    intro k hk
    rw [hybrid_on_window M (j : ℤ) L k hk]
    exact ⟨data.profile_strict k hk, (data.profile_bonds k).2⟩
  have hActual : ∀ k ∈ W,
      0 < actualBond M k ∧ actualBond M k ≤ 1 / 2 :=
    fun k hk => ⟨data.actual_strict k hk, (data.actual_bonds k).2⟩
  have hMu := actualMu_lower hM (j : ℤ) L ht.le
    data.index_lower hActual hHybrid
  have hResidual := actual_hybrid_residual_bound
    M hM (j : ℤ) L data.F hCa hCb hCf
    data.actual_bonds data.profile_bonds
    data.residual_actual data.residual_profile
    data.locality data.locality_summable
  exact {
    B := Bbar
    h := h
    μ := μ
    L_two := data.width_two
    L_linear := data.width_linear
    symmetric := hMatrix.1
    positive := hMatrix.2.1
    decay := hMatrix.2.2
    mu_lower := hMu
    residual_identity := hIdentity
    residual_decay := hResidual
  }

/-- The original rate (160), for actual β[M] and ξ, with NO certificate
or squared error premise: the certificate is constructed from the
classical pointwise spectral input + the original (163) endpoint bounds.
This still must not be called unconditional while (163) remains an input. -/
theorem actual_rate_of_published_calculus
    {M j L : ℕ} (hM : 0 < M) (hj : 0 < j)
    {ε c t Ca Cb Cf : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t)
    (hc : 0 < c) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf)
    (hsmall : ε ^ 2 * (Cf * Z3) ≤ 4 * t)
    (hβ : 0 ≤ UniformLanczos.Theorem59.betaM M j)
    (hupper : Real.sqrt (UniformLanczos.Theorem59.betaM M j) / (M : ℝ) ≤ 1 / 2)
    (data : PublishedJacobiInput M j L c t Ca Cb Cf) :
    |UniformLanczos.Theorem59.betaM M j / (M : ℝ) ^ 2 -
      UniformLanczos.Profile.F ((j : ℝ) / (M : ℝ))| ≤
      rateConstant ε (Ca + Cb + Cf * Z2) c (4 * t) / (M : ℝ) ∧
    |Real.sqrt (UniformLanczos.Theorem59.betaM M j) / (M : ℝ) -
      UniformLanczos.Profile.ξ ((j : ℝ) / (M : ℝ)) / 2| ≤
      rateConstant ε (Ca + Cb + Cf * Z2) c (4 * t) / (M : ℝ) := by
  have hmu : 0 < 4 * t := by linarith
  exact actual_rate_from_operator_certificate hM hj
    hε hε1 hc hmu hCf hsmall hβ hupper
    (constructActualCertificate hM ht hc hCa hCb hCf data)

/-- **Uniform** version for the actual M12 coefficients: the same
published constants (c,t,Ca,Cb,Cf,ε) and one M₀ work for all j/M in
the fixed compact interval. The theorem constructs every certificate
instead of assuming hcert as in #531.

Nonclassical remaining obligation: instantiate `PublishedJacobiInput`
from the actual f(J(u)) and the manuscript's proved (163) estimates. -/
theorem compact_uniform_rate_of_published_calculus
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : t₁ ≤ t₂)
    {ε c t Ca Cb Cf : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t)
    (hc : 0 < c) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf)
    (hsmall : ε ^ 2 * (Cf * Z3) ≤ 4 * t)
    (M₀ : ℕ) (hM₀ : 1 ≤ M₀)
    (hβ : ∀ M j : ℕ, M₀ ≤ M →
      (j : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
      0 ≤ UniformLanczos.Theorem59.betaM M j)
    (hupper : ∀ M j : ℕ, M₀ ≤ M →
      (j : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
      Real.sqrt (UniformLanczos.Theorem59.betaM M j) / (M : ℝ) ≤ 1 / 2)
    (hPublished : ∀ M j : ℕ, M₀ ≤ M →
      (j : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
      Σ L : ℕ, PublishedJacobiInput M j L c t Ca Cb Cf) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ j : ℕ,
        (j : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
          |UniformLanczos.Theorem59.betaM M j / (M : ℝ) ^ 2 -
            UniformLanczos.Profile.F ((j : ℝ) / (M : ℝ))| ≤ C / (M : ℝ) ∧
          |Real.sqrt (UniformLanczos.Theorem59.betaM M j) / (M : ℝ) -
            UniformLanczos.Profile.ξ ((j : ℝ) / (M : ℝ)) / 2| ≤ C / (M : ℝ) := by
  have hM_forall : ∀ M : ℕ, M₀ ≤ M → 0 < M := by
    intro M hM
    omega
  have hcert : ∀ M j : ℕ, M₀ ≤ M →
    (j : ℝ) / (M : ℝ) ∈ Icc t₁ t₂ →
    Σ L : ℕ, LocalOperatorCertificate M j L ε
      (Ca + Cb + Cf * Z2) c (4 * t) Cf := by
    intro M j hM hj
    obtain ⟨L, inp⟩ := hPublished M j hM hj
    exact ⟨L, constructActualCertificate (hM_forall M hM)
      ht hc hCa hCb hCf inp⟩
  have hmu : 0 < 4 * t := by linarith
  exact compact_uniform_rate_from_operator_certificates
    ht₁ ht₂ hε hε1 hc hmu hCf hsmall
    M₀ hM₀ hβ hupper hcert

end UniformLanczos.Rate514ActualOperatorCertificate

#print axioms UniformLanczos.Rate514ActualOperatorCertificate.constructActualCertificate
#print axioms UniformLanczos.Rate514ActualOperatorCertificate.actual_rate_of_published_calculus
#print axioms UniformLanczos.Rate514ActualOperatorCertificate.compact_uniform_rate_of_published_calculus
