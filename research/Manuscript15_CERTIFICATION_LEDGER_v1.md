# Manuscript 15 — Lean 4 certification ledger v1

**Date:** 10 November 2026 UTC
**Branch:** manuscript15-cycloidal-lean4-20261110
**Pull request:** #112 (DRAFT; DO NOT MERGE)
**Source-tested commit:** 9edea534427899894555c4c688d5c77c9240dbec
**CI run:** https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/42880981222
**CI result:** SUCCESS

## Configuration

- Lean toolchain: leanprover/lean4:v4.35.0-rc3
- Mathlib pin: 0272bbe1c093d038d7257ab15306abd58245f9ff
- Builds the inherited local module EulerianCert.FourierModes before checking Manuscript 15.

## Exact declarations kernel-checked

File: lean/Manuscript15/CycloidalReconstruction.lean

1. Manuscript15.eulerian_X_eq_cycloid
2. Manuscript15.eulerian_Y_eq_cycloid
3. Manuscript15.eulerian_kinematic
4. Manuscript15.cusp_leading_coefficient — leading-order algebraic ratio only, NOT the analytic limiting proposition.
5. Manuscript15.eulerian_Y_pi

File: lean/Manuscript15/CoefficientRigidity.lean

6. Manuscript15.coefficientRule_unique — uniqueness of any sequence satisfying the stated exact quadratic recurrence and c(0)=1.

For all SIX declarations, the successful workflow ran #print axioms. The reported axioms were precisely a subset of [propext, Classical.choice, Quot.sound]. No sorryAx or Lean.ofReduceBool occurred.

## Delimitations: not yet certified

- Extraction of the recurrence for the actual Taylor coefficients of a compactly supported symmetric probability measure from X_f'=Y_f.
- Identification of the sinc Taylor coefficients as a solution of the abstract coefficient rule.
- Reconstruction of equality of entire characteristic functions from equality of coefficients.
- Uniqueness of characteristic functions, identifying the compactly supported measure as Uniform[-1/2,1/2].
- The nontrivial limits in the cusp proposition and endpoint classification of convolution powers.
- Quantitative Wasserstein bounds in the full probabilistic model.
- Any theorem connecting these mathematical structures to wormholes, AdS/CFT dynamics, experimental qubits, or physical gravitomagnetism.
- Bibliographic priority; a separate agent is responsible for this audit.

## Scope and preservation

Manuscripts 11–14 and the V007/V097 certification projects were not modified. The PR remains draft and is not merged. This ledger reports *tested* declarations only; it does not count proposed manuscript statements as certified.
