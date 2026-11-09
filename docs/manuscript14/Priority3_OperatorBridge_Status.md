# Manuscript 14.119 — Priority 3: operator-dependency audit

**Scope:** the operator-theoretic inputs of Proposition 6.2 (relative zeta-regularised
determinants versus Fredholm determinants) and Proposition 5.4 (identification
with DLMF angular oblate spheroidal functions). This record distinguishes
established formal theorems from missing functional-analytic identifications.

## Existing kernel certificates (not new claims)

- DirichletFiniteDeterminant and DirichletFiniteTrace: determinant of concrete
  finite diagonal matrices, positive finite products, and finite trace formulas.
  Finite-dimensional identities **are not** infinite Fredholm determinants.
- Section67ScalarCertificate: infinite Euler products for sinh(x)/x and cosh(x),
  and scalar spectral traces. This module explicitly does **not** define a
  trace-class Fredholm determinant or a zeta-regularised determinant.
- GegenbauerSpectralRealisation, SpheroidalProposition54: the actual
  self-adjoint compact-resolvent realisation and the joint spectral Hilbert
  basis, parity, simplicity in parity sectors, and positive Gram eigenvalues.
- SpheroidalDLMFIdentification: the correspondence with the standard
  DLMF special functions is conditional on an explicit structure
  Manuscript14Gram.DLMF30.OblateInput c.

## New first bridge: genuine finite-to-infinite Dirichlet product

V14119Priority3SpectralDetBridge proves, for real x != 0:

1. The concrete finite determinant factors at t=x² are the Euler factors.
2. The finite products converge (as N tends to infinity) to sinh(x)/x.
3. The infinite spectral product, **defined as a convergent tprod**, equals
   sinh(x)/x.

This is a scalar spectral product theorem; its name and docstring deliberately
do not identify that product with a zeta determinant or with a determinant
of a trace-class operator. Certification status is the CI of this module.

## Remaining obligations: determinant bridge

1. Construct or identify the positive Dirichlet Sturm–Liouville operator
   A on L²(0,1) with eigenvalues π²(n+1)² and the corresponding eigenbasis.
   Identify its bounded inverse A⁻¹ with the actual operator—not merely
   an abstract sequence of eigenvalues.
2. Prove that A⁻¹ is trace class (the summability of its positive
   eigenvalues is not by itself a formal trace-class instance) and prove
   det_F(I+t A⁻¹) equals the actual spectral product.
3. Define the spectral zeta functions for A+tI and A, prove the
   relevant analytic continuation and differentiability at s=0, and
   justify the identity
       log det_zeta(A+tI) - log det_zeta(A)
       = log det_F(I+t A⁻¹)
   under precisely stated boundary conditions and t>=0.
   Do not take this formula as an axiom disguised as a definition.
4. Extend to the mixed Dirichlet–Neumann boundary spectrum
   π²(n+1/2)² where required by Proposition 6.2 and
   Theorem 7.2, and derive the cosh product by the same operator route.

The classical analytic reference is K. Kirsten and A. J. McKane,
"Functional determinants for general Sturm–Liouville problems",
J. Phys. A 37 (2004), 4649, DOI: 10.1088/0305-4470/37/16/014.
It is a source, not a formally supplied axiom.

## Remaining obligations: spheroidal DLMF identification

The existing structure OblateInput c bundles a strictly increasing
eigenvalue enumeration, nonzero real C² solutions of the oblate
spheroidal ODE on [-1,1], and the uniqueness/normalisation statement.
The existing Lean proof is conditional on this structure.

To close the dependency fully, derive or construct those data from
the already-certified self-adjoint regular Sturm–Liouville problem:
- establish sufficient regularity and endpoint conditions for
  the solutions representing the spectral eigenvectors;
- prove uniqueness and ordering of the regular eigenvalues and the
  one-dimensional eigenspaces without assuming OblateInput;
- identify the canonical normalised functions with the standard
  DLMF Ps_n^0(·,-c²) convention, including indices and phases/signs.

DLMF §§30.2–30.3 defines the spheroidal differential equation
and the eigenvalue indexing:
https://dlmf.nist.gov/30.2
https://dlmf.nist.gov/30.3

## Interpretation rule

Only statements for which the CI supplies a successful Lean kernel
check **and** a clean axiom audit are reported as certified.
Results dependent on OblateInput or a future zeta/Fredholm bridge remain
conditional until those hypotheses themselves are discharged. Priority 3
is therefore *in progress*, not yet complete.
