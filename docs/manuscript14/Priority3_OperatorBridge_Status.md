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

1. The concrete finite Dirichlet determinant factors at t=x² are the Euler factors.
2. The Dirichlet finite products converge (as N tends to infinity) to sinh(x)/x.
3. The infinite Dirichlet spectral product, **defined as a convergent tprod**, equals
   sinh(x)/x.
4. The mixed Dirichlet–Neumann finite spectral products converge to cosh(x).
5. Their infinite spectral product equals cosh(x).

Items 4–5 refer to the explicit mixed spectral factors, not yet to the
resolvent or determinant of a constructed mixed-boundary differential operator.

This is a scalar spectral product theorem; its name and docstring deliberately
do not identify that product with a zeta determinant or with a determinant
of a trace-class operator. Certification status is the CI of this module.

## Second bridge: actual spectral inverse on complex Hilbert space

The new `V14119Priority3DirichletDiagonal.lean` module constructs a **genuine**
bounded positive operator on `ℓ²(ℕ, ℂ)` as the operator-norm convergent series
of Dirichlet inverse spectral rank-one projections with coefficients
`(π²(n+1)²)⁻¹`. It certifies summability, convergence, the exact eigenbasis
action, Loewner positivity and the corresponding real diagonal values.
[Kernel CI #42701424154](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/42701424154)
finished **SUCCESS** with five audited theorems and only standard axioms.

The `V14119Priority3TraceClassModel.lean` module establishes that
this **actual positive spectral inverse** is in the source-compatible
complex CFC-absolute Schatten-S₁ class, with basis-independent trace norm
equal to the sum of its positive inverse eigenvalues. PR #79 was merged
and [CI #42702505123](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/42702505123)
verified all seven declarations with only standard axioms.

PRs #80–81 then proved the matrix coefficients and determinants of the
**actual finite Hilbert-basis compressions**, including exact equality
with the finite Dirichlet Euler factors and convergence to sinh(x)/x.
[CI #42707655344](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/42707655344)
verified six declarations.

Neither this spectral-model construction nor the finite-compression
theorems identifies the model via a proved unitary map with the
differential realisation of `-d²/dx²` on `L²(0,1)` with Dirichlet
boundary conditions. That remains a separate open obligation.

## Third bridge: genuine trace-norm convergence of the spectral truncations

PR #82 adds two modules, `V14119Priority3RankOneS1.lean` and
`V14119Priority3S1Truncation.lean`. The first establishes that
**each actual rank-one inverse summand**
`T_n = (π²(n+1)²)⁻¹ |e_n⟩⟨e_n|` belongs to the true
CFC-absolute trace class and has genuine trace norm
`‖T_n‖₁ = (π²(n+1)²)⁻¹`.

The second instantiates the already-certified V007 Schatten-S₁ Banach
series theorems and proves the following *actual operator* estimates,
in the trace-norm topology:
`‖A_sp⁻¹ - ∑_{n<N} T_n‖₁ ≤ ∑_{k≥0}(π²(k+N+1)²)⁻¹`,
with the error tending to zero as N tends to infinity.
The same numerical tail also bounds the ambient operator-norm error.
The infinite S₁ Banach sum is identified explicitly with the original
bounded operator `A_sp⁻¹` rather than merely its formal spectrum.

[CI #42710157209](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/42710157209)
completed **SUCCESS** for ten named declarations on PR #82's
working commit. The push and PR workflows both passed on the definitive PR #82 commit\n`1cfcb2e95587` (runs #42711608603 and #42711611430). The PR was merged\ninto `main` on 10 November 2026 (merge commit `c80b4ab88a5a2bd`). **A trace-norm compression limit is not by itself
a basis-independent definition of the Fredholm determinant**; proving
the Fredholm determinant's well-definedness and continuity remains open.

## Fourth bridge: certified trace-class continuity reduction

`V14119Priority3FredholmContinuityReduction.lean` makes the precise
remaining logical dependency explicit. Its four declarations are deliberately
*conditional* on properties of a future operatorial determinant:

1. The actual finite S₁ compressions converge to the true S₁ inverse
   Banach sum in the genuine CFC Schatten norm.
2. Any functional `F : TraceClass H → ℂ` continuous at that inverse and
   agreeing with the true finite compressed complex matrix determinants
   at each truncation must satisfy `F(A_sp⁻¹)=sinh(x)/x` for the
   nonzero real shift parameter `x` (with the shift `x²` incorporated
   into the finite-rank compatibility condition for `F`).
3. Any two functionals continuous at this inverse and agreeing on
   all its finite trace-class truncations must agree at the infinite inverse.
4. Any locally Lipschitz functional satisfying the stated trace-norm
   estimate on this approximation path inherits a quantitative error
   bounded by its Lipschitz constant times the already certified
   spectral S₁ tail.

**Status: certified, merged in PR #83** (merge SHA
`ea21d81be6cce5d7068a49f619c8847c95776a9b`).
Pinned exact-head PR CI #42777071909 and push CI #42777000432
both returned SUCCESS for four declarations, with only `propext`,
`Classical.choice` and `Quot.sound`. This is a uniqueness-and-continuity
reduction, **not** the
existence, basis independence or trace-norm continuity proof of the
abstract Fredholm determinant. No zeta regularization is postulated.

## Fifth bridge: general positive diagonal S₁ operatorial sector (corrective PR #85)

**Certification alert:** PR #84 was merged at 08:01 UTC on 10 November 2026 before the new module's CI completed. CI #42779117046 subsequently FAILED on the Fin-index/range-product conversion. The copy introduced to `main` by PR #84 is NOT a certified result. Corrective PR #85 includes the fixed rewrite and the extended audit; do not merge it until all checks succeed.

Candidate `V14119Priority3PositiveDiagonalFredholm.lean` is no longer
restricted to the Dirichlet coefficient sequence. A parameter of
type `Data` is **any** nonnegative real summable sequence `a n`.
The module constructs actual Hilbert-space rank-one operators
`(a n : ℂ) • rankOne ℂ (b n) (b n)`, proves their exact CFC Schatten
trace norms, forms the genuine CFC S₁ Banach sum and checks its underlying
operator equals the norm-convergent bounded infinite operator.

It also proves that its true S₁ norm equals `∑' n, a n`, that the finite
S₁ truncations converge with quantitative tails, and that the
**complex determinants of actual Hilbert-space compression matrices**
converge to the infinite product `∏' n, (1+t*a n)` for arbitrary real
`t`. The original Dirichlet operator and finite compression matrices
are recovered as exact instances.

New `V14119Priority3FredholmSectorFunctional.lean` proves that a positive diagonal operator in the actual CFC S₁ carrier uniquely determines its coefficient data, then defines a determinant as a FUNCTION ON THIS OPERATOR SUBTYPE (rather than merely on the coefficient sequence), establishes independence of the chosen diagonal-data witness, invariance under arbitrary index permutations, the absolutely convergent finite-subset Fredholm expansion, and the exact Dirichlet Euler-product specialization.

**Status: corrective PR #85, pending pinned Lean 4 compilation and full 19-declaration axiom audit.**
This is an actual operatorial diagonal-sector construction, but the
infinite product is a determinant only on that **fixed diagonal
commutative sector**. No basis-independent determinant functional
on the entire `S₁(H)` has yet been constructed, and no global S₁
continuity or unitary invariance has been certified. The proof must not
be described as the full Fredholm determinant until those results hold.

## Remaining obligations: determinant bridge

1. Construct or identify the positive Dirichlet Sturm–Liouville operator
   A on L²(0,1) with eigenvalues π²(n+1)² and the corresponding eigenbasis.
   Identify its bounded inverse A⁻¹ with the actual operator—not merely
   an abstract sequence of eigenvalues.
2. Transfer the certified CFC Schatten-S₁ property and trace-norm
   approximations of the **spectral** inverse to the **differential**
   Dirichlet inverse through a proved unitary equivalence; then construct
   and certify a basis-independent operator Fredholm determinant,
   including continuity in S₁ norm and the equality
   det_F(I+t A⁻¹) with the already-certified Euler product.
   Do not simply define det_F as that particular product.
3. Define the spectral zeta functions for A+tI and A, prove the
   relevant analytic continuation and differentiability at s=0, and
   justify the identity
       log det_zeta(A+tI) - log det_zeta(A)
       = log det_F(I+t A⁻¹)
   under precisely stated boundary conditions and t>=0.
   Do not take this formula as an axiom disguised as a definition.
4. Construct the actual mixed Dirichlet–Neumann differential operator
   and identify its compact resolvent / trace-class inverse with the
   spectrum π²(n+1/2)² used in the now-certified scalar cosh product.
   Prove its Fredholm and relative zeta determinant identities by the
   same genuine operator route.

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
