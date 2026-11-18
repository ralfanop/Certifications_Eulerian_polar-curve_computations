# M16 v16.6 §13 — Schatten operator realization and ideal transfer

Source of record: author-approved `Manuscript_16_AI_Declaration_20261118(1).zip`,
SHA256 1f316919eae73c3459fdbdf0572ba1d523aca297cd18594faae0efd6655895d4.
Section 13 SHA256 21fec377ce89f5ffd47c13b1f8d38a5e3453965c578e1d937d16bd5bfd2a1bdd,
unchanged from v16.5, reconciled in #403. See #344 for shell analysis,
#368 for Lean nearest-mode divergence, and #401/#404 for actual graph-domain
inversion and compactness transfer.

## Operator argument (mathematical proof; not all steps are Lean-certified)

On the maximal spectral domains use the stated complete orthonormal spectral
decompositions for the deck-even nonresonant Maxwell block and the spatial
Dirac block (not the spacetime Dirac block). Repeated according to the
multiplicities in §13 and the earlier spatial Dirac spectral formula, the
absolute diagonal entries of the inverse are:

* Maxwell: 1/(4 |k| |ell+k|), ell>=2, k integer other than 0,-ell,
  each repeated 2(ell^2-1).
* Dirac: 1/(n+3/2), n>=0, repeated 2(n+1)(n+2) (both signs).

For each positive threshold t the number of entries >=t is finite:
for Maxwell, min(|k|,|ell+k|)>=1 and max>=ell/2 imply ell<=1/(2t);
also |k|<=1/(4t). For Dirac n+3/2<=1/t. Thus the entries admit a
nonincreasing enumeration s(0), s(1), ... tending to zero. On the actual
spectral Hilbert direct sum the diagonal inverse is bounded (norm 2/3)
and its rank-n truncation has operator-norm error exactly s(n), by
Parseval and evaluation on the first omitted eigenvector. In particular
it is compact, as the norm limit of finite-rank maps.

These entries are not just a scalar proxy: for every map R factoring
through C^n, restrict R to the span of the first n+1 orthonormal
eigenvectors. Rank-nullity gives a unit vector v in that span with Rv=0.
Parseval then gives ||(L0^-1-R)v||=||L0^-1 v||>=s(n), so the rank-n
approximation optimum is exactly s(n). This also identifies the
singular values, because (L0^-1)* L0^-1 is diagonal with squared
absolute entries. The construction is valid even with repeated values
or negative original eigenvalues.

The Maxwell sum is bounded for p>3 by the shell estimate (at most four
k for each minimum j) times the p-series in ell^(2-p). Its nearest
mode k=1 gives the divergent lower series for all 0<p<=3:
for p=3 the bound 1/[96(ell+1)] applies; for smaller p the inverse
entries are <=1, hence their p-powers are no smaller. The Dirac series
has the same threshold by comparison with (n+1)^(2-p). Since this is
a disjoint union of nonnegative singular-value summands, the mixed
inverse belongs to S_p iff p>3, for positive real p.

For an arbitrary compact Hilbert-space operator T the same rank-n
extremal argument uses the right singular vectors and the singular
value expansion (including zero values for finite-rank T). This proves
the equivalence of the approximation characterization in the Lean file
with S_p. Conversely if the approximation envelope has summable p-th
powers for p>0, it tends to zero, so the finite-rank maps converge in
norm and T is compact, and the lower estimate proves summability of
the singular values. Finite-rank maps factor through C^n by choosing
a basis of their range and the continuous coordinate map, padding
with zeros as necessary. No infinite-dimensional singular-value API
is assumed in Lean: the pinned Mathlib SingularValues.lean is
explicitly finite-dimensional.

For U=I+E L0^-1 the already proved graph Neumann construction gives
L^-1=L0^-1 U^-1 and L0^-1=L^-1 U. If G F approximates T with rank at
most n, (G F)C and B(G F) approximate TC and BT with error bounded
respectively by ||T-GF|| ||C|| and ||B|| ||T-GF||. Consequently the
approximation envelope remains p-summable under these operations.
This proves the sharp threshold for L^-1 and K=B L^-1 C in S4,
and indeed K in every S_p for p>3. No lower threshold for arbitrary
K is asserted (B or C can vanish).

## Lean scope

V166SchattenIdeal.lean proves the approximation ideal laws on actual
continuous linear maps, the optimal-error criterion, both directions
of graph inverse membership transfer, and the mediated S4 statement
conditional on reference membership. It does not formalize the
spectral realization/Parseval/rank-nullity chain above, the
equivalence with the infinite-dimensional singular-value definition,
or the infinite spectral sums for all p in one compiled theorem.
Those are outstanding. The full regularized determinant criterion
also requires non-normal compact spectral theory and the canonical
product. This is distinct from the scalar reference diagonal model
in #373/#379. No numerical calculation or Arb enclosure is claimed.

No manuscript edits or merge.
