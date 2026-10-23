V033 INDEPENDENT VERIFICATION AND ALL-DEGREE LEAN PROOF — 21 October 2026
Final package updated 21 October 2026.

PACKAGE CORRECTIONS
This archive includes this README.txt and builds V033UniformIntegrals.lean
in code/verify_lean_portable.sh before V033Verification.lean.
SHA256SUMS.txt records the hashes of all other packaged files.

MAIN RESULT
All twelve supplied rational functions beta_5 through beta_16 are correct.
The two-term theorem is mathematically valid for every FIXED j >= 1:
  beta_j(M) = j*M/12 - j*(j-1)/20 + O_j(1/M).
No coefficient, sign, scalar or normalisation error was found.

FORMALISATION STATUS - UPDATED 21 OCTOBER 2026
The all-degree two-term asymptotic theorem is now formalised in Lean 4.
The final statements are in lean/V033AllDegreeTheorem.lean:
  uniform_integral_hankel_two_term
  uniform_probability_two_term
  canonical_two_term
  two_term_lanczos_asymptotic

The first theorem concerns actual integrals of powers of sums of independent
uniform random variables. It proves eventual nonvanishing of the relevant
Hankel determinant and the quantitative two-term bound, for EVERY fixed
positive degree. The second theorem identifies the same conclusion for any
monic orthogonal family having the defining three-term recurrence.

Its polynomial-family hypotheses specify the mathematical object: monicity,
degree, orthogonality, initial polynomials and the three-term recurrence.
They do NOT assume a moment expansion, a Gaussian limit, a perturbation
formula, a determinant formula for beta, or a bounded remainder. These are
proved. The separate canonical/integral-Hankel theorem has no polynomial-
family hypothesis. The code does not construct an infinite orthogonal family
as a separate existence object; the standard defining family is universally
quantified, and its determinant representation is proved from its properties.

The new proof uses exact cumulant polynomials, finite matrix algebra and
continuity of a rational function with nonzero constant denominator. It does
not use an Edgeworth theorem. The estimate is explicitly
  exists C>0, exists N>0, forall integers M>=N,
  abs(beta_j(M)-j*M/12+j*(j-1)/20) <= C/M.
The constants may depend on j. No joint growing-degree limit is asserted.

The complete 56-source build and its portable verification script passed.
The audit covers 631 named declarations: 499 earlier certificates and 132
new general lemmas/theorems. These are not 631 independent discoveries.
Only propext, Classical.choice and Quot.sound (or no axioms) are used.
No sorry, admitted proof, custom axiom, or native_decide is used.

CONTENTS
- V033_INDEPENDENT_ADVERSARIAL_REVIEW.pdf: English review and complete paper proof.
- report/main.tex: editable review source.
- inputs/: supplied V033 files, unchanged.
- code/independent_check.py: independent reconstruction, without importing JS.
- code/generate_lean.py: generator for data and orthogonality/ratio witnesses.
- lean/: transparent Lean sources and exact certificates.
- results/independent_exact.json: all moments, polynomials, norms and checks.
- results/independent_exact.log: fresh exact-computation log.
- results/lean_axiom_audit.log: earlier 499-declaration axiom audit.
- results/full_axiom_audit.log: the 132 new declarations.
- FORMAL_THEOREM_MAP.txt: statement interpretation and proof dependency map.
- results/input_hashes.json: supplied-file hashes, including V032.
- VERIFICATION_STATUS.json: machine-readable coverage and limitations.

EXACT COMPUTATION
With Python 3.10 or later, from the package directory:
  python3 -m pip install -r requirements.txt
  python3 code/independent_check.py
The code constructs moment polynomials by falling-factorial occupancy counts,
then uses symbolic Stieltjes orthogonalisation and checks all orthogonality
conditions. It separately performs full Fraction Gram-Schmidt at
M=1,2,3,4,5,10, through degree 16. Only afterward does it recompute parity
determinants and scalar factors for comparison with the supplied data.

LEAN REPRODUCTION
Install elan/Lean 4.24.0 and Lake. From this package directory:
  lake update
  lake exe cache get
  bash code/verify_lean_portable.sh
The lakefile pins mathlib to f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
The ZIP omits .olean caches and the large dependency tree; sources and build
logs are included. The script builds one module at a time, limiting each Lean
process to 2048 MiB. It requires ripgrep (rg) and Python 3 for the final declaration-by-declaration
axiom audit (code/audit_kernel.py).
code/run_lean.sh records the local cached-runtime invocation actually used
for this audit; that wrapper is specific to the original computer.

CERTIFICATE INTERPRETATION
The polynomial checker is proved sound for real evaluation. The occupancy
identities are checked through order 32. Monic polynomial witnesses and
every lower-monomial orthogonality identity are checked through degree 16.
The norm-ratio identities are denominator-cleared. Their real rational
interpretations explicitly state nonzero-denominator hypotheses. Universal
positive-integer nonvanishing of every supplied expanded denominator remains
a paper proof. The new all-degree Lean theorem proves the eventual
nonvanishing required for its asymptotic result; it does not assert a formal
all-M positivity theorem for the original finite JSON denominator arrays.

JSON CAUTION
Expanded numerator/denominator arrays ALREADY contain the scalar. Do not
multiply their quotient by scalar again. The scalar belongs only to the
factorised representation. The supplied JavaScript regenerates the same
mathematical data with different JSON key names. See the report and
results/supplied_js_reproduction/.

NOVELTY AND SCOPE
The first two terms are present in Milovanovic (2017), Conjecture 2, p.347.
A proof can be a contribution; priority has not been certified. The theorem
is fixed-degree: it establishes no joint large-j, large-M regime and no
higher terms of the conjectured series. V032 was not edited or used as
independent corroboration. The previous uniform-asymptotic review stays paused.
