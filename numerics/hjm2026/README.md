# Heilman, Jones and Malavolta (arXiv:2610.10477v1, 7 Oct 2026): check of the claimed bounds

S. Heilman, C. Jones and G. Malavolta, *Primal/Dual Method for the Grothendieck Constant* (preprint, not peer-reviewed), **claim**

  1.773 ≤ K_G ≤ 1.7799 (their Theorem 1.1),

and, heuristically, K_G ≈ 1.779. Their certificates are at https://github.com/christophsjones/RealGrothendieck (commit b02621d, 7 Oct 2026).

This folder records what we checked on 15 Oct 2026. Status categories:
- **certified by us**: independent method and code;
- **re-executed by us**: the authors' verifier, run here from source;
- **checked by hand**: an analytic step we read and verified;
- **claimed**: not checked.

## Lower bound K_G ≥ 1773/1000

### Analytic chain (checked by hand)

1. **Theorem 2.2, left inequality: K_G ≥ 1/v_∞(q).** This holds for every Hermite projection game Q = Σ q_m Π_m with q_1 = 1, |q_m| ≤ 1, q_{2m} = 0.
   - SDP(Q) ≥ 1 − o_n(1) with f(x) = g(x) = x/‖x‖. Indeed ⟨f, Qf⟩ ≥ 2‖Π_1 f‖² − ‖f‖² = 2(E‖x‖)²/n − 1 → 1.
   - Matrices are obtained by the standard discretization.
   - This is the same mechanism as Davie's and Reeds' lower bounds.
2. **Lemma 2.6.** Odd Boolean functions suffice.
3. **Proposition B.1** (one-variable criterion). We checked every step:
   - the identity ⟨f, Qg⟩ = Σ q_m(‖Π_m h‖² − ‖Π_m k‖²), with h = (f+g)/2, k = (f−g)/2, h² + k² = 1;
   - the rotation-average bound (B.12) via Mehler, with σ_{r+N} = −σ_r;
   - α_m = β_m = −Γ_m ≤ 0 for m > 21, from (B.6);
   - the fibre decomposition z = (S, Y) and Parseval in Y, where degree 2j + p + |η| gives D_{p,|η|};
   - the semidefinite bounds (B.7), including the Schur-complement step at η = 0, p = 1;
   - the Bessel bound on the 3ε cost;
   - the identity E_Y (h_1(M))_0 = √(2/π) x;
   - convexity of Φ.
4. **Section B.2** (reduction to signs). We checked:
   - convexity: F(M) − F(Bσ) ≤ ξᵀM − ‖Bᵀξ‖₁ with ξ = 2RM + ℓ and σ = sign(Bᵀξ);
   - the quadratic Bernstein interpolant with nonnegative weights;
   - the Peano constant 1/96. As a sample, for p = s³ the error integral is 1/32 ≤ 6/96;
   - the panel density comparison e^{h max|s|};
   - the roof-duality (min-cut) upper bound (B.20).

   We read the persistency argument for sign fixing, but did not re-derive it.

### Numerical certificate (re-executed by us, `lower_run/`)

We ran `python verify.py --lower --workers 2` from a fresh clone. Two local adjustments were needed:

- **Manifest.** In the published commit, the SHA-256 entries of `lower/README.md` and `upper/README.md` (and hence of `lower/MANIFEST.sha256`) do not match the files. These are documentation files only. We updated those three hashes in a working copy. No source or data file was changed, and all other hashes matched.
- **Build tools.** PyPI is not reachable from our machine, so we built GMP 6 with `--enable-cxx` (for `gmpxx.h`) and used Cython 3.2.4 from its GitHub source.

Result (`lower_run/logs/final_assembly.log`, `lower_run/VERIFICATION_REPORT.json`):

- `KG_1773_THEOREM_ACCEPTED=1`, `CERTIFIED_KG_LOWER=1773000000000/999999998227`;
- 35/35 universal fibres regenerated and certified;
- 1820 matrix positive-definiteness checks;
- 32/32 negative controls rejected;
- the deliberately insufficient repair 10⁻¹² fails, as designed;
- 70/70 exact rational tail inequalities (`TAIL_CHECK.json`);
- 384-bit MPFR endpoint arithmetic.

The driver stopped only afterwards, while writing the environment record: `importlib.metadata` found no installed metadata for Cython, because we used it from its source tree. That happens after the final assembly and does not affect the certificate.

**Status:** the analytic chain is checked by hand and the numerical part is re-executed by us. The method and the code are the authors', not independent ones.

## Upper bound K_G < 1779893/1000000

- **Lemma 2.1 (checked by hand).** For any randomized rounding with E[x̃ỹ] = H(⟨u,v⟩) = Σ c_m t^m, applied to SDP-optimal vectors, OPT(A) ≥ (c_1 − Σ_{m≥3} |c_m|) SDP(A), using ±(u^{⊗m}, v^{⊗m}). It needs no Krivine preprocessing.
- **The rounding algorithm of Section 4.2 (checked by hand).** It is explicit: a signed tensor realization of the 31 polynomials P_i, with ‖P_i‖_A ≤ 1, and shared Gaussian vectors. The formula (C.2), H_i(t) = Σ C[a,b] P_i(t)^a (−t)^b, follows from Mehler's formula. The bound therefore does not need the asymptotic-space results (Theorem 3.2, which rests on the preprint HMP24 and the unpublished Jon26).
- **Numerical part (re-executed, `upper_run_mac/`).** We ran `python verify.py --upper` on 15 Oct 2026 on the author's MacBook Pro: Intel x86_64, 32 GB, macOS 15.8.1, Python 3.12.15, NumPy 2.3.5, python-flint 0.9.0. The same three documentation-hash corrections were needed, plus `upper/MANIFEST.sha256` (README.md); no source or data file was changed.
  - All 12 stages completed in about 20 minutes (1202 s): `FRESH_COMPLETE_UPPER_CERTIFICATE_VERIFIED=1`, `CERTIFIED_KG_UPPER=1779893/1000000`.
  - Margin c₁ − Σ_{m≥3}|c_m| ≥ 0.5618315289504650030756700411845 (± 9·10⁻³⁷), so K_G ≤ 1.7798929901069453754 < 1.779893.
  - Components: head through degree 681 ≥ 0.561877379945335208; non-additive tail ≤ 3.8782·10⁻⁶; rare additive tail ≤ 3.40972·10⁻⁵; heavy additive tail ≤ 7.8758·10⁻⁶. These agree with the values printed in Theorem 4.2.
  - The 256-bit Fourier-tail check (C.22) passes: 2.72·10⁻¹⁸ < 3·10⁻¹⁸.
  - Note: the upper package's own final log still states `lower_endpoint_status: NOT_CERTIFIED` for the degree-21 game. That text comes from the upper package, which predates the separate lower certificate (re-executed above).
  - **Status:** reduction checked by hand; numerical certificate re-executed. The analytic claims of Appendix C (Claims 1–9) are implemented in the verifier, but we have not checked them by hand. Method and code are the authors'.

## Summary

| Statement | Status |
|---|---|
| K_G ≥ 1.773 | analytic chain checked by hand; authors' certificate re-executed and accepted |
| K_G < 1.779893 | reduction checked by hand; authors' certificate re-executed (on the author's Mac) and accepted; Appendix C claims not checked by hand |
| K_G ≈ 1.779 | heuristic, by the authors' own description |
