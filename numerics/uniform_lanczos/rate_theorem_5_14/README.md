# Manuscript 12 — Theorem 5.14 (rate O(1/M)): numerical checks

Date: 20 November 2026.

These are floating-point computations in 80-bit extended precision (`numpy.longdouble`). They are evidence only and none of them is used in the proof. They are not Arb certificates.

The certification status of the printed Table 1 is unchanged, as stated in Section 6 of [`docs/manuscript12/Manuscript12_Certification.md`](../../../docs/manuscript12/Manuscript12_Certification.md) and in [`docs/manuscript12/M12_20261119_AUTHORITATIVE_RECONCILIATION.md`](../../../docs/manuscript12/M12_20261119_AUTHORITATIVE_RECONCILIATION.md). Theorem 5.14 and its proof are described in [`docs/manuscript12/M12_20261120_THEOREM_5_14_RATE.md`](../../../docs/manuscript12/M12_20261120_THEOREM_5_14_RATE.md).

## Method

The method is that of `../beta_bspline.py`, reimplemented independently.

1. **The weight.** `w_M` is the centred cardinal B-spline density, the law of `S_M = U_1 + ... + U_M`. It is evaluated on every knot interval by the Cox–de Boor recursion. All terms of the recursion are nonnegative, so there is no cancellation. The 80-bit exponent range (10^±4932) covers values down to `1/(M-1)!`.
2. **The discretisation.** Each knot interval carries `N_per` Gauss–Legendre nodes. The Stieltjes procedure on the resulting discrete measure gives `a_k = (beta_k^[M])^{1/2}/M`, the recurrence coefficients of `g_M(x) = M w_M(Mx)`.
3. **The profile.** `F(t) = xi_t^2/4` comes from `Phi(xi_t) = t`. Here `Phi` is computed by Gauss–Legendre quadrature in theta with 400 nodes. `I'` is computed by bisection on the bracket `1/(1/2-x) - 2 <= I'(x) <= 1/(1/2-x)`, which follows from (109).
4. **Controls.** The exact values `beta_1 = M/12` and `beta_2 = (M/3 - 1/5)/2` are reproduced to machine precision. The results are identical for `N_per = 32` and `48`.

## Results

`table1_log.txt` gives the values of `M * E_{j,M}`, with `j = tM`:

| t | F(t) | M = 100 | M = 200 | M = 400 | M = 800 |
|---|------|---------|---------|---------|---------|
| 1/4 | 0.0178432 | 0.0108277 | 0.0108002 | 0.0107864 | 0.0107795 |
| 1/2 | 0.0303768 | 0.0171709 | 0.0171109 | 0.0170811 | 0.0170662 |
| 1 | 0.0445361 | 0.0176478 | 0.0176019 | 0.0175790 | 0.0175676 |
| 2 | 0.0548091 | 0.0104792 | 0.0104706 | 0.0104663 | 0.0104642 |
| 4 | 0.0598372 | 0.0043398 | 0.0043413 | 0.0043420 | 0.0043424 |

- The columns M = 100, 200 and 400 agree with the printed Table 1.
- The column M = 800 is new and is not certified.
- The differences between consecutive columns halve as M doubles. This is consistent with a nonzero first-order term `e_1(t)/M`. It is a numerical observation, not a theorem.

`checks_log.txt` checks the ingredients of the proof:

- **Freud's identity (Lemma 5.11).** `k/a_k = int p_k' p_{k-1} g_M dx` agrees to 12 digits.
- **Residual of the true coefficients.** `G_k(a) = M int_{|x|<=0.49} I' p_k p_{k-1} g_M dx - k/a_k` stays bounded as M doubles: about 1.35, 2.39 and 4.47 for t = 1/4, 1/2, 1. The proof needs only `O(1)`.
- **Deviation of the coefficients.** `M (a_k - xi_{k/M}/2)` stays near 0.040, 0.049 and 0.042.

## Reproduction

Python 3.13, numpy 2.5, scipy 1.18; total run time a few seconds.

```
python3 profile_F.py
python3 table1.py 100,200,400 32,48
python3 table1.py 800 32
python3 check_proof_ingredients.py
```
