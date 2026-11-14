# Manuscript 16 v16.4 — nonresonant wave fourth spectral sum (independent audit)

Source: **the attached v16.4 ZIP, `16.tex`, Section 13**, especially
`eq:mixed-maxwell-index-164`, `eq:mixed-upper-series-164` and
`prop:mixed-schatten-164`. Does **not** modify the manuscript or 11–15.

## New closed expression (E = 0 only)

Write `ell >= 2`; on the deck-even nonresonant Maxwell space,
`m = ell + 2*k` with integer `k != 0,-ell`, and transverse
multiplicity `d_ell = 2*(ell**2-1)`. Then, by the spectral prescription,

```text
S_W = sum_{ell>=2} 2*(ell^2-1) *
              sum_{k in Z \ {0,-ell}} [4*abs(k)*abs(ell+k)]^(-4).
```

For each ell, partition k into `k > 0`, `-ell < k < 0` and
`k < -ell`. The two exterior ranges give equal terms. Therefore

```text
S_W = (2/256) * sum_{ell>=2} (ell^2-1) *
      ( sum_{j=1}^{ell-1} 1/(j^4*(ell-j)^4)
        + 2*sum_{j>=1} 1/(j^4*(ell+j)^4) ).
```

The `p=4` convergence proven by the bound in v16.4 §13 permits
rearranging these **nonnegative** series. Reindex the interior sum
by `a=j,b=ell-j`; reindex the exterior terms by ordered pairs
`a,b>=1`, `|a-b|>=2`. Thus

```text
128*S_W = sum_{a,b>=1} ((a+b)^2-1)/(a^4*b^4)
        + sum_{a,b>=1, |a-b|>=2} ((a-b)^2-1)/(a^4*b^4).
```

Because `(a-b)^2-1=0` when `|a-b|=1`, extending the second
sum to all pairs only introduces the diagonal contribution
`-sum_a a^(-8)=-zeta(8)`; correct it by adding `zeta(8)`.
The pairwise polynomial identity
`((a+b)^2-1)+((a-b)^2-1)=2(a^2+b^2-1)` yields

```text
S_W = [4*zeta(2)*zeta(4)-2*zeta(4)^2+zeta(8)]/128
    = pi^6/17280 - pi^8/907200
    = 0.045176809575... .
```

Using the *spatial* Dirac fourth expression (already in §8),

```text
Tr |(W_R direct_sum D_3)^(-1)|^4
    = pi^2-pi^4/12+pi^6/17280-pi^8/907200
    = 1.797356957831... .
```

**This is not** the v16.1 spatial `Delta_T direct_sum D_3`
fourth trace `1.778711559829...`. The new calculation does not
apply to `E != 0`, and does not imply a closed trace formula for
the effective resonant operator.

## Formal verification boundary

- Lean file `V164MixedWaveFourthArithmetic.lean`: five exact integer/
  polynomial algebra facts, **not** a proof of the reindexing of
  infinite sums, sphere multiplicities, or the operator trace.
- FLINT/Arb: independently encloses both equivalent closed **scalar
  expressions** at 10000 bits; checks minimum measured relative
  accuracy >=8182 bits, positivity and correct 12-digit rounding.
- Remaining analytic Lean obligations: identification of the
  infinite spectral trace with the double series, convergence/
  Tonelli reindexing, actual eigenvalue multiplicities, classical
  zeta special values, transfer to the Hilbert-space operator and
  the v16.4 Fredholm/det4 statements.

Status: research proof and reproducible numerical programme pending
exact-HEAD CI; do not call the operator theorem kernel-certified.
