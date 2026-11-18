# M15 §6.5 — squarefree trace-class determinant: analytic subcase

Date: 2026-11-17. Independent proof note for the long-standing obligation `prop:squarefree-eulerian-det` recorded in `CERTIFICATION_SCOPE_20261115_DISCUSSION_FIRST.md`. **Not a Lean 4 compilation or an Arb certificate.** This note proves the ordinary trace-class determinant and its locally convergent logarithmic series; it does **not** prove any zeta-regularized determinant, meromorphic continuation, or the manuscript's exact operator identification if its eigenvalue convention differs.

## Exact construction and convergence

Fix a real `s>1`. Let `Q={n∈ℕ : n≥1 and n is squarefree}`, and let `H=ℓ²(Q;ℂ)`. Define `T_s e_n=n^{-s}e_n` on its canonical orthonormal basis. The diagonal entries are positive, and

`Tr(|T_s|)=Σ_{n∈Q}n^{-s} ≤ Σ_{n≥1}n^{-s}=ζ(s)<∞.`

Thus `T_s` is positive trace class (hence compact). Its ordinary Fredholm determinant is an **entire** function of `z∈ℂ`:

`D_s(z)=det_F(I+zT_s)=∏_{n∈Q}(1+z/n^s).`

The product converges normally on compact subsets of `ℂ`, since `Σ_{n∈Q}|z|n^{-s}<∞`. This is the usual trace-class determinant; no regularization is needed for `s>1`.

## Squarefree Dirichlet identity

For every real `u>1`, `1_Q(n)=μ(n)^2` and absolute convergence of the Dirichlet series and Euler products give

`Σ_{n∈Q} n^{-u}=Σ_{n≥1} μ(n)^2/n^u=∏_{p}(1+p^{-u})=ζ(u)/ζ(2u).`

The prime-factor identity is `1+p^{-u}=(1-p^{-2u})/(1-p^{-u})`; convergence is absolute because `Σ_p p^{-u}<∞`. This identity does not imply a corresponding formula at `u≤1` without separate continuation arguments.

## Logarithmic Fredholm series

For `|z|<1`, all `|z|n^{-s}<1`. Expanding the logarithm at zero and interchanging sums absolutely gives

`log D_s(z)=Σ_{n∈Q}log(1+zn^{-s})=Σ_{k≥1}(-1)^{k+1}z^k/k · ζ(ks)/ζ(2ks).`

Here `log D_s(0)=0` specifies the analytic logarithm on the open unit disk: `D_s` has no zeros there. A direct absolute majorant is

`Σ_{n∈Q}Σ_{k≥1}|z|^k/(k n^{ks}) ≤ ζ(s) Σ_{k≥1}|z|^k/k = -ζ(s)log(1-|z|)<∞.`

Consequently `Tr(T_s^k)=ζ(ks)/ζ(2ks)`, and the expansion is exactly the standard trace-log formula. The radius one is sharp because `n=1` gives the zero `D_s(-1)=0`.

## Rigorous truncation bounds

Let `Q_N=Q∩[1,N]`, `D_{s,N}(z)=∏_{n∈Q_N}(1+zn^{-s})`. For any `N≥1`,

`Σ_{n∈Q, n>N} n^{-s} ≤ Σ_{n>N}n^{-s} ≤ N^{1-s}/(s-1).`

Using the telescoping finite-product estimate and `|1+w|≤e^{|w|}` yields the uniform complex bound

`|D_s(z)-D_{s,N}(z)| ≤ |z| exp(|z|ζ(s)) N^{1-s}/(s-1).`

For `|z|≤r<1`, truncating the logarithmic series after `K≥1` gives

`|log D_s(z)-Σ_{k=1}^K (-1)^{k+1}z^k ζ(ks)/(kζ(2ks))| ≤ ζ(s) r^{K+1}/((K+1)(1-r)).`

These bounds are analytic estimates, not FLINT/Arb balls. Any numerical certification must separately use `ctx.prec=3600000`, individual `rel_accuracy_bits()>=3400000` assertions for appropriate nonzero quantities, and exact rational rounding-cell containment at 1000001 significant digits on the exact HEAD.

## Lean 4 work still required

Construct the diagonal bounded operator and prove trace-class summability; identify its trace powers; prove the squarefree indicator/Möbius-square identity and absolutely convergent Euler products; identify the Fredholm determinant with the diagonal product; justify locally uniform logarithmic expansion and the two explicit tail bounds. Reuse existing Mathlib definitions where possible. None of these steps is claimed Lean-certified by this note.

**Scope boundary:** the result concerns the standard positive squarefree diagonal spectrum `n^{-s}`, `s>1`. Any zeta-determinant, regularized product at a singular parameter, alternate multiplicity, or connection to the actual geometric operator in M15 requires a separate theorem. No manuscript, figure, M11–14, V007, or V097 file is modified. No merge.
