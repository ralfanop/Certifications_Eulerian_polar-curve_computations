# Coefficient tails for polynomial-threshold limiting schemes (Saha et al., Peng)

The schemes below are written as f(w,x) = sgn(w + P(x)) and g(w,x) = f(w,−x), with corr(W,W′) = ρ(t) and corr(X,X′) = t:

- **Cubic–quintic** (Saha et al., arXiv:2608.11158, preprint): P = ϑHe₃, ρ(t) = (t − s₃²t³ + s₅²t⁵)/V.
- **Peng** (arXiv:2609.20074, preprint): P of degree 11 and ρ of degree 51.

The upper bound K_G ≤ π/(2γ) follows from the near-linearity criterion

  γ + Σ_{m≥3} |b_m| < b₁,  H(t) = Σ b_m t^m.

The b_m and the head Σ_{3≤m≤N} |b_m| are certified in `../cubicquintic` and `../peng2026`. This folder bounds the tail Σ_{m>N} |b_m| with **our own code**, independent of the authors' scripts.

## Method

1. **Representation of D³H.** H(t) = T_{−t}[K_{ρ(t)}(P(x), P(y))], where T_s is the Mehler trace. Since D T_{−t}[Ψ] = T_{−t}[DΨ − t ∂ₓ∂ᵧΨ], one gets D³H(t) = T_{−t}[Φ₃]. Φ₃ is a combination of nine kernels ∂_r^p(∂ₓ∂ᵧ)^a K_r. Bell polynomials and the recurrence for F_{ij} = φ⁻¹∂ᵤⁱ∂ᵥʲφ make them explicit; see the header of `d3norm.c`.
   - **Check:** we compare the formula with Σ m³ b_m t^m from the certified heads. They agree to 12–13 digits: cubic–quintic at t = 0.5, 0.8 and −0.3; Peng at t = 0.5 and −0.7. This uses `d3norm SCHEME test t`.
2. **Trace bound.** For |s| ≤ 1,
   |T_s G|² ≤ C_a (‖G‖² + a ‖∂ₓ∂ᵧG‖²),  C_a = Σ_{n≥0} 1/(1 + an²),
   by Cauchy–Schwarz on the diagonal Hermite coefficients. Parseval on |t| = 1 then gives
   Σ m⁶ b_m² ≤ C_a (J₀ + a J₁),
   where J_e is the mean over θ ∈ [0, π] of ‖(∂ₓ∂ᵧ)^e Φ₃(e^{iθ})‖²_{L²(γ⊗γ)}. The integrand is explicit: |R_e|²/(2π|d|) · exp(−Re(Q/d) − (x² + y²)/2).
3. **Rigorous integration (`d3norm.c`).** Arb ball arithmetic on boxes of [0, 8] × [−8, 8] × [0, π]; the integrand is invariant under (x,y) → (−x,−y).
   - R_e is enclosed in mean-value form: its value at the centre plus first-order jets in x, y and θ evaluated over the box.
   - The exponent uses the lower bounds A ± B ≥ ½.
   - Refinement is best-first: the box with the largest weighted excess is split first. The final bound is the sum of the upper bounds over all leaves.
4. **Exterior max(|x|,|y|) > 8.** Analytic bound (`d3norm SCHEME ext 8`). It uses |ℓᵤ|, |ℓᵥ| ≤ (|u| + |v|)/δ, where δ = min_{|t|=1} |1 − ρ²| is certified on 20000 θ-panels, together with Gaussian moments and |P(x)| ≥ U₀ for |x| ≥ 8.
5. **Closing step.** `tail_close.py` works in exact rationals. It uses the bound (Σ_{m>N, odd} m⁻⁶)^{1/2} ≤ (10N⁵)^{−1/2}, and C_a ≤ ½ + π/(2s)(1 + 2/(2z + 2z²)) with z = π/s and a = s².

## Results

### Cubic–quintic (N = 251)

Inputs, all certified by us:
- δ ≥ 0.37246733; the authors give 0.3724.
- **Inner domain** (`out/cq_A.log`, `out/cq_B.log`): J₀ ≤ 2 × 3.430454708 and J₁ ≤ 2 × 590.2601312. The two θ-halves give identical results, as expected from the symmetry θ → π − θ. These two logs were produced with the code of commit c7a96fe; later commits only tighten the box enclosures (θ-Taylor form, Bell values from P^{(j)}, per-box a priori fallback), so the logged bounds remain valid. The exterior was recomputed after the correction of its constant.
- **Consistency rerun with the current code** (`out/cq_A_v2.log`, `out/cq_B_v2.log`; η = 20, τ = 5, capped at 1.5·10⁶ evaluations per half): J₀ ≤ 2 × 5.593671736 and J₁ ≤ 2 × 1634.135268. The closing (`out/cq_close_v2.log`) also certifies: tail ≤ 7.86·10⁻⁶, margin ≥ 9.23·10⁻⁶. The longer original runs give the sharper figures below.
- **Exterior** (`out/cq_ext.log`): J₀ ≤ 8.74·10⁻⁷² and J₁ ≤ 7.58·10⁻⁶⁴.
- **Closing inputs:** J₀ ≤ 6.860909417 and J₁ ≤ 1180.520263 (inner + exterior, rounded up).

The closing step (`out/cq_close.log`), with a = 1/64, gives:
- **Tail bound:** Σ_{m>251} |b_m| ≤ 5.77·10⁻⁶. The authors give ≤ 4.58·10⁻⁶.
- **Margin:** b₁ − γ − head − tail ≥ 1.13·10⁻⁵.

**Hence γ + Σ_{m≥3} |b_m| < b₁ is certified for the cubic–quintic scheme, with γ = 0.881545409, so that K_G ≤ π/(2γ) ≤ 1.7818666069360661.** The two reduction lemmas (near-linearity criterion and signed tensor realization; see below) were checked by hand.

### Peng (N = 501)

Inputs, all certified by us:
- δ ≥ 0.38034475, and |P(x)| ≥ U₀ = 240.3385 for |x| ≥ 8 (`out/peng_ext.log`). This agrees with his c₈·8¹¹ > 240.3385653640865.
- **Head** (`../peng2026/out/penghead_501.log`): b₁ ≥ 0.881850816423338 and Σ_{3≤n≤501}|b_n| ≤ 3.59235480199·10⁻⁸. Room for the tail: ≥ 2.496408·10⁻⁵.
- **Inner domain** (`out/peng_A.log`, `out/peng_B.log`; 6 585 618 evaluations per half): J₀ ≤ 2 × 304.1465559 and J₁ ≤ 2 × 28 609.54363. Again the two θ-halves agree.
- **Exterior** (`out/peng_ext.log`): J₀ ≤ 1.07·10⁻⁶²³⁴ and J₁ ≤ 1.73·10⁻⁶²¹⁰.
- **Closing inputs:** J₀ ≤ 608.2931118 and J₁ ≤ 57219.0873.

The closing step (`out/peng_close.log`), with a = 1/100, gives:
- **Tail bound:** Σ_{n>501}|b_n| ≤ 7.79·10⁻⁶ (B₃² ≤ 19 152, i.e. B₃ ≤ 138.4). Peng states B₃ < 107 and tail < 2.1527·10⁻⁵ for n > 301.
- **Margin:** b₁ − γ − head − tail ≥ 1.717·10⁻⁵.

**Hence γ + Σ_{n≥3}|b_n| < b₁ is certified for Peng's scheme, with γ = 5000π/17813, so that K_G ≤ π/(2γ) = 1.7813.** The certificate uses our own code throughout: Hermite coefficients, head at degree 501 instead of his 301, D³ representation, and tail integration. The reduction lemmas are the same as for the cubic–quintic scheme (below).

## Reproduce

```
gcc -O2 -I$FLINT/include d3norm.c -o d3norm -L$FLINT/lib -lflint -lmpfr -lgmp -lm
./d3norm cq:0.136419125:0.34101124:0.05276111 ext 8 > out/cq_ext.log
./d3norm cq:0.136419125:0.34101124:0.05276111 8 200.0 50.0 12000000 0 16 > out/cq_A.log 2>&1      # and 16 32 for cq_B
python3 tail_close.py 251 0.881545409 0.0000113288599277 0.881573822049599 6.860909417 1180.520263 0.125 0.1875 0.25 0.375 0.5 1 2
S=he:../peng2026/threshold_P.txt:../peng2026/rho.txt
./d3norm $S ext 8 > out/peng_ext.log
./d3norm $S 8 200.0 50.0 12000000 0 16 0.01 > out/peng_A.log 2>&1       # ~3 h; and 16 32 for peng_B
python3 tail_close.py 501 peng 0.0000000359235480199 0.881850816423338 608.2931118 57219.0873 0.0625 0.08 0.1 0.125 0.25 0.5
```

## Reduction lemmas used (stated in the preprints, checked by hand here)

- **Near-linearity criterion** (Saha et al. Prop. 6.1; Peng Lemma 2.2). If γ + Σ_{m≥3} |b_m| < b₁, the inverse majorant at γ is below 1. The proof compares the coefficients of H⁻¹ with those of the solution V of b₁V = z + E_maj(V), which has nonnegative coefficients.
- **Signed tensor realization and transfer** (Peng Lemma 2.1, Prop. 2.3). An allowable series g (‖g‖_A ≤ 1) is realized by unit vectors with ⟨L(u), R(v)⟩ = g(⟨u, v⟩), by Krivine's construction. Composing with k = H⁻¹(γ·) and with ρ, Mehler's identity in each Gaussian channel gives E[f g] = (2/π)γ⟨u, v⟩, hence K_G ≤ π/(2γ).

Both arguments are elementary. Their status is "checked by hand", not machine-checked.
