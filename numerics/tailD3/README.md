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
- **Inner domain** (`out/cq_A.log`, `out/cq_B.log`): J₀ ≤ 2 × 3.430454708 and J₁ ≤ 2 × 590.2601312. The two θ-halves give identical results, as expected from the symmetry θ → π − θ.
- **Exterior:** J₀ ≤ 6.6·10⁻⁷³ and J₁ ≤ 1.6·10⁻⁶⁵.

The closing step (`out/cq_close.log`), with a = 1/64, gives:
- **Tail bound:** Σ_{m>251} |b_m| ≤ 5.77·10⁻⁶. The authors give ≤ 4.58·10⁻⁶.
- **Margin:** b₁ − γ − head − tail ≥ 1.13·10⁻⁵.

**Hence γ + Σ_{m≥3} |b_m| < b₁ is certified for the cubic–quintic scheme, with γ = 0.881545409, so that K_G ≤ π/(2γ) ≤ 1.7818666069360661.** The two reduction lemmas (near-linearity criterion and signed tensor realization; see below) were checked by hand.

### Peng (N = 501)

Certified so far:
- δ ≥ 0.38034475;
- |P(x)| ≥ U₀ = 240.3385 for |x| ≥ 8, which agrees with his c₈·8¹¹ > 240.3385653640865;
- head Σ_{3≤n≤501} |b_n| ≤ 3.59·10⁻⁸.

Room for the tail: 2.496·10⁻⁵. The run for the inner domain is in progress.

## Reduction lemmas used (stated in the preprints, checked by hand here)

- **Near-linearity criterion** (Saha et al. Prop. 6.1; Peng Lemma 2.2). If γ + Σ_{m≥3} |b_m| < b₁, the inverse majorant at γ is below 1. The proof compares the coefficients of H⁻¹ with those of the solution V of b₁V = z + E_maj(V), which has nonnegative coefficients.
- **Signed tensor realization and transfer** (Peng Lemma 2.1, Prop. 2.3). An allowable series g (‖g‖_A ≤ 1) is realized by unit vectors with ⟨L(u), R(v)⟩ = g(⟨u, v⟩), by Krivine's construction. Composing with k = H⁻¹(γ·) and with ρ, Mehler's identity in each Gaussian channel gives E[f g] = (2/π)γ⟨u, v⟩, hence K_G ≤ π/(2γ).

Both arguments are elementary. Their status is "checked by hand", not machine-checked.
