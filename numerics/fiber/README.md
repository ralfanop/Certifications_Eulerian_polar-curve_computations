# Lower bound K_G ≥ 6π/11 (Saha et al.): independent certification of the fiber inequality

Saha, Li, Xue, Chaudhuri, Klivans, Kothari and Meka (arXiv:2608.11158v2, preprint) **claim** that K_G ≥ 6π/11 = 1.7136… . This folder certifies their only computer-assisted step, the **fiber inequality** (their Theorem 9.3, (36)), with our own method and code. It also records our hand check of the analytic steps.

## The fiber inequality

For every u : ℝ → {−1, 0, 1}, with Z ~ N(0,1), ν = E|Z| = √(2/π) and ψ₀ … ψ₃ the orthonormal Hermite polynomials,

  V(u) = Σ_{j≤3} (E[u ψ_j])² ≤ 3νβ − β²,  β = E[|Z| u(Z)²].   (36)

### Exact dual form (our reduction)

For a unit a ∈ ℝ⁴, let p_a = Σ a_j ψ_j, and set

  J(c, a) = E[(|p_a(Z)| − c|Z|)₊],  d(c) = (3ν/2)(√(1+c²) − c).

Then **(36) holds for all u if and only if J(c, a) ≤ d(c) for all unit a and all c ≥ 0**.
- **Necessity.** E[u p_a] − cβ(u) ≤ √V(u) − cβ(u) ≤ φ(β) − cβ ≤ d(c), where φ(β) = √(3νβ − β²) and d is the concave conjugate of φ. The graph of φ is a semicircle of radius 3ν/2, and its support function is (3ν/2)(√(1+c²) − c). Moreover, sup_u (E[u p] − cβ(u)) = J(c, a), attained pointwise by u = sgn(p)·1{|p| ≥ c|z|}.
- **Sufficiency.** Take a = (E[uψ_j])/√V(u). Then √V = E[u p_a] ≤ J(c, a) + cβ ≤ d(c) + cβ for every c ≥ 0. Since β ≤ ν < 3ν/2, the infimum over c ≥ 0 of d(c) + cβ is φ(β).

The authors (Appendix D) use the dual form only for c ≥ 0.993. Below that they use a different primal "high-budget" bound, spliced at β₀. **We certify the dual form on the whole half-line c ≥ 0**, so no splice is needed.

### Certificate for c ∈ [0, 8]: `fibcover.c` and `fibcore.h` (`out/fibcover_0_8.log`)

**Exact enclosure of J (`fibcore.h`).** Write p(z) − cz and p(z) + cz as cubics r₁ and r₂. Then

  J = ∫₀^∞ [(r₁)₊ + (−r₂)₊] φ + ∫_{−∞}^0 [(r₂)₊ + (−r₁)₊] φ.

Each term is integrated **in closed form**:
- **Real roots.** They are isolated in Arb (`acb_poly_find_roots` and `acb_poly_validate_real_roots`), and independently confirmed:
  - each root interval carries a certified sign change;
  - the number of real roots is fixed by the sign of the discriminant.
- **Gaps between roots.** The sign is certified at an interior point. The integrals ∫ z^k φ come from the Gaussian moment recursion with erfc.
- **Root intervals.** These widths are ~10⁻³⁰. Each is charged width × φ(0) × sup|r|.

**Covering S³ (convexity + homogeneity, no Lipschitz constants).**
- S³ modulo a ↦ −a is the radial projection of the four facets {x_f = +1} of [−1,1]⁴. A patch is the projection of a dyadic sub-cube.
- J is convex in the coefficient vector, nonincreasing in c, and homogeneous: J(c, t q) = t J(c/t, q).
- Every point of a patch is t·q, with q in the convex hull of the normalized corners v_j, 1 ≤ t ≤ T = 1/min_j⟨v_j, n⟩, and n the normalized centre.
- Hence, for c ∈ [c_L, c_U], J(c, a) ≤ T · max_j J(c_L/T, v_j), while d(c) ≥ d(c_U).
- Pairs (patch, c-band) are split until this holds.

**Result.** 29 310 pairs certified, 96 s, no failures. The worst relative margin is 6.8·10⁻⁷, near c ≈ 6.6, where the true relative margin is ≈ 4·10⁻³; the splitting stops as soon as a pair passes.

### Certificate for c ≥ 8: `fibtail.c` (`out/fibtail.log`)

As c → ∞ the inequality becomes tight at second order. The extremal direction is p₀ = (3 − z²)/√6, and c³(d − max J) → 5ν/32. A finite cover cannot reach c = ∞, so we use our own analytic reduction.

Write p = e + o, with even part e(s) = A₀ + B s² and odd part o; let O = a₁² + a₃². Take κ = 5/4, s* = κ/c and S₀ = (√6 c)^{1/2}. By the symmetry p ↦ −p we may assume A₀ ≥ 0.

1. **Integrand.** For s ≥ 0, the folded integrand is f(|e|, |o|) with t = cs, where f(x,y) = max(0, x+y−t, 2x−2t, 2y−2t). When y ≤ t this equals 2(x−t)₊ + (y − |x−t|)₊.
2. **Localization.** By Cauchy–Schwarz, |p(±s)|² ≤ K(s) = 3/2 + 3s²/2 − s⁴/2 + s⁶/6. The function K(s)/s² is convex in s². The checks K(s*) ≤ κ² (for c ≥ 8) and K(S₀) ≤ S₀⁶/6 = c²S₀² show that nothing is active on [s*, S₀].
3. **Far part (s ≥ S₀).** It is at most 2∫_{S₀}^∞ (s³/√6 − cs)φ = (4/√6)φ(S₀).
4. **Near part (s ≤ s*).**
   - Since |o| ≤ √(5O/2)·s ≤ cs, the near part is at most T₁ + T₂.
   - **T₁.** T₁ = 2∫(A₀ + Bs² − cs)₊φ ≤ 2φ₀∫₀^{s₁}(A₀ + Bs² − cs)(1 − s²/2 + s⁴/8) ds. Here s₁ is the exact root, written stably as 2A₀/(c + √(c² − 4A₀B)).
   - **T₂.** u(s) = |e| − cs decreases with slope at least c − 2|B|s*. Hence T₂ = ∫(|o| − |u|)₊φ ≤ φ₀ · (5/2)Oκ²c⁻² / (c − 2|B|κ/c).
5. **Margin.** In the variable u = 1/c²,
   c³(d − T₁ − T₂ − T₃) = φ₀(3/2)(1 − r²cos²f)/u + h′(ξ) − c³T₂ − c³T₃, with ξ ∈ [0, u].
   Here h is explicit, and its derivative needs no differentiation of the root, because the integrand vanishes there. It is enclosed on the whole interval [0, u]. The parameters are (A₀, B) = r·(√(3/2) cos f, sin(f − atan(1/√2))/√2).
6. **Branch and bound.** Interval branch and bound on f ∈ [−π/2, π/2], r ∈ [0,1], u ∈ [0, 1/64]: 2 224 boxes, all positive.

**Sanity check.** On 20 000 random (a, c ≥ 8), the bound T₁ + T₂ + T₃ was always ≥ the exact J. This is a numerical check, not part of the proof.

### Result

**The fiber inequality (36) is certified by us for every ternary u.** Our method differs from the authors' throughout:
- a dual form valid for all c, instead of their primal/dual splice;
- an exact closed-form J with convexity on S³ patches, instead of their Christoffel envelopes and 480 panels;
- our own analytic tail with mean-value enclosure in u, instead of their local/away charts and moving-cutoff lemma.

We did not use their scripts.

## The rest of the proof of K_G ≥ 6π/11 (checked by hand, not machine-checked)

- **§9.1 (agreement–disagreement substitution).** B₁ ≤ 2‖P₁h‖² − ‖P₃h‖² + ‖P₃k‖². Correct.
- **§9.3, Lemma 9.1 (rearrangement).** sup E[A(S³ − 3S)] = −νΔ(x). We redid the Gaussian moments and A* = sgn(S) sgn(S² − r²). Correct. This gives Corollary 9.2.
- **§9.4.**
  - (34)–(35): orthogonal splitting and Bessel. Correct.
  - Theorem 9.4: E|S|k² ≤ ν(1 − x), Jensen, and monotonicity of 3νt − t². Correct, given (36).
  - Theorem 9.5: bathtub argument. Correct.
- **§9.5 (three ranges).** Correct.
  - Low range: 2r₋² + π/2 = 2/3 − 1/√3 + π/2 < 11/6.
  - Middle range: algebra.
  - High range: Δ ≥ 3x − 2, via (1 − t) + t log t ≥ 0, and (3x−2)² − (6x² − 6x + 1) = 3(1 − x)².
  - Exact checks in `scalar_checks.py` (`out/scalar_checks.log`).
- **§10, Proposition 10.2.** a₁ = 1/b₁, a₃ = −b₃/b₁⁴. The identity for M_H(11/12) and 2(11/12)³ > 1 are checked exactly.
- **§11, Lemma 11.2.** It uses the construction of Naor–Regev, *Krivine schemes are optimal*, Proc. Amer. Math. Soc. 142 (2014), 4315–4320 (peer-reviewed). We checked the logic of the transfer:
  - Grothendieck's inequality and LP duality give exact finite sign representations of ⟨x_i, y_j⟩/K_G.
  - Step functions on fine partitions give uniform approximation.
  - With Σ|b_m| ≤ π/2, uniform convergence on [−1,1] implies coefficientwise convergence.
  - Affine inequalities pass to mixtures and limits.

  **Still to do:** a line-by-line comparison of the authors' quotation of NR14 (eqs. (4)–(6), the choice of c_k, Lemma 2.1) with the published text.

## Reproduce

```
gcc -O2 -I$FLINT/include fibcover.c -o fibcover -L$FLINT/lib -lflint -lmpfr -lgmp -lm
gcc -O2 -I$FLINT/include fibtail.c  -o fibtail  -L$FLINT/lib -lflint -lmpfr -lgmp -lm
./fibcover 0 8 64 > out/fibcover_0_8.log      # ~100 s
./fibtail > out/fibtail.log                   # < 1 s
python3 scalar_checks.py > out/scalar_checks.log
```
