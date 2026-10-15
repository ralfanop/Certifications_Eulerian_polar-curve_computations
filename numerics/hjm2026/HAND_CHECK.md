# Hand check of the lower bound K_G ≥ 1773/1000 (Heilman, Jones, Malavolta, arXiv:2610.10477v1)

Checked step by step on 15 Oct 2026. Numbers in brackets are the preprint's equation numbers. "Verified by computer" marks the two small exhaustive or numerical sanity tests we ran (see the end); every other step is checked by hand.

## 1. From a Hermite projection game to K_G (Theorem 2.2, left inequality; Lemma 2.6)

Let Q = Σ_m q_m Π_m on L²(γ_n), with q_1 = 1, |q_m| ≤ 1 and q_{2m} = 0.

- **Discretization.** Take simple functions f = Σ_i 1_{A_i} u_i and g = Σ_j 1_{B_j} v_j with unit vectors u_i, v_j. Then ⟨f, Qg⟩ = Σ a_ij⟨u_i, v_j⟩ with a_ij = ⟨1_{A_i}, Q 1_{B_j}⟩. Sign choices constant on the cells are Boolean functions, so the matrix OPT is at most OPT(Q). Hence K_G ≥ (Σ a_ij⟨u_i, v_j⟩)/OPT(Q). Q is bounded, so step-function approximation in L² passes to SDP(Q)/OPT(Q). This is the same bridge as in Davie's proof (Lean: `FiniteVectorBridge`).
- **SDP(Q) ≥ 1 − o_n(1).** Take f = g = x/‖x‖. By oddness Π_0 f = 0, and Σ_m ‖Π_m f‖² = 1. Hence ⟨f, Qf⟩ ≥ ‖Π_1 f‖² − Σ_{m≥3} ‖Π_m f‖² = 2‖Π_1 f‖² − 1. By symmetry Π_1 f_i = E[x_i²/‖x‖] x_i, so ‖Π_1 f‖² = (E‖x‖)²/n → 1.
- **Odd functions suffice (Lemma 2.6).** ⟨f, Qg⟩ = ⟨f_odd, Q g_odd⟩, where f_odd and g_odd take values in {−1, 0, 1}. Filling the zeros with ±a, for an odd Boolean a, gives odd Boolean f_±, g_± whose average is f_odd and g_odd. One of the four pairs is at least as large.

Hence **K_G ≥ 1/v_∞(q)**, where v_∞(q) = sup_n sup over odd Boolean f, g of ⟨f, Qg⟩.

## 2. Proposition B.1 (one-variable criterion)

Put h = (f+g)/2 and k = (f−g)/2. Then h² + k² = 1, ⟨Π_m f, Π_m g⟩ = ‖Π_m h‖² − ‖Π_m k‖², and ‖Π_m f‖² + ‖Π_m g‖² = 2(‖Π_m h‖² + ‖Π_m k‖²).

- **Rotation.** The operator Q commutes with orthogonal maps, so we may assume Π_1 h = √(2/π)·x·z_1. Here x ∈ [0, 1], because E[z_1 h] ≤ E|z_1| = √(2/π).
- **(B.12).** Put σ_r = f(cos(rπ/N)U + sin(rπ/N)V). Then σ ∈ {±1}^N and, by oddness, σ_{r+N} = −σ_r. By Mehler, E[σ_r σ_{r+j}] = Σ_{m odd} cos^m(πj/N) ‖Π_m f‖². The sign vector is admissible in (B.2) pointwise, so Σ_m Γ_m^{(N)} ‖Π_m f‖² ≤ B_N. The same holds for g. Averaging and summing over N = 7, 9 gives Σ_m Γ_m (‖Π_m h‖² + ‖Π_m k‖²) ≤ B.
- **(B.13).** We have the identity ⟨f, Qg⟩ = Σ Γ_m(‖h_m‖² + ‖k_m‖²) + Σ (q_m − Γ_m)‖h_m‖² + (−q_m − Γ_m)‖k_m‖².
  - The first sum is at most B.
  - The m = 1 term of the h-part is (1 − Γ_1)(2/π)x². The k-part at m = 1 is β_1 = −1 − Γ_1.
  - For m > 21 we have q_m = 0 and Γ_m ≥ 0, from (B.6) and §6 below, so those terms are ≤ 0 and are dropped.
- **Fibres.** Write z = (S, Y). The S-coefficients of h(·, Y) are h_p(M(Y))_j = E_S[ψ_{2j+p}(S) h], of degree 2j + p ≤ 21. A Hermite coefficient of h of total degree m is a coefficient of ψ_{2j+p}(S)ψ_η(Y) with 2j + p + |η| = m. Hence Σ_m α_m‖Π_m h‖² = Σ_η Σ_p û_p(η)ᵀ D_{p,|η|}(α) û_p(η), with û_p(η) = E_Y[h_p(M(Y)) ψ_η(Y)]. The same holds for k with β.
- **(B.7).**
  - For 1 ≤ |η| ≤ 21: D_{p,|η|} ⪯ H_p + εI.
  - For |η| > 21: D = 0 ⪯ H_p.
  - For η = 0, p = 0: D_{0,0}(α) = 0, since the even entries vanish.
  - For η = 0, p = 1: apply the block inequality to (z, −1). This gives zᵀD_{1,0}z ≤ zᵀH_1z − 2ℓ_hᵀz + c_h + ε + ε‖z‖².
- **Assembly.** Parseval in Y turns Σ_η û_pᵀ H_p û_p into E_Y[h_pᵀ H_p h_p], and −2ℓᵀû_1(0) into E_Y[−2ℓᵀh_1]. The ε‖·‖² costs total at most ε E(h² + k²) = ε, by Bessel in S. Adding t·(h_1)_0 inside F and subtracting its mean t√(2/π)x, which is equal in expectation, gives ⟨f, Qg⟩ ≤ E_Y F(M(Y)) + Φ(x) ≤ C + Φ(x), with the cost 3ε included in Φ.
- **Endpoints.** Φ is convex because 1 − Γ_1 > 0. Its maximum on each covering interval is therefore at an endpoint, and (B.11) gives v_n(q) ≤ 1000/1773 − 10⁻⁹ for every n.

## 3. Section B.2, reduction of F ≤ C to signs

- **(B.15).** R ⪰ 0, so F is convex. With ξ = 2RM + ℓ = ∇F(M), we get F(M) − F(Bσ) ≤ ξᵀ(M − Bσ). Choose σ = sign(Bᵀξ), so that ξᵀBσ = ‖Bᵀξ‖₁. Also ξᵀM = Σ_i ∫ p_i h_i dγ ≤ Σ_i ∫ |p_i| dγ, since |h_i| ≤ 1.
- **Interpolation.** On each panel, I₂p = Σ λ_ν c_ν(p), with Bernstein weights λ_ν ≥ 0 and c_1 = 2p(mid) − (p(a) + p(b))/2. Hence ∫|I₂p| dγ ≤ Σ_ν |c_ν(p)| ∫λ_ν dγ. Endpoint columns shared by adjacent panels are positive multiples of the same functional, so they merge without loss. The result is ‖Bᵀξ‖₁.
- **Peano bound (B.16).** H(s) = u²(3 − 4u)/24, with u = min(s, 1−s), satisfies H(0) = H(1) = H′(0) = H′(1) = 0 and −H‴ = sign(1/2 − s), and its maximum is H(1/2) = 1/96. On a panel of width h, rescaling gives the factor h³, and the Gaussian density varies by at most e^{h·max|s|}.
- **Error allowance (B.17).**
  - Tail beyond |s| > 9: Cauchy–Schwarz gives ∫_T |ψᵀξ| dγ ≤ √γ(T) ‖G_T^{1/2} ξ‖.
  - Panels: ∫_J |p‴| dγ ≤ √γ(J) ‖Q_J^{1/2} ξ‖.
  - Uniform bound in M: ξ[i] = ℓ[i] + 2Σ_j R[ij] M[j], with M[j] = Σ_L ∫_L ψ h_j dγ. Each piece is bounded by ‖R_0 ∫_L ψh‖² ≤ γ(L) Tr(R_0 G_L R_0ᵀ) for |h| ≤ 1, which gives A(Q; P).
- **Rounding (B.18).** Put x = Bσ and x̄ = B̄σ, with |x| ≤ b and |x − x̄| ≤ δ. Then xᵀRx − x̄ᵀRx̄ = (x − x̄)ᵀR(x + x̄) ≤ δᵀ|R|(2b + δ). The terms x̄ᵀ(R − R̄)x̄ and those in ℓ are bounded in the same way. Rounding the 2⁴⁴-scaled coefficients to integers costs the sum of the absolute rounding errors, because |σ-monomials| = 1.

## 4. Graph bound and sign fixing

Vertices are j⁺, j⁻ and two terminals of sign ±1. For a_jk > 0, the edges (j⁺, k⁺) and (j⁻, k⁻) have capacity |a_jk|; for a_jk < 0, the edges are (j⁺, k⁻) and (j⁻, k⁺). The edges (j⁺, T_{sign a_j}) and (j⁻, T_{−sign a_j}) have capacity |a_j|.

- **Identity.** For the consistent cut x(σ) = (σ, −σ), each pair of edges contributes 2|a|·[disagreement]. Hence a_jkσ_jσ_k = |a_jk| − (cut part), and similarly for a_jσ_j. Therefore P(σ) = a_0 + Σ|a_j| + Σ|a_jk| − cap(x(σ)). Minimizing over all cuts, not only consistent ones, gives the upper bound (B.20).
- **Certification of the minimum cut.** A feasible flow whose value equals the capacity of a cut certifies by weak duality that the cut is minimal. The verifier checks capacities, conservation and equality.
- **Sign fixing (persistency).** Let x be a minimum cut and z a consistent cut of a maximizer of P. Let x̄(v) = −x(v̄) be the reflected cut, where v̄ swaps j⁺ and j⁻ and swaps the terminals. The graph is invariant under this swap, so cap(x̄) = cap(x).
  - Take a, y, b as the vertexwise minimum, median and maximum of (z, x, x̄). The terminals are fixed in all three.
  - For each edge, the disagreements of a, y and b total |p_u − p_v|, where p counts the positive labels. This is at most the original total.
  - Hence cap(y) ≤ cap(z) + 2 cap(x) − cap(a) − cap(b) ≤ cap(z), because x is a minimum cut.
  - y is consistent: y_{j⁻} = med(−z_{j⁺}, x_{j⁻}, −x_{j⁺}) = −y_{j⁺}.
  - Wherever x is consistent, x̄_{j⁺} = x_{j⁺}, so y_{j⁺} = x_{j⁺}.

  Hence y gives a maximizer of P that obeys every fixing.
- **Rectangle certificates (B.21).** On a leaf R, the added term μ_k(u_k − l_k)(h_k − u_k) is ≥ 0 for every σ with u ∈ R. So a bound for the augmented polynomial over all σ bounds P on that leaf. Expanding u_k² with σ_j² = 1 gives exactly the two constants −μ_k l_k h_k and −μ_k‖v_k‖₂²/‖v_k‖₁². Each contribution rounded to the nearest integer costs at most 1/2.
- **Exclusion of a leaf.** For σ_{j0} = 1 we have wᵀσ ≤ w_{j0} + Σ_{j≠j0} |w_j|. If the minimum of a‖v_1‖₁s_1 + b‖v_2‖₁s_2 over R, attained at a corner, exceeds this, then no σ lands in R.

## 5. The infinite part of (B.6), via (B.22)

For N = 7, 9 and 1 ≤ j ≤ (N−1)/2, we have c_j = cos(πj/N) > 0 and c_j decreasing. Hence Σ_j w_j c_jᵐ = c_1ᵐ(w_1 + Σ_{j≥2} w_j(c_j/c_1)ᵐ) ≥ c_1ᵐ η_N > 0, so Γ_m ≥ 0 for every m. The value 1 − Γ_1 > 0 is checked exactly by the verifier.

## 6. Conclusion

Every analytic step from the finite certificate to K_G ≥ 1773/1000 is correct. The finite certificate itself was re-executed by us and accepted (`lower_run/`).

## Sanity tests (verified by computer, not part of the proof)

- **Graph identity, bound (B.20) and sign-fixing lemma.** We checked them exhaustively on 300 random quadratic pseudo-Boolean functions with N ≤ 6 variables, over all 2^{2N} cuts: 0 violations.
- **Peano bound (B.16).** Over 300 random degree-8 polynomials, ∫|p − I₂p| / ((1/96)∫|p‴|) ≤ 0.651, consistent with the bound.
