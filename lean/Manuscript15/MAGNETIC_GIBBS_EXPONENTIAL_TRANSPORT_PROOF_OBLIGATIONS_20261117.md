# M15 §8.4: exact exponential-to-odd-lattice transport identities (analytic proof, NOT Lean-certified)

Date: 2026-11-17. This is a standalone proof-obligation note, not an amendment to the author's manuscript, and not an Arb numerical certificate. It is intended to bridge the integrated M15 graph-coupling/rounding work (#348, #359, #360) to the actual source and target measures. No theorem below is claimed to have passed Lean.

Fix a real parameter λ>0. Let μ_λ on [0,∞) have density λ exp(-λx) dx. Let T(x)=2⌊x/2⌋+1, and let ν_λ=Σ_{n≥0}(1-q)q^n δ_{2n+1}, q=exp(-2λ)∈(0,1).

**Pushforward law.** For each n≥0, T^{-1}({2n+1})=[2n,2n+2). Thus μ_λ(T^{-1}({2n+1}))=exp(-2λn)-exp(-2λ(n+1))=(1-q)q^n. The cells partition [0,∞), proving T_#μ_λ=ν_λ (including normalization). The graph law (id,T)_#μ_λ is therefore a coupling.

**W1 optimality.** For any y in {1,3,5,...}, |x-y|≥dist(x,{1,3,5,...})=|x-T(x)| except at cell boundaries, where either nearest neighbor is allowed. Integrating against any coupling with first marginal μ_λ yields a lower bound E|X-T(X)|, attained by the graph coupling. Consequently W1(μ_λ,ν_λ)=E|X-T(X)|. The same pointwise nearest-site inequality for squared distance proves W2²=E|X-T(X)|², attained by the same graph coupling (both laws have finite second moments).

**Explicit integrals.** Write x=2n+u, 0≤u<2. For k=1,2,
 E|X-T(X)|^k = [λ/(1-exp(-2λ))] ∫_0^2 exp(-λu)|u-1|^k du.
Splitting at u=1 and integrating by parts gives
 W1(μ_λ,ν_λ) = 1 - (1-exp(-λ))/(λ(1+exp(-λ))) = 1 - tanh(λ/2)/λ,
 W2(μ_λ,ν_λ)^2 = 1 + 2/λ² - (2/λ)coth(λ).
These are exact real-variable identities for every λ>0, not floating-point evaluations. In particular W2 is the nonnegative square root of the displayed positive expectation.

**W∞.** The graph coupling has |X-T(X)|≤1 almost surely, hence W∞≤1. For every 0<r<1, the union of intervals on which dist(x,{1,3,...})>r has positive μ_λ measure (already inside (0,1-r)). Any coupling must move those source points by more than r, because its second marginal is supported on the odd lattice. Thus its essential supremum cost is ≥1, proving W∞(μ_λ,ν_λ)=1. This exact limiting-law statement does NOT imply W∞ convergence of the magnetic approximants.

**Lean implementation obligations.** (1) Measurability of T and exact half-open preimages; (2) exponential integral on each cell and geometric normalization; (3) equality of measures by their singleton masses on the countable odd lattice; (4) integrability of |x-T(x)| and its square, plus finite moments of ν_λ; (5) coupling marginal identities using the already merged graph-law lemmas; (6) nearest-site inequality, primal lower bound and attainment for p=1,2; (7) summation of nonnegative cell integrals by Tonelli; (8) the two closed-form integrals; (9) the lower bound for W∞ via positive mass on sets at distance >r. All must be discharged without sorry, new axioms or an unproved analytic summability assumption.

**Scope limits.** No magnetic Friedrichs operator, compact resolvent, diamagnetic inequality, heat-trace bound, finite-h magnetic Gibbs law, or Wp convergence has been established here. Identifying the author's actual parameterization with λ and q requires checking the exact formulas in the authoritative 74-page ZIP. No FLINT/Arb computation, 3,600,000-bit accuracy assertion, or million-digit rounding cell is claimed. Keep the existing numerical certification register unchanged until an actual exact-HEAD run proves those assertions.
