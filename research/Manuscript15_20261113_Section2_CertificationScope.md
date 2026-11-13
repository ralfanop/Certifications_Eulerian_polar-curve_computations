# Manuscript 15, editorial source of 13 November 2026 — Section 2 certification audit

**Authoritative text for this inventory:** the 30-page PDF and `15.tex` in
`Manuscript_15_Editorial_Review_Maldacena2023_20261113(2).zip`.
SHA-256 of `15.tex`: `ccfcef205a7fc38db4386142a9173d0a8a60121ab58ae5ed1713f4219b1e200d`.

This audit is *source-scoped*: it supersedes references to the older
14-environment manuscript matrix **for §§2.1–2.7 only**. It does not change,
delete, rewrite, or reinterpret any manuscript or figure. The word "CERTIFIED"
is reserved for the stated declarations on a CI-tested exact SHA, never for
the entire proposition merely by association.

| Current subsection | Statements actually present | Relevant certified source / work | Outstanding precise obligations |
|---|---|---|---|
| **2.1 — kernel and cycloidal coordinates** | Exact cycloidal reconstruction; Speed and curvature realisations, including speed, curvature, radius and recovered sinc | Existing `Manuscript15/CycloidalReconstruction.lean` verifies `X,Y` coordinate reconstruction and the kinematic relation. Draft **#288** original head `8a8dbe1a6c9a97a51aaace81c3c4f68f127d5754` passed workflow **43502822152**, checking the real squared-speed, positive speed under sine-sign hypothesis, derivative determinant and curvature quotient. | The revised #288 also proposes explicit `HasDerivAt` proofs for both coordinates and velocity jets; certify **new head separately**. Link the resulting jet identities directly to the intrinsic parametric speed and curvature definition, including the open arc `0<t<2*pi` and the endpoint singularity exclusions. |
| **2.2 — Fredholm, Langevin, special points** | Fredholm determinant of the genuine Dirichlet inverse; entire special function identity; logarithmic derivative and actual resolvent trace; imaginary-point corollary, area/vertex identities | Exact-source tested #273 covers genuine Fredholm–Langevin special scalar/logarithmic derivative track; #274 outward Arb enclosures at 10000 working bits, minimum 9990 rigorously checked relative bits. Existing analytic sine/hyperbolic identities from previous PRs apply only within their exact theorem hypotheses. | Exact differential-L² operator-domain equivalence and physical Dirichlet resolvent identification of the diagonal inverse; full abstract trace-resolvent bridge; exact statement-level re-audit of all equalities and branch conventions in current Theorem 2.2 and its corollary; possible area and vertex expression gaps. |
| **2.3 — four representations** | Complex-analytic `r_E(2ix)`, genuine Fredholm determinant, sphere `S²` exponential average, invariant pure-state `CP¹` exponential average; logarithmic derivative and duplication | The scalar and true trace-class determinant parts have partial inherited certified coverage. | Explicit normalized `S²` measure and push-forward to the uniform `[-1,1]` law; Bloch map and normalized invariant `CP¹` probability, with rigorous measure-preserving equality; differentiation under integral; genuine direct-sum factorisation, rather than only scalar product coincidences. |
| **2.4 — Eulerian apex and Fourier triangle** | Exceptional angles `alpha3=alpha5=2 arccot 2`, `alpha_n>alpha3` for all odd `n>=7`; two-term asymptotic cited from M11; triangular profile Fourier series, sign derivative and Plouffe/Sprugnoli inverse-central-binomial identities | Draft **#290**, head `b061663621bd4d6e78142e882746d9648708dbef`, passed workflow **43503214410**: exact rational `s3=s5=2, s7=35/18`, rigorous Arb 10000-bit interval for `5/sqrt(2*pi)+40/(9*pi^10)<2`, **minimum 9988 certified relative bits** across claimed nonzero enclosures. | Formalize global Fourier integral upper bound and the uniform decrease for even `N>=10`, giving the *infinite* strict `s_n<2` theorem; import M11 two-term asymptotic only with a genuine theorem; construct periodic triangular function, Fourier coefficient/uniform convergence and pointwise sign derivative; formalize inverse-binomial beta integral and infinite series as mathematical equalities. A successful Arb test at N=10 alone does **not** prove the universal inequality. |
| **2.5 — conformal Cayley half-angle** | Null-cone chart, `q=tan(tau/2)`, inverse `Omega(q)`, complex exponential, two distinguished angles and limiting `r_E(Omega)` | #288 includes precisely the real rational Cayley unit-circle coordinates and `q=1/2` values, but these are not a proof of the null-cone geometry or complex exponential identities. | Define null cone with chosen projectivisation and coordinate chart; prove half-angle and chart inverse with proper domains; complex exponential and large-q limit; distinguish geometric coordinate identities from proposed physical/dynamical interpretations, which the manuscript does not assert as theorems. |
| **2.6 — Laplace, Cayley matrix, Segal unitime** | Laplace transform of true Eulerian sinc for **every** `lambda>0`; `lambda=1,pi/2` values; scalar complex 2×2 Cayley transform, `q=1/2` values, unitime and conformal factor | #288 exact-source initial run certifies the *rational real and imaginary Cayley coordinate algebra*, unit-circle identity, `q=1/2` components `(-3/5,-4/5)` and `4/5` conformal factor, not the integral. | Rigorous Fubini/integrability argument for `∫_0^∞ exp(-lambda*t)r_E(t) dt=2 atan(1/(2lambda))`; derive both specialisations, genuine complex-matrix inverse/exponential identity; separate Segal's normalization hypothesis from the purely algebraic identities. |
| **2.7 — reconstruction Wasserstein-1 estimate** | `|Xmu-Xnu|<=2a*t²*W1`, `|Ymu-Ynu|<=a*|t|³*W1`, compact-time uniform continuity for symmetric finite-first-moment laws | #240 proves pointwise cosine/sine phase bounds, #285–287 finite coupling bounds. Draft **#291**, head `27701f7372f5b4dad35241efc325ac5ac427f5f2`, workflow **43503627135 SUCCESS**, proves *actual measure-level Bochner integral* transport bound, unit-Lipschitz tests, and sine/cosine Fourier coupling integrals with explicit integrability. | Identify arbitrary coupling marginals with characteristic-function integrals; prove the coupling cost/infimum step for Mathlib's `W1` and moment assumptions; compose with the already kernel-proved `X,Y` algebraic estimates and derive uniformity on compact time intervals. No converse is asserted. |

## Certification discipline

* Every Lean upgrade requires **an exact-head successful** pinned CI build and
  `#print axioms` for the genuinely relevant declarations. Standard Lean
  `propext`, `Classical.choice` and `Quot.sound` may occur; no `sorryAx`,
  nonstandard unproved axiom, or hidden numerical fallback is permitted.
* Every new nonzero Arb interval needs **10000-bit working precision** and
  independently checked **at least 8182 rigorously certified relative bits**.
  Exact rational identities are established symbolically; outward interval
  overlap alone is never treated as an equality proof.
* Exclude Section 6 physical conjectures from mathematical closure criteria.
  Do **not** transfer Manuscript 14 modular-`j` certification obligations to
  Manuscript 15 unless the current source actually contains them.
* This inventory does not authorize merge. No previous manuscripts, V007,
  V097, or figures are changed.

**Priority for subsequent proof work:** the complete §2.7 marginal/Wasserstein
bridge; §2.1 analytic jet/domain interpretation; §2.6 exact Laplace integral;
§2.4 general odd-order inequality and Fourier triangle; §2.5 half-angle
chart; §2.3 normalized geometric probability measures and §2.2 true
unbounded-operator trace/resolvent bridge.
