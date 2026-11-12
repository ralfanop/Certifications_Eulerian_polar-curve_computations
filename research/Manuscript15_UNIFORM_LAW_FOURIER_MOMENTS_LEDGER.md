# Manuscript 15 — Composed genuine probability-law Fourier and moment identities

**Stacked on PR #238**, the actual centred-uniform Borel probability
law. Also imports exact copies of independently kernel-certified
`UniformCosineIntegral.lean` (PR #209) and
`UniformMoments.lean` (PR #233).

Nine proposed declarations:
1. The normalized conditioned volume measure **equals**
   restricted Lebesgue volume on `Icc(-1/2,1/2)`.
2. Any real integral under the uniform law equals its set
   integral over that interval.
3. That set integral equals the oriented real interval integral
   because the endpoint singleton is Lebesgue-null.
4. Actual `∫ cos(tx) dμ_E(x) = r_E(t)`, the inherited sinc kernel.
5. Actual `∫ sin(tx) dμ_E(x) = 0`.
6–9. Actual probability-law first, second, fourth and sixth
   raw moments are `0,1/12,1/80,1/448`.

Together, these results connect the manuscript's concrete
probability law with its characteristic kernel and moments rather
than merely verifying unrelated formulas.

**Still to formalize:** the true complex-valued characteristic
function `∫ exp(i t x) dμ_E`, entire extension,
the differentiation-under-integral theorem for arbitrary competing
probability laws, existence/uniqueness of the moment recurrence, and
the formal uniqueness of the resulting measure.

**Status:** CANDIDATE until exact-head combined Mathlib build and
standard-axiom kernel CI succeeds. Importantly, passing the three
prerequisite PRs individually does not imply the new bridge is
already certified. No merges; earlier manuscripts unchanged.
