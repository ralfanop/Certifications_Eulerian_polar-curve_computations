# M16 v16.4 §13 — finite-cutoff necessary-side ledger

Authoritative input: `Manoscritto_16_4_Editorial_Abstract200_Sezioni14-16_20261114(1).zip`, SHA-256 `c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f`.

Previous verified steps: PR #310 establishes the pointwise lower bound; PR #318 provides a separate **scalar** million-decimal enclosure of the mixed unperturbed fourth trace. No repetition of those certificates.

This PR proves an **exact rational difference** and two **finite** summation comparison statements for the p=3 Maxwell nearest mode. These are mathematical arithmetic/finite-sum bridges, not a proof of harmonic divergence, spectral multiplicities, or the full operator Schatten iff.

Exact identity, for x>-1:
```text
2(x²-1)/(4(x+1))³ - 1/[96(x+1)] = (x-2)/[48(x+1)²].
```

Open analytic obligations:
1. Formalise nonsummability of the shifted harmonic sequence.
2. Transfer nonsummability to the spectral series with correct temporal/spatial multiplicities.
3. Establish the p>3 sufficiency and the compact inverse on the actual graph domain.
4. Establish Fredholm index and det4 assertions independently.

Numerical status: no new transcendental numerical quantity is introduced. The historical PR #318 Arb results at 3600000 working bits / >=3400000 relative bits and 1000001 significant decimal digits are not replaced or upgraded here. CI state must be checked on the exact HEAD before any of these three Lean lemmas is called certified.
