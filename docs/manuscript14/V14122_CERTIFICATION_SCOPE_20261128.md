# M14 v14.122 — source-locked certification scope (2026-11-28)

Author ZIP SHA-256: 1ce48be698d8896b4c871c2870be3ce17750f5e5a226900848023336fd8e81ad
TeX SHA-256: 3ef7c36b6e3f27ea1b7a109f6be0cf6b3adaca23d5ff2c34c308c99416383888
PDF SHA-256: 12414d02db8d6adff50d0b00fb03b4ebd7c89ae01c6e3c5f9d4c0c6644783423

New Lean modules check the actual positive-B1 convention, degree-one Bernoulli polynomial and zeta interpolation at positive integers, quartic/discriminant algebra; the ideal spin-one inverse and saturation criterion; and explicit finite Krein matrix identities. The residue-based holomorphic extension at zero and Stieltjes expansion, intrinsic angular geometry, global positivity/inertia and full spectral equivalence are not claimed by these modules. Earlier M14 records (including Eq. 211) are retained; this is not a whole-manuscript audit.

New Arb producer uses 3,600,000 working bits and 1,000,001 **fractional decimal digits**, with exact rational endpoint checks. It distinguishes printed effective moment from ideal sqrt(2) ratio. At H=-6.5 the text says no induction exists while the target is below saturation. The ideal spin-one inverse is finite for this target; the CI tests this rather than certifying the false nonexistence claim. Empirical accuracy is not claimed. No author manuscript modification.

Status: implementation submitted; CI results and exact commit audit must be checked before declaring certification.

Follow-up: actual punctured Bernoulli residue limit; actual interval Fourier integral and principal branch counterexample; characteristic determinant, Pauli double commutator and explicit global Gram factorisation/positivity added to the proposed Lean audit. These new declarations remain pending successful CI.
