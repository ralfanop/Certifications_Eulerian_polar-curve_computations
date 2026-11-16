# Manuscript 16 v16.4 §13 — independent Schur inverse ledger

Authoritative source: `Manoscritto_16_4_Editorial_Abstract200_Sezioni14-16_20261114(1).zip`, SHA256 `c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f`. Mathematical core §§2–13 checksum `7f7585aef3a1c9a7b8a3d670474cae67ecd026c377ef544f64232bd472f7f759`.

Section 13, `eq:mixed-factor-164`: the operator Schur factorisation requires an inverse. Earlier PR #324 formalised scalar determinant factor/zero-locus. This **distinct** lemma verifies all eight component equations for both matrix products `M M⁻¹ = M⁻¹ M = I`, with
`M=[[a,b],[c,l]]`, `d=a*l-b*c ≠ 0`, and
`M⁻¹ = [[l,-b],[-c,a]]/d`.

## Scope
- Exact finite-dimensional complex algebra only. No Arb needed (zero residuals are symbolic).
- Lean theorem and `#print axioms` must pass exact-HEAD CI before marking certified.
- Open: unbounded graph-domain operator inverse, boundedness of triangular factors, compactness/Schatten ideal transfer, Atkinson index, det4 spectral equivalence.
- No changes to manuscripts or previous certificates. No merge by this agent.
