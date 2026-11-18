# Manuscript 12 — numerical certification audit (provisional)
 
Snapshot: 2026-11-18. This is a work-in-progress audit, **not a declaration of complete certification**. No manuscript source is modified.

Authoritative manuscript ZIP SHA-256: `7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860`. The two supplied duplicate uploads had identical SHA-256.

## Acceptance criterion

Arb working precision 3,600,000 bits; relative enclosure accuracy at least 3,400,000 bits; strict unique rounding of the enclosed value to 1,000,001 significant decimal digits. Relative enclosure accuracy alone is not a substitute for checking that both endpoints round identically. Significant digits are distinguished from fixed decimal places. Published-table rounding and million-digit certification are separate tests.

## Verified individual checks

28 successful checks (not asserted to be 28 distinct constants); the logs below report the indicated relative accuracy in bits. The accepted runs include strict unique decimal rounding checks.

| Evidence | Quantity | Relative bits |
|---|---|---:|
| #318 | r_E / π | 3599998 |
| #318 | −2 / π | 3599998 |
| #318 | Eulerian angle in degrees | 3599996 |
| #318 | d_E | 3599997 |
| #318 | β₃ | 3599996 |
| #318 | C_B | 3599997 |
| #318 | s(1/4) | 3479999 |
| #318 | η(1/4) | 3479992 |
| #384 | eq:triangle-density-eulerian — 2/π² | 3599996 |
| #384 | eq:valean-double-eulerian — √8/π | 3599997 |
| #384 | eq:plouffe-general — f(1/2) | 3599997 |
| #384 | eq:plouffe-euler-angle — radians | 3599997 |
| #384 | eq:sigma-one — Ω(1/2) | 3599998 |
| #384 | eq:beta2-moment — β₂ | 3599998 |
| #384 | eq:beta2-moment — integral 2G | 3599998 |
| #384 | eq:beta3-moment — π³/8 | 3599996 |
| #384 | eq:zeta3-moment — ζ(3) | 3599998 |
| #384 | eq:zeta3-moment — integral 9ζ(3)/8 | 3599997 |
| #384 | cor:geometry-moment — −56ζ(3)−2π³ | 3599997 |
| #384 | eq:blagouchine — 2 log(4/π) | 3599995 |
| #384 | eq:catalan-q — 4G/π | 3599997 |
| #384 | eq:moments-log3 | 3599998 |
| #384 | eq:lambertian-45 — log(1+√2) | 3599998 |
| #384 | eq:lambertian-45 — L₈(1) | 3599997 |
| #384 | eg:eq:D12 — √5/12 | 3599997 |
| #384 | eg:eq:D12 — 2/√5 | 3599997 |
| #384 | eg:eq:Dproved — 2/(π²+1) | 3599997 |
| #384 | eg:eq:15proved — 1/(π²+1) | 3599997 |

- [PR #318](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/318), pinned commit `cbdef6bc71522d4a49186fcb07a13c01df31a513`, [job log](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43701995391/job/132774933850), [artifact](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43701995391/artifacts/14156991950).
- [PR #384](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/384), pinned commit `5df7554b2eb37e7b8b051f996f4b4c4572c53ac5`, [job log](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44312456543/job/134829827657), [artifact](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44312456543/artifacts/14430751913).

## Historical coverage and authoritative-source reconciliation

The manuscript itself cites the [historical certification record](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/3282b7f41fd8b9bdf09e5e5142ee6b721e0bf8dd/docs/manuscript12/Manuscript12_Certification.md) at commit `3282b7f4`. Section 6 reports validated Arb rounding cells for all 25 printed Table 1 entries and the displayed scalar values. This is evidence at the **printed** precision, not evidence at 1,000,001 digits. The same record reports exact Lean verification of seven profile expansion coefficients, thirteen norm and reciprocal corrections, and the fixed-degree coefficient results. The 26 displayed rational corrections (13 each in `eg:eq:expanded-norm` and `eg:eq:expanded-vacuum`) are exact mathematical quantities and should be cross-referenced as such, not mistaken for uncertain numerical approximations.

The authoritative TeX identifies Table 1 as `tab:ul-beta`: five rows, five numerical columns, including F(t), three scaled errors for M=100,200,400 and the unscaled error for M=400. Its printed table contains 25 values; the 15 finite Lanczos inputs are intermediate values, not 15 extra printed cells.

The manuscript's Data Availability statement still cites the historical record. This audit supplements it without changing the submitted text or replacing that record. Before final release, reconcile the exact identity/approximation inventory (including the Rabotnov specializations and phase coefficient) and verify fixed decimal-place rounding separately if that is required by the release specification.

## Open certification dependencies

| Dependency | Scope | Snapshot status |
|---|---|---|
| [#385](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/385) | Five profile values, t = 1/4, 1/2, 1, 2, 4 | Five pilots passed; five full precision jobs running |
| [#386](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/386) | Fifteen finite Lanczos coefficient inputs, M = 100, 200, 400 | Exact-versus-Arb pilot passed; three full precision jobs running |
| [#387](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/387) | 20 table error cells, using the eight source artifacts from #385 and #386 | Combiner prepared; awaiting full inputs |
| [#390](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/390) | Interval Newton profile acceleration | 1,024-bit benchmarks passed at t=1/4 and 4; 4,096-bit benchmark at t=1/4 passed; t=4 still pending; not a substitute for full certification |

Pinned inputs:
- #385 `7f2ab3c805e599680579d0c8ec68c48e648b6b7c`, [run 44312751989](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44312751989).
- #386 `8fc451ce053a769087fb25ed16289018890bc926`, [run 44313014167](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44313014167).
- #387 `e16a5e26afcafdb5ee05f0ece2f3884da61acea5`.
- #390 `c790ff3915aee28ad67a054d648b18e6b16f502e`, [run 44315118699](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44315118699). At 1,024 bits the paired benchmark yielded speedups 2.90x and 2.73x; at 4,096 bits, t=1/4 yielded 3.62x (75.06s versus 20.74s); this is not a runtime prediction at 3,600,000 bits.

## Release gate

- [x] Record authoritative archive identity.
- [x] Record successful historical and supplementary constant runs.
- [ ] Retrieve all five full precision profile artifacts and verify their rounding and provenance.
- [ ] Retrieve all three full precision finite Lanczos artifacts and verify all fifteen inputs.
- [ ] Execute the table combiner, verify each of the twenty derived error cells and their agreement with the published table.
- [ ] Reconcile the complete numerical-claim inventory against the authoritative manuscript, including distinction between exact identities, printed approximations, significant-digit rounding and fixed decimal-place rounding where relevant.
- [ ] Record exact run/job IDs, artifacts, achieved accuracy, decimal output hashes, and any exceptions. Only then issue a final certification statement.

Lean formalization, where available, is complementary evidence; this audit does not assert that Lean has formally proved the Arb execution or that every printed claim is covered.

## 2026-11-18 14:15 UTC incremental verification

- **PROVED (Lean CI)**: PR #377 was merged (merge commit `4634f4d902286a67f719242cf5e92febac04ee6c`); exact original HEAD `3d1ecb565fe71a81ddf715b101ae2ca0a98b63e8` has two successful workflows, runs [44263029044](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44263029044) and [44263028985](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44263028985). These validate the stated shell-model obligations, not genuine Maxwell/Dirac operator identification. PR #372, #373, #376 are also merged, but their analytic statements must not be relabelled Lean-proved without separate checks.
- **CERTIFIED (Arb)**: PR #386, pinned HEAD `8fc451ce053a769087fb25ed16289018890bc926`, run [44313014167](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44313014167), job `134831845524` (`full (100)`) completed SUCCESS. All five recurrence coefficients (j=25,50,100,200,400) have strict 1,000,001-significant-digit rounding PASS, minimum 3,597,107 relative bits, at 3,600,000 working bits. Artifact `m12-lanczos-100` ID `14431877216`. **Remaining:** M=200 and 400 jobs still running at this snapshot; do not count them as certified.
- **BENCHMARK ONLY**: PR #390 exact HEAD `c790ff3915aee28ad67a054d648b18e6b16f502e`, run [44315118699](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44315118699), all four jobs SUCCESS. At 4,096 bits, t=4: baseline 272.58s, interval Newton 74.81s, speedup 3.64x, 4,088 certified relative bits (job `134839060958`). This does **not** establish a speedup at 3,600,000 bits.
- **OPEN**: PR #385 all five full-profile jobs still running at snapshot; #387 error combiner awaits their outputs and the two outstanding #386 artifacts. No final million-digit table certification is claimed.

## 2026-11-18 15:16 UTC incremental verification

- **CERTIFIED (Arb):** #386, pinned HEAD `8fc451ce053a769087fb25ed16289018890bc926`, run [44313014167](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44313014167), job `134831845297` (`full (200)`) completed SUCCESS at 14:17:58 UTC. Five coefficient checks at 3,600,000 working bits, minimum **3,593,431 relative bits**, all strict 1,000,001-significant-digit rounding checks PASS. Artifact [14435228234](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44313014167/artifacts/14435228234), artifact ZIP SHA256 `eb184d12ad6db434bbc533b0cfde30d83fa08f54b6917e54284ea4aeca8f2a26`, job peak RSS 1,096,280 KiB, 3,315.621 seconds. Together with prior M=100 success, 10/15 finite Lanczos intermediate inputs are certified; M=400 still in progress.
- **OPEN:** #385 all five full profile jobs remain in progress at 15:16 UTC; #387 cannot yet combine the table without the remaining inputs. No new jobs were duplicated or interrupted. Historical printed-precision table coverage is unchanged and distinct from million-digit certification.
