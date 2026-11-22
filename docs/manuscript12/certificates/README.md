# Manuscript 12: certificates of Table 1

These are the result files of the certification runs of Table 1. They are copied here so that readers can link to them permanently. Workflow artifacts need a GitHub sign-in to download and expire after 90 days.

Each folder holds the files of one artifact, byte for byte, and a `SHA256SUMS` file. Every cell is stored with its enclosure as exact rational endpoints (`lower`, `upper`) and its strict roundings. Anyone can recheck the rounding from these files alone.

| Folder | Digits (significant and fixed decimal places) | Run | Artifact (zip SHA-256) |
|---|---|---|---|
| [`m12-table-68000`](m12-table-68000) | 68000 | [45043079648](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/45043079648), 22 November 2026, `numerics/arb/m12_table_68000.py` | `m12-table-68000`, id 14762806069 (`8e43ab140e8d35fd0a3b9626b72612b61f7947d3797c42fd292243a79a9c28f4`) |
| [`m12-table-100000`](m12-table-100000) | 29000 | [44782807031](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44782807031), 20 November 2026, `numerics/arb/m12_table_100000.py` | `m12-table-100000`, id 14672499850 (`de7e1aae2d3af03990131db193189827b2ed8995920d66bc8e6937e33e256083`) |

The 68000-digit file also contains the five root enclosures it uses (`roots`). These are the step-2 roots of the staged 1000000-bit pipeline: artifact `m12m-bundle-step2` of run 44898333059, at least 226971 relative bits.
