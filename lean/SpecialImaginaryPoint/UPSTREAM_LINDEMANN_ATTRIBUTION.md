# Lindemann–Weierstrass formalisation: third-party source and license

The following two files contain **third-party proof code** by **Yuyang Zhao**:

- `UpstreamLindemannAlgebraicPart.lean`
- `UpstreamLindemannBasic.lean`

**Original source:** Mathlib [PR #28013](https://github.com/leanprover-community/mathlib4/pull/28013), project `leanprover-community/mathlib4`, commit `5a0057ccc26b` (18 September 2026).

**Original source paths:**
- `Mathlib/NumberTheory/Transcendental/Lindemann/AlgebraicPart.lean`
- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean`

**Original copyright holder:** Copyright (c) 2022 Yuyang Zhao. All rights reserved.

**License:** Apache License, Version 2.0. The complete corresponding license is included in [`UPSTREAM_LINDEMANN_APACHE_LICENSE.txt`](UPSTREAM_LINDEMANN_APACHE_LICENSE.txt). The original Apache-2.0 copyright notices remain at the top of both Lean source files. The surrounding repository's CC0 license does **not** supersede this third-party Apache-2.0 source license.

**Local modifications:** The copies are compatible with Lean `v4.35.0-rc3` and the existing Mathlib pin `0272bbe1c093d038d7257ab15306abd58245f9ff`. The `AlgebraicPart` file has an additive source comment and changes the former `IsAddTorsionFree` declaration to `HasUniqueDiv` to match the pinned library API; `Basic` has an additive source comment and maps its algebraic-part import to `SpecialImaginaryPoint.UpstreamLindemannAlgebraicPart`. No mathematical result from the upstream original is represented as newly discovered in the Eulerian paper.

**Verification:** [CI #41812297467](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41812297467) and the combined Lean/Arb [CI #41812736721](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41812736721) both succeeded, with the generated special-case proof and final theorem depending only on `propext`, `Classical.choice`, and `Quot.sound`.

**Maintenance:** The Mathlib PR has not yet been merged as of 4 November 2026. When a suitable official upstream version becomes available, remove these local compatibility copies only in a separately reviewed maintenance update; do not silently alter the pinned toolchain or Mathlib revision. This is a **software dependency integration**, not an assertion of scientific priority or a merge to another manuscript.
