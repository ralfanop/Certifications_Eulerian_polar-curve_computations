# Davie's lower bound for K_G: independent Arb check of the value

This folder checks the value of Davie's lower bound, and compares it with the numerical statements of the Lean 4 certificate of 15 October 2026 (`NUMERICAL_CERTIFICATE.txt`; archive SHA-256 `aa2762d8…dd4b`). We have not received the archive itself, so the Lean build has **not** been rerun here.

## Formula used

We use Davie's original formula (his TeX note of 21 November 2024):

  F_ρ(α) = (2/π) e^{−α²} + ρ (1 − 2 (2/π)^{1/2} ∫_α^∞ e^{−x²/2} dx),  ρ(α) = (2/π)^{1/2} α e^{−α²/2},

  K_G ≥ sup_{0<α<1} (1 − ρ(α)) / max(ρ(α), F_{ρ(α)}(α)).

The Lean certificate characterises the optimiser by H(α) = 1 − 2cJ(α) − c² e^{−α²} = 0, with c = (2/π)^{1/2} and J(α) = ∫_0^α e^{−t²/2} dt, and sets C_D = (π/2) e^{α*²}.

## Result (`davie_arb.c`, `davie_arb.log`, Arb at 256 bits)

- α* = 0.25573021316621001436186993372833260790…, isolated by bisection with certified signs of H. It lies inside the Lean interval (0.25573021316621001436186993372833260, …261).
- C_D = 1.676956674215576237077855078853041131… ± 4·10⁻⁴¹. It lies inside the Lean interval (1.676956674215576237077855078853, …854).
- Davie's ratio (1 − ρ)/max(ρ, F_ρ) evaluated at α* equals C_D to all 40 digits. At nearby α it is smaller, for example 1.6769566724… at α = 0.2557 and 1.6769566647… at α = 0.2558.

This agrees with the Lean statements: K_G ≥ C_D > 1.676956674215576237077855078853.

## Note on the printed formula

The forms printed in eq. (2.15) of the 22 May 2026 submission and in eq. (316) of the manuscript differ from Davie's original in two places: e^{−α²/2} instead of e^{−α²}, and ∫_0^∞ instead of ∫_α^∞. Used as printed, they would give π e^{1/(4π)} − 1 = 2.4018… instead of 1.67696…. The Lean value agrees with Davie's original form: same optimiser and same value.

## Reproduce

```
gcc -O2 -I$FLINT/include davie_arb.c -o davie_arb -L$FLINT/lib -Wl,-rpath,$FLINT/lib -lflint -lmpfr -lgmp -lm
./davie_arb > davie_arb.log
```

## 1000 certified digits (`davie_1000.c`, `davie_1000.log`)

The program `davie_1000.c` encloses α* to 1000 digits and C_D with error below 2.4·10⁻¹⁰¹⁰. It works at 3600 bits: Newton steps, then a certified sign change of H on [α* − 2⁻³⁵⁰⁰, α* + 2⁻³⁵⁰⁰].

The root is unique because H′(a) = 2c e^{−a²/2}(c a e^{−a²/2} − 1) < 0 for a ≥ 0, since c a e^{−a²/2} ≤ c e^{−1/2} < 1. These are digits of Davie's constant C_D, the value of his lower bound; they are not digits of K_G.

## Review of the Lean 4 package (received 15 Oct 2026, 09:30)

We received `Davie_Lean4_Numerical_Certificate_2026-10-15.zip`. Its SHA-256 is aa2762d8…dd4b, which matches the announced value, and all 63 entries of its `SHA256SUMS.txt` match. We read the package; we did **not** rebuild it. A rebuild needs Lean 4.24.0 and mathlib `f897ebc`, and neither the toolchain release nor the mathlib cache is reachable from our machine.

What we checked by reading:

- **The hypothesis `IsGrothendieckBound K`** (`GrothendieckBound.lean`) is the finite real Grothendieck inequality. It states |Σ a_ij⟨u_i, v_j⟩| ≤ K·M for all finite I, J, every dimension n, and ‖u_i‖, ‖v_j‖ ≤ 1, whenever |Σ a_ij s_i t_j| ≤ M for all s_i, t_j ∈ [−1, 1]. So `davie_lower_bound` states exactly K_G ≥ C_D.
- **The scalar definitions** (`Basic.lean`): F(r, x) = (2/π)e^{−x²} + r(1 − 2·tail x), with tail x = c∫_x^∞ e^{−t²/2}. This is Davie's original formula, and the file says so explicitly ("not the erroneous printed formula").
- **No proof escapes.** There is no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `extern` in the 3247 lines of source. The recorded axiom audit lists only propext, Classical.choice and Quot.sound.
- **The numerical enclosures** of α* and C_D agree with our independent Arb computation (above).
