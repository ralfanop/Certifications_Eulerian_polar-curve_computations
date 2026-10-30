# V170 — Consegna moduli Lean nuovi (handoff 2026-10-29) / Delivery of the new Lean modules

Data / date: 2026-10-29. Toolchain: **Lean 4.24.0**, **Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**
(pinned del progetto `EulerianGrothendieck`; `lean-toolchain` e `lake-manifest.json` invariati).

## 1. Che cosa contiene lo zip / Contents

```
lean/EulerianGrothendieck/*.lean      19 moduli NUOVI (nessuno dei 52 certificati e' stato toccato)
lean/AuditNew.lean                    #print axioms + #check per tutti i 286 teoremi nuovi
lean/verify_v170_new.py               ricompilazione certificante sequenziale (-M4096) + audit + hash
verification/V170_NEW_CERTIFICATION.json   certificato: versioni, SHA-256 sorgenti/oggetti, assiomi per teorema
verification/V170_NEW_AXIOMS_AND_STATEMENTS.txt   log dell'audit (#print axioms, #check)
verification/*_NEW_BUILD.txt          log di compilazione di ciascun modulo (vuoti = nessun warning/errore)
verification/V170_CERTIFICATION.json  ri-verifica della baseline (52 moduli, 418 dichiarazioni): PASS
STATEMENTS_NEW_MODULES.md             enunciati completi (tipi) di tutte le 286+ dichiarazioni nuove
manuscript/                           main.tex, sections/eulerian_grothendieck.tex e diff (modifiche chieste in sessione)
SHA256SUMS.txt
```

Regole dell'handoff rispettate: solo moduli nuovi; nessun `sorry`/`admit`/`axiom`/`native_decide`
(controllo testuale nello script + audit); ogni teorema dipende al piu' da `propext`,
`Classical.choice`, `Quot.sound`; un processo `lean` alla volta; nessuna modifica/pubblicazione su GitHub.
Le ipotesi dei teoremi probabilistici sono quelle gia' usate dai 52 moduli certificati:
uno spazio di probabilita' astratto `(Ω, μ)`, `U : ℕ → Ω → ℝ` misurabili, `iIndepFun U μ`,
`μ.map (U i) = V033.UniformSum.uniformLaw`; la copia indipendente `T_M` e' realizzata su `μ.prod μ`.
Nessuna quantita' e' definita uguale al valore da dimostrare.

## 2. Mappa task → moduli → risultati principali / Task map

| Task | Modulo | Risultati principali |
|---|---|---|
| **A** Fock ↔ probabilita' | `GaussianFockBridge` | `rE` (= ∫_{-1/2}^{1/2} e^{itz} dt), `rE_eq_sin_div` (r_E(z)=sin(z/2)/(z/2), z≠0), `gaussian_pairing` (∫ e^{izs−i z̄ t} dμ_α = e^{st/α}), `gaussian_fubini`, **`fock_norm_eq_probability_integral`** (∫‖r_E^M‖²dμ_α = E exp(S_M T_M/α)), `fock_norm_eq_moment_series`, `fock_norm_scaled_eq_uniformNormSeries` |
| **A** | `FockVacuumProjection` | `fockMeasure α` (= volume.withDensity((α/π)e^{−α|z|²})), `fockMeasure_isProbability`, `vacuum`, `fockState α M` in L²(μ_α), `norm_vacuum`, `inner_vacuum_fockState` (=1), `fockState_norm_sq`, **`fock_vacuum_probability`** (‖P_vac ψ‖² = 1/E exp(S T/α), con P_vac = starProjection su ℂ·1), `fock_vacuum_all_orders`, `fock_norm_all_orders` |
| **A** | `FockCorollaries` | `fock_vacuum_threshold_limit` (Teorema 9.6 per p_{E,M}(cM), entrambi i rami), `fock_vacuum_uniform_parameters` |
| **B** ramo critico/subcritico | `CriticalSubcriticalVacuum` | `uniform_norm_lower_bound_divergence`, **`critical_subcritical_norm_tendsto_atTop`** (0<c≤1/12 ⇒ N_M(c)→+∞), **`critical_subcritical_vacuum_tendsto_zero`** (1/N_M(c)→0), `raw_uniform_kernel_hasSum` |
| **C1** proiettore/Grothendieck | `BilinearScalarBridge` | `bilinearScalarNorm` (g_ℂ(A)=sup_{|a_i|,|b_j|≤1}|aᵀAb|), **`bilinearScalarNorm_explicit`** (g_ℂ(P)=max_{|u_j|=1}u*Pu=g(P)), `bilinearScalarNorm_explicit_attained` |
| **C1** | `VectorOptimum` | `bilinearVectorNorm`, **`bilinearVectorNorm_explicit`** (=4), `bilinearRatio_explicit` (𝒬=4/g), `bilinearRatio_eulerian`, **`bilinear_ratio_critical_law`**, **`bilinearRatio_le_of_grothendieck`** (𝒬≤K per ogni K ammissibile), `bilinearRatio_le_complexGrothendieckConstant` (*condizionale*, v. §3) |
| **C2** correlazione esposta | `ExposedCorrelation` | `correlationElliptope`, `frameGram` (K=WW*), `frameGram_mem_elliptope`, `frameGram_rank` (=2), `explicitFrameScalarNorm_lt_four`, `bilinearRatio_gt_one`, `trace_P_le`, **`frameGram_exposed`** (K unico massimizzatore di X↦Re Tr(PX) sull'ellitopo) |
| **C2** | `EndpointDecompositions` | `frameGram_endpoint_zero/one` (K=(u₊u₊*+u₋u₋*)/2), `explicitFrameScalarNorm_endpoint_zero/one` (g=4), `endpoint_vectors_in_range` |
| **D** arcoseno complesso | `ComplexArcsineDisk` | `H0` (ramo), `sin_H0`, `hasDerivAt_H0`, `sup_norm_deriv_H0`, **`H0_lipschitz`**, `H0_lipschitz_sharp`, **`H0_lipschitz_constant`** (2/√5 e' la costante di Lipschitz minima su D_B) |
| **E** L(1,χ₅) | `DirichletChiFive` | `chiFive` (= quadraticChar (ZMod 5) su ℕ), `partialSum`, `integral_pFun`, **`dirichlet_chiFive_tendsto`** (somme parziali → (2/√5)log φ), `LOneChiFive_eq` |
| **E** | `DirichletChiFiveLFunction` | `chiFiveChar : DirichletCharacter ℂ 5`, `chiFiveChar_ne_one`, **`LFunction_chiFive_one`** (`DirichletCharacter.LFunction χ₅ 1 = (2/√5) log φ`), `LFunction_chiFive_one'` (forma 2 log((1+√5)/2)/√5 di Mathar, Table 22 / OEIS A086466), `LFunction_chiFive_one_eq_LOneChiFive` |
| **E** | `CatalanLipschitzDirichlet` | `catalanB_value` (B(1/20)=√5/2), `catalanTheta_value` ([(Θ²−Θ)B](1/20)=3√5/128), **`catalan_lipschitz_dirichlet_bridge`**, `vacuum_limit_cL`, `fock_vacuum_limit_cL` (Prop. 10.1) |
| **F** Bernoulli/ζ | `BernoulliCumulantIdentification` | `even_bernoulli_sum`, **`standardUniformCumulant_bernoulli`** (κ_n = 3^{n+1}2^{2n+1}B_{2n+2}/(2n+2)!), `uniformLogCoefficient`, `standardUniformCumulant_eq_mul_logCoefficient` |
| **F** | `ZetaCumulantIdentification` | **`uniformLogCoefficient_zeta`** (a_j = (−1)^{j−1}3^j ζ(2j)/(j π^{2j})), `standardUniformCumulant_zeta` |
| **G1** occupazione | `OccupancySharpRemainder` | `uniformMomentRatio_occupancy` (R_{M,k}=E∏ρ_{N_j}), `expect_collisions`, `expect_collisions_falling`, **`occupancy_moment_bound`** (Lemma 9.3), **`occupancy_square_bound`** (Lemma 9.4) |
| **G1** | `ExplicitNormRemainder` | `remF, remA, remB` (= F, A, B stampate), **`explicit_norm_remainder`** (Teorema 9.5: 0 ≤ N−F+A/M ≤ B/M²), **`explicit_vacuum_remainder`** |
| **G2** maggiorante stampato | `PrintedAllOrderMajorant` | `standardUniformCumulant_sharp_bound` (|κ_j|≤(1/2)3^{−j}), **`uniformRatio_sharp_coefficient_bound`** (|g_r(k)|≤e(8k²)^r), `uniformSquared_sharp_coefficient_bound`, `printedNormConstant` (C^{(N)}_{t,R} stampata), **`printed_all_order_norm_remainder`** (M ≥ 4096) |
| **H** fase generale | `GeneralPhaseOptimization` | `phaseLambda`, `lambdaPhase`, `general_frameInfimum_remainder`, **`general_phase_loss`** (|4−g(P(p,ϑ))−λ(ϑ)p| ≤ 2000 p^{3/2}, 0<p≤1/144), `general_phase_loss_limit` |
| **I** resto reciproco uniforme | `UniformParameterVacuum` | `inverseSeriesCoefficient_bound`, **`reciprocal_uniform_remainder`**, `uniformVacuumSeries_uniform_parameters`, **`raw_uniform_vacuum_uniform_parameters`** (una sola K(c₀,R) per tutti i c ≥ c₀ > 1/12, M ≥ 1) |

Totale: 286 teoremi/lemmi nuovi (tutti auditati), piu' definizioni. Enunciati completi in `STATEMENTS_NEW_MODULES.md`.

## 3. Punti condizionali / dichiarati esplicitamente — Conditional items

1. **K_G^ℂ (Task C1).** `bilinearRatio_le_of_grothendieck : SatisfiesComplexGrothendieck K → bilinearRatio … ≤ K`
   e' **incondizionato** ed e' il contenuto matematico del lower bound. La versione con l'infimo
   `bilinearRatio_le_complexGrothendieckConstant` ha l'ipotesi `hex : ∃ K, SatisfiesComplexGrothendieck K`
   (teorema di Grothendieck, non formalizzato; in Mathlib `sInf ∅ = 0`). Matematicamente `hex` e' il
   teorema classico (Grothendieck 1953; Haagerup 1987: K_G^ℂ ≤ 1.40491; Davie: ≥ 1.338).
2. **L(1,χ₅) (Task E).** Non piu' condizionale: `LFunction_chiFive_one` identifica il valore con
   `DirichletCharacter.LFunction` di Mathlib (via sommazione per parti, convergenza dominata, continuita' in 1).
3. **Task A.** `rE` e' definita come integrale caratteristico; `rE_eq_sin_div` la identifica con sin(z/2)/(z/2)
   per z ≠ 0 (`rE_zero` per z = 0). La norma e il proiettore sul vuoto sono presi nel vero `Lp ℂ 2 (fockMeasure α)` di Mathlib.
4. **Task G2.** Il teorema con la costante stampata richiede `M ≥ 4096` come nel manoscritto.
5. **Task H.** Costante 2000 e range `0 < p ≤ 1/144` come stampati.
6. **Task L** (UniformLanczos, toolchain 4.35.0-rc3): **non svolto** in questa sessione (toolchain diverso,
   da compilare da sorgente; L3 — Levin–Lubinsky — e' fuori portata di qualsiasi sessione). Piano concordato:
   sessione dedicata, ordine L4 (coefficienti superiori di F) → L2 (log-concavita' di Floater) → L1 (saddlepoint);
   L3 resta ipotesi esterna dichiarata del Teorema 5.9.

## 4. Riproduzione / Reproduction

```
# nella cartella del progetto EulerianGrothendieck (con i 19 .lean copiati in EulerianGrothendieck/ e AuditNew.lean, verify_v170_new.py in radice)
python3 verify_v170.py     --lake /path/to/lake      # baseline: 52 moduli, 418 dichiarazioni (PASS)
python3 verify_v170_new.py --lake /path/to/lake      # nuovi: 19 moduli, 286 teoremi (PASS)
```
Il secondo script cancella gli .olean dei moduli nuovi, li ricompila uno alla volta con `-M4096`, esegue `AuditNew.lean`
e scrive `verification/V170_NEW_CERTIFICATION.json` (hash SHA-256 di sorgenti e oggetti).

## 5. Modifiche al manoscritto chieste in sessione / Manuscript edits (manuscript/)

- (13): rimosso `=1/(4d_E)`; nuova (14): ∫∫∫dxdydz/(1+x²y²z²) = −(7/8)ζ(3) − ψ″(1/4)/64 = 1/(4d_E), con ψ″ = ψ⁽²⁾
  identificata (digamma ψ=Γ′/Γ, ψ″(1/4) = −2Σ(n+1/4)⁻³ ≈ −129.3277399375369) e [31, A233091] per 7ζ(3)/8.
- Parentesi delle O-grandi e delle frazioni nelle formule numerate: `\left( \right)` (11 coppie), `\left| \right|` (2), inline in forma `O(1/M^k)` (2);
  (allprob) con M^{R+1} a denominatore.
- p. 57: "φ=(1+√5)/2 denotes the golden ratio [31, A001622], the quadratic Dirichlet evaluation is".
- p. 58: (281)–(282) accorpate in `c_L = B(x_*)/6 = √5/12`, Proof allineata.
I diff sono in `manuscript/*.diff`. Nel container mancavano i font cm-super: la copia di controllo e' stata compilata
senza espansione microtype (71 pagine); le interruzioni di riga vanno verificate nella build dell'autore.
