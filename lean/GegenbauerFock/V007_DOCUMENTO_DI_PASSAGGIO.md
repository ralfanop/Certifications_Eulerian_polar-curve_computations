# V007 — Documento di passaggio operativo e scientifico

**Aggiornamento:** 26 ottobre 2026, ore 14:46 circa (Europe/London).  
**Scopo:** consegna autonoma del lavoro Gegenbauer–Fock a una successiva sessione o a un altro revisore, senza perdere risultati, limiti di certificazione, convenzioni o vincoli editoriali.  
**ATTENZIONE:** questo è un documento di passaggio per **V007**, non una nuova versione del manoscritto V097.

## 1. Vincoli inderogabili

1. **V097 è approvato, autonomo e intoccabile.** Non modificarlo, non ampliarlo, non fondere alcuna sua sezione con V007. V007 deve collegarsi scientificamente a V097 con citazioni e con definizioni sufficienti all'autonomia espositiva.
2. **V007** è il nuovo manoscritto e contiene ogni ulteriore risultato riguardante curva polare euleriana, Gegenbauer–Fock, rappresentazioni Segal–Bargmann, teoria operatoriale e relative certificazioni.
3. **Non usare ChatGPT Work senza richiesta espressa dell'autore** (l'autore ha respinto il trasferimento automatico).
4. **Non fare merge della PR #16**, né modificare \`main\`, senza autorizzazione esplicita e specifica. La PR deve restare **draft**.
5. Non dichiarare “certificata” una proposizione soltanto perché è matematicamente plausibile o perché è scritta in un dossier: richiedere sempre la compilazione effettiva, il corretto enunciato e l'audit \`#print axioms\`.
6. Gli originali vettoriali delle figure di V097 sono intoccabili.

## 2. Repository e stato GitHub

- Repository: https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations
- PR: https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/16
- Ramo: \`gegenbauer-fock-formalization-20261025\`
- Workflow: https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/workflows/gegenbauer-fock-lean.yml
- Directory Lean: \`lean/GegenbauerFock/\`
- Stato verificato nell'istante della stesura: **PR aperta, in bozza, non incorporata in \`main\`**.
- HEAD osservato: \`c6f5c33e80a526fed3f5e01bd16b8b6534976da8\`.
- CI Push dell'HEAD: https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40341913976 — **SUCCESS**.
- CI Pull Request dello stesso HEAD: https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40341922475 — **in esecuzione nell'istante della verifica**; ricontrollare prima di dichiarare verificata anche questa esecuzione.
- Il commit precedente \`b64392d8b1cf924b01aa0343329096b582345b2d\` ha **entrambi** i controlli verdi:
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40341865374 e
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40341874388.

**Nota:** gli identificativi di commit e gli esiti cambiano con le revisioni. Prima di proseguire, leggere PR HEAD e i log delle esecuzioni pertinenti, senza assumere che il commit qui riportato sia ancora l'ultimo.

## 3. Parametri e strutture matematiche

Si assumono \(\lambda>0\), \(\alpha>0\). La misura ultrasferica normalizzata è
\[
d\nu_\lambda(u)=
\frac{\Gamma(\lambda+1)}{\sqrt{\pi}\,\Gamma(\lambda+\frac12)}
(1-u^2)^{\lambda-\frac12}\mathbf 1_{(-1,1)}(u)\,du.
\]
Nel codice è realizzata concretamente come pushforward di
\(\operatorname{Beta}(\lambda+\frac12,\lambda+\frac12)\)
mediante \(x\mapsto 2x-1\).

L'operatore ricercato è
\[
C_{\lambda,\alpha}f(z)=
\int_{-1}^1 f(u)e^{izu/2}\,d\nu_\lambda(u).
\]
Il suo modello di Hilbert a coefficienti è una mappa
\[
C_{\lambda,\alpha}:L^2(\nu_\lambda;\mathbb C)
\longrightarrow\ell^2(\mathbb N;\mathbb C),
\]
con righe normalizzate
\[
(C_{\lambda,\alpha}f)_n=
\frac{i^n}{2^n\alpha^{n/2}\sqrt{n!}}\,
\int_{-1}^1 u^n f(u)\,d\nu_\lambda(u).
\]

**Convenzione:** Mathlib usa un prodotto interno \`inner ℂ\` con coniugazione sul primo argomento. Controllare sempre gli aggiunti e i fattori \(i^n\), \(\overline z\), segni e coniugazioni. Il dossier matematico usa convenzioni dichiarate autonomamente: non trasferire le formule senza conversione esplicita.

## 4. Risultati formalizzati e verificati (allo stato rilevato)

I seguenti risultati hanno moduli Lean compilati nelle esecuzioni verdi del ramo, **nei limiti degli enunciati effettivamente presenti nei sorgenti**:

- \`KernelCore.lean\`, \`OscillatorCore.lean\`: identità algebriche di nucleo, positività finita Gram, algebra bosonica formale a due modi.
- \`AnalyticKernel.lean\`: derivate vere del nucleo \(e^{cuv}\), identità **puntuale** differenziale sferoidale, positività e maggiorazione sul quadrato.
- \`LegendreMoments.lean\`: integrali per ogni momento pari/dispari del caso \(\lambda=1/2\), massa uno.
- \`EulerianFourierIntegral.lean\`: integrali Fourier complessi, incluse frequenze complesse non nulle.
- \`UltrasphericalMeasure.lean\`: misura Beta trasportata per ogni \(\lambda>0\), normalizzazione, supporto quasi ovunque; funzionali di valutazione Fourier come autentici elementi di \(L^2\) e loro identificazione integrale.
- \`WeightedMoments.lean\` e \`FactorialFockWeights.lean\`: coefficienti monomiali \(L^2\) con pesi fattoriali, controllo della norma e sommabilità quadratica.
- \`ConcreteFockOperator.lean\`, \`GeneralUltrasphericalFock.lean\`, \`InfiniteFockAnalysis.lean\`: operatore complesso-lineare **limitato e concreto** \(L^2(\nu_\lambda)\to\ell^2\), formula dei coefficienti.
- \`L2Coefficient.lean\`, \`HilbertGram.lean\`, \`AdjointBasis.lean\`: aggiunto di Hilbert effettivo, Gram positivo e autoaggiunto, formula dell'aggiunto sui vettori della base canonica.
- \`InfiniteFockTruncations.lean\`, \`SummableRowsCompact.lean\`, \`CompactnessBridge.lean\`, \`ConcreteFockCompact.lean\`: approssimazioni a rango finito, convergenza in norma e **compattezza dell'operatore concreto nel modello \(\ell^2\)**.
- \`ConcreteFockEnergy.lean\`, \`ConcreteFockRowEnergy.lean\`, \`MomentEnergyIntegral.lean\`, \`RowEnergyTonelli.lean\`, \`RowEnergyExpIntegral.lean\`: energia quadratica delle righe e, nel modello \(\ell^2\), identità esatta
  \[
    \sum_{n\ge0}\|(\operatorname{coord}_n\circ C_{\lambda,\alpha})\|^2
     =\int e^{u^2/(4\alpha)}\,d\nu_\lambda(u).
  \]
  Questo è un teorema sull'energia di righe e coincide matematicamente con la norma Hilbert–Schmidt al quadrato; la sua identificazione **in Lean** con una eventuale API separata di ideale Hilbert–Schmidt resta un compito distinto.
- \`FockEvaluationSequence.lean\`, \`EvaluationComposite.lean\`: funzionali di valutazione continui sul modello a coefficienti e formula di serie per la loro composizione con l'operatore.
- \`RationalTrace.lean\`: aritmetica razionale esatta di una somma di 15 termini, per \(\lambda=\frac12\), \(\alpha=1\), a supporto di un intervallo razionale per l'integrale scalare. La stima del resto e il legame con l'integrale infinito sono illustrati nei documenti matematici e vanno distinti dall'audit Lean.

**Cautela:** “certificato in Lean” significa soltanto che il preciso enunciato elaborato dal kernel è dimostrato e privo di \`sorryAx\` negli audit pertinenti. La compilazione del workflow non certifica automaticamente tutta la teoria a cui i commenti del codice alludono.

## 5. Obiettivi non ancora da dichiarare conclusi

1. Identità esplicita della misura Beta trasportata con la densità Gamma ultrasferica e formula generale dei momenti
   \(m_{2n}=(1/2)_n/(\lambda+1)_n\), \(m_{2n+1}=0\).
2. Identificazione isometrica rigorosa del modello \(\ell^2\) con lo **spazio di Bargmann–Fock di funzioni intere integrabili rispetto alla misura gaussiana complessa**.
3. Dimostrazione Lean che la valutazione in \(z\) dell'operatore a coefficienti è **esattamente** l'integrale di Bochner
   \(\int f(u)e^{izu/2}\,d\nu_\lambda(u)\) per ogni \(z\in\mathbb C\). La sola uguaglianza con una serie è insufficiente senza giustificare integrazione termine a termine.
4. Identificazione in Lean dell'energia delle righe con la norma di ideale Hilbert–Schmidt, qualora si usi una struttura formale distinta; e identità con
   \({}_1F_1(1/2;\lambda+1;1/(4\alpha))\), che richiede i momenti generali.
5. Formula esplicita dell'aggiunto nel modello analitico
   \((C^*F)(u)=F(-iu/(2\alpha))\), con convenzioni di coniugazione controllate.
6. Formula integrale del Gram con nucleo \(e^{uv/(4\alpha)}\), classe traccia e sua traccia esplicita, collegamento rigoroso dei valori singolari e delle classi di Schatten \(S_p\).
7. Iniettività, densità dell'immagine, operatori a due modi in domini adeguati.
8. Realizzazione autoaggiunta di Sturm–Liouville e commutazione degli **operatori integrali non limitati con i relativi domini**: la sola identità puntuale \(L_u K=L_v K\) non basta.
9. Certificazioni numeriche intervallari **solo** per le costanti, gli autovalori e i resti quantitativi effettivamente richiesti nel nuovo manoscritto; non confondere un'approssimazione numerica con una prova generale.

Queste sono attività **per V007**, non variazioni a V097.

## 6. Documenti di riferimento già nel repository

- Dossier teorico:
  \`lean/GegenbauerFock/V007_HILBERT_PROOF_DOSSIER.md\`
- Registro degli obblighi:
  \`lean/GegenbauerFock/ANALYTIC_AUDIT.md\`
- Intervalli razionali:
  \`lean/GegenbauerFock/V007_RATIONAL_CERTIFICATE.md\`
- README dei certificati:
  \`lean/GegenbauerFock/README.md\`
- Documento presente:
  \`lean/GegenbauerFock/V007_DOCUMENTO_DI_PASSAGGIO.md\`

I dossier matematici presentano anche risultati ancora privi della formalizzazione finale; rileggere gli enunciati Lean originali prima di comunicare lo stato delle certificazioni.

## 7. Ripresa tecnica immediata

1. Leggere il HEAD effettivo della PR e l'esito **Push + Pull Request** relativo a quel medesimo SHA.
2. Consultare **il sorgente** dei moduli e i loro \`#print axioms\`, non soltanto i commenti.
3. Usare il toolchain \`lean/lean-toolchain\` esistente; Mathlib fissata in \`lean/lakefile.toml\` al commit \`0272bbe1c093d038d7257ab15306abd58245f9ff\`.
4. Compilazione riproducibile: \`cd lean && lake update && lake exe cache get && lake build GegenbauerFock.ConcreteFockCompact\` e gli altri target della workflow.
5. Proseguire con i teoremi che collegano **valutazione della serie, integrale di Bochner, aggiunto di valutazione, traccia e ipergeometrica**, uno alla volta, facendo fallire CI su ogni obiettivo incompleto.
6. Assicurare che gli audit non riportino \`sorryAx\` né \`Lean.ofReduceBool\`; non introdurre \`sorry\`, \`admit\` o nuovi assiomi.
7. Per ogni risultato finale, registrare: enunciato, modulo, SHA, link CI, output assiomi e confini precisi della proposizione dimostrata.
8. **Non fare merge**; non modificare V097. I risultati approvati saranno rielaborati editorialmente **soltanto nel nuovo documento V007**.

## 8. Stato della consegna

Questo file è il **documento di passaggio**. Le versioni di testo scientifico del futuro manoscritto V007 e le relative impaginazioni LaTeX/PDF restano oggetti distinti: questo documento **non** è il manoscritto V007 finale.

Si deve poter riaprire una sessione successiva consegnando soltanto il link a questo documento e alla PR #16.

## 9. Aggiornamento certificato del 26 ottobre 2026 — aggiunto completo e Gram integrale

**Questa sezione prevale sulle indicazioni precedenti relative agli
obiettivi 3, 5 e alla formula integrale dell'obiettivo 6 della sezione
5, che descrivevano lo stato storico della prima consegna.**

**Commit del codice formalmente verificato:**
`444e3b80cd3e1241909ed51b5930812b1e160729`

**Workflow associato:** https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40386146429

**Esito:** `completed/success`, incluse regressioni e audit degli
assiomi. I log `#print axioms` delle nuove dichiarazioni riportano
esclusivamente `propext`, `Classical.choice`, `Quot.sound`;
nessuna dipendenza `sorryAx` o `Lean.ofReduceBool`.

**Completato in Lean:**

1. `EvaluationComposite.lean` dimostra per ogni \(z\in\mathbb C\)
   l'uguaglianza, come funzionali lineari continui, tra
   valutazione della trasformata Gegenbauer–Fock a coefficienti e
   integrale di Bochner originale.
2. `AnalyticRestrictionCLM.lean` costruisce l'operatore limitato
   \(R_{\lambda,\alpha}:\ell^2\to L^2(\nu_\lambda)\) dalla restrizione
   analitica \(F\mapsto[u\mapsto\mathcal R_\alpha F(-iu/(2\alpha))]\).
3. `AnalyticAdjointComplete.lean` dimostra le formule di base
   normalizzate e, per densità e continuità, l'identità completa
   \[
       \boxed{C_{\lambda,\alpha}^{*}=R_{\lambda,\alpha}}
   \]
   come **uguaglianza di veri operatori lineari continui**.
   La formula vale per ogni \(F\in\ell^2\), in \(L^2(\nu_\lambda)\).
4. `GramIntegralComplete.lean` costruisce l'operatore limitato
   con nucleo integrale e certifica
   \[
       \boxed{
       (C_{\lambda,\alpha}^{*}C_{\lambda,\alpha}f)(u)
       =\int_{-1}^{1}e^{uv/(4\alpha)}f(v)\,d\nu_\lambda(v)
       \quad \nu_\lambda\text{-q.o.}}
   \]
   per ogni \(f\in L^2(\nu_\lambda)\), oltre all'uguaglianza
   dell'intero operatore \(C^*C\) con l'operatore di Bochner.
5. `GramKernelSeries.lean` conserva le identità di serie
   integrali, la forma sesquilineare e la compattezza concreta.

**Ancora distinti e aperti nella formalizzazione:** modello
olomorfo gaussiano completo e sua isometria con \(\ell^2\);
esplicita densità Gamma e momenti generali; norma nella API
formale dell'ideale Hilbert–Schmidt, operatore classe traccia e
ipergeometrica \({}_1F_1\); iniettività, densità dell'immagine,
spettro e Schatten; teoria Sturm–Liouville con domini; eventuali
certificati intervallari di stime numeriche.

Il dossier
`lean/GegenbauerFock/V007_ADJOINT_GRAM_COMPLETE_PROOF.md`
è aggiornato per registrare i nuovi teoremi, le prove matematiche
e il confine della certificazione Lean.

**Invarianti:** PR #16 Draft; non eseguire merge in `main`;
non modificare V097. Ogni ulteriore modifica deve conservare il
presente checkpoint certificato e superare nuova CI al nuovo HEAD.

## 10. Checkpoint del 29 ottobre 2026 — ampiezza polare positiva

Questa sezione aggiorna gli obiettivi spettrali storicamente aperti alla
sezione 5; non sostituisce la verifica dei teoremi specifici nel codice Lean.

- **Fattorizzazione spettrale unitaria verificata:** commit
  `711fd13da311aa6821c09453fa0dda63df708ead`,
  CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40905428785
  (**SUCCESS**). Il teorema
  `exists_unitary_positive_spectrum_factorization_kummer`
  costruisce l'isometria lineare suriettiva `W` fra i due spazi di
  Hilbert, l'ampiezza continua `P` e le identità puntuali
  `C f = W (P f)` e `gram f = P (P f)`, con valori singolari
  positivi e somma quadratica espressa dalla serie non regolarizzata
  `KummerCoefficients.kummerSeries lam (1 / (4 * alpha))`.
  Nessuna suriettività è asserita per il compatto `C`.
- **Positività globale dell'ampiezza verificata:** commit
  `0f8223fb9bb2f19681a1fce0b2500af96aa8bdbb`,
  CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40918482559
  (**SUCCESS**). Il teorema
  `exists_positive_polar_amplitude_kummer` in
  `PositivePolarAmplitude.lean` stabilisce l'autoaggiuntezza di `P`,
  la positività della forma quadratica sull'intero spazio sorgente,
  la sua iniettività, la diagonalizzazione sulla base di Hilbert,
  `P²=C* C` e le identità della trasformata unitaria.
  L'audit della CI riporta esclusivamente gli assiomi standard
  `propext`, `Classical.choice` e `Quot.sound`; niente
  `sorryAx` né `Lean.ofReduceBool`.
- **Identificazione con radice CFC ancora in validazione:** la CI
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40918647299
  è fallita per istanze di tipo e un passaggio di elaborazione Lean
  nel modulo `CanonicalCFCPolarSquareRoot.lean`. Il ramo
  contiene correzioni successive per l'azione scalare reale e
  l'identità `P*P=gram`. La nuova CI
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40921575135
  è stata avviata, ma **non va dichiarata SUCCESS senza verificare
  la conclusione e l'audit**. Obiettivo preciso:
  `CFC.sqrt (gram lam alpha hlam ha) = P` e
  `C f = W (CFC.sqrt (gram lam alpha hlam ha) f)`.

La serie di Kummer utilizzata nel progetto ha parametri
`(1/2; lam+1)`, come definita dalla ricorrenza di
`KummerCoefficients.ratio`: non sostituirla con parametri
ipergeometrici diversi senza dimostrarne l'equivalenza.

**Invarianti operativi:** PR #16 aperta in Draft, nessun merge,
`main` e V097 immutati. Su un ramo con commit concorrenti,
rileggere HEAD e blob SHA prima di ogni modifica.

## 11. Certificazione in corso — compattezza della radice polare positiva

Per evitare di confondere risultati matematici dedotti e teoremi già
certificati dal kernel, registriamo separatamente questo nuovo obbligo:

- **Modulo:** `lean/GegenbauerFock/CompactPositivePolarAmplitude.lean`.
- **Commit del modulo:** `1b75d29b014f89d0cd2c3eee9e452643fd5a1ee4`.
- **Commit del workflow:** `78665726b8f3e836e3c7ed2726b6fe849a4912fe`.
- **CI dedicata:**
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40923232633
  (avviata, da verificare prima di dichiarare SUCCESS).
- **Teorema:** `exists_compact_positive_polar_amplitude`.

L'argomento matematico utilizza l'identità certificata
`C = W ∘ P` con `W` unitario e la compattezza già certificata
di `C`: dunque `P = W⁻¹ ∘ C` è compatto. Il nuovo file trascrive
questo trasferimento nella API Mathlib `IsCompactOperator.clm_comp`
senza sostituire una prova con una semplice dichiarazione.

Resta distinta la CI del modulo `CanonicalCFCPolarSquareRoot.lean`,
necessaria per l'identità letterale `P = CFC.sqrt (C* C)`.

## 12. Identità polari bilaterali certificate — 29 ottobre 2026

**SUCCESS:** la CI
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40922456777
sul commit `eabb42bca4c8f4d29f448f8e743820f172c9cb08` ha compilato
`FullUnitaryPolarAdjointOutputGram.lean` ed eseguito con successo
l'audit degli assiomi del teorema
`exists_full_unitary_polar_adjoint_and_outputGram_kummer`.
Assiomi utilizzati: esclusivamente `propext`,
`Classical.choice` e `Quot.sound`.

Per la trasformata effettiva `C` e unitaria `W`, con l'ampiezza
positiva autoaggiunta `P`, sono ora formalmente certificate
le identità sui **due interi spazi di Hilbert**:

- `C = W ∘ P` e `C* C = P²`;
- `C* = P ∘ W⁻¹`;
- `C C* = W ∘ P² ∘ W⁻¹`.

In particolare queste formule non affermano che `C` sia suriettiva
né che un compatto iniettivo abbia inverso limitato.

**Checkpoint non ancora certificati** alla redazione di questo
aggiornamento:

- Compattezza esplicita dell'ampiezza positiva:
  la CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40923232633
  aveva fallito per una conversione di funzioni in un `simpa`;
  commit correttivo `0d9718186b0affcb0535bc601f43be910c341709`,
  nuova CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40937763994
  avviata. Non dichiarare SUCCESS senza verifica.
- Radice quadrata CFC: il fallimento precedente
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40921575135
  era imputabile all'istanza
  `SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E)`.
  È presente una nuova specializzazione alla sorgente ultrasferica
  nel commit `f044f4c1d2a2db1b344fb9fb9624065d4258e726`,
  con CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40937938186
  avviata; la conclusione deve essere controllata.

**Invarianti:** non eseguire alcun merge; mantenere PR #16 Draft,
non modificare il ramo `main` né il manoscritto V097.

## 13. Positività compatta e nuovi controlli operatoriali — 29 ottobre 2026

**CERTIFICATO:** il teorema
`GegenbauerFock.GeneralUltrasphericalFock.exists_compact_positive_polar_amplitude`
del modulo `CompactPositivePolarAmplitude.lean` ha superato
la compilazione Lean 4 e l'audit degli assiomi alla CI
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40937763994
(**SUCCESS**) sul commit correttivo
`0d9718186b0affcb0535bc601f43be910c341709`.
L'audit non contiene `sorryAx` né `Lean.ofReduceBool`;
solo `propext`, `Classical.choice`, `Quot.sound`.
L'ampiezza `P` effettiva è compatta, positiva, autoaggiunta,
iniettiva, con `C = W P` e `P² = C* C`.

**NUOVO TEOREMA DEPOSITATO, NON ANCORA CERTIFICATO:**
`CompactPositivePolarProperDenseRange.lean` tenta di
mostrare che questa ampiezza compatta ha immagine densa ma propria.
Modulo: commit `b4a413ec797889145593a37f00df9f8b7f0e544e`;
workflow: commit `30182ec7005668b997c61d40bb6489d02835f617`;
CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40943270510
(in coda alla verifica). La prova della densità utilizza
`P.adjoint = P`, `ker P = ⊥` e `orthogonal_range`;
la non-suriettività si trasferisce da `C` attraverso l'unitario
`W`. Non dichiarare il teorema completo fino a verifica della
compilazione **anche** del suo import
`CompactFockProperDenseRange.lean` e dell'audit.

**CFC ancora aperta:** la CI
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40937938186
è **FAILED**: ora la classe mancante è `IsScalarTower ℝ A A`,
per `A = E →L[ℂ] E`. Il ramo include nuovi controlli `#synth`
e istanze specifiche in `CanonicalCFCPolarSquareRoot.lean`,
con CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40942913774
avviata. Solo SUCCESS e audit pulito autorizzano a dichiarare
formalmente `P = CFC.sqrt (C* C)`.

Questa sezione aggiorna le etichette storiche “in corso” delle
sezioni 11–12, senza riscrivere il contenuto dei checkpoint passati.
PR #16 deve restare Draft; non eseguire merge e non modificare
`main` o V097.

## 14. Radice CFC locale e ampiezza con immagine propria — 29 ottobre 2026

Verifica diretta della CI precedente
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40942913774:
**FAILED**, il kernel non riesce a sintetizzare le istanze
`IsScalarTower ℝ A A` e `SMulCommClass ℝ A A` su
`A = E →L[ℂ] E`, anche nei controlli `#synth`.
Non attribuire a questa CI un successo né considerare il teorema
`exists_cfc_sqrt_polar_unitary_kummer` già certificato.

**Nuova strada depositata, da certificare:**

- `LocalCFCGramSquareRoot.lean` introduce due costruttori di
  strutture scalari reali `cfcComm` e `cfcTower`, riferiti allo
  spazio ultrasferico sorgente.
- Definisce `localCFCGramSqrt` come **esattamente**
  `CFC.sqrt (gram lam alpha hlam ha)`, in un contesto in cui le
  strutture scalari sono esplicitamente installate con `letI`.
  Non si tratta di una radice quadrata posticcia o di un assioma.
- Il teorema `exists_local_cfc_sqrt_polar_unitary_kummer`
  identifica questa radice con l'ampiezza positiva `P` usando
  `CFC.sqrt_unique`, preservando la fattorizzazione unitaria
  `C = W P`, la diagonalizzazione e la somma di Kummer.
- Commit del modulo: `50de9d8d934155aaece572b4aa278ef243f8ee6c`.
  Commit del workflow: `10c935267c9ec8b49d833d86fd63345bdadc4fd2`.
  CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40956634761
  (in coda alla compilazione; **NON certificato** finché non sia
  `SUCCESS` con audit pulito).

In parallelo, la CI
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40943270510
sul modulo `CompactPositivePolarProperDenseRange.lean` è in corso.
Verificare anche l'import
`CompactFockProperDenseRange.lean`; evitare conclusioni sulla
non-suriettività dell'ampiezza prima dell'audit.

La precedente certificazione della compattezza e positività di `P`
resta valida: CI
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40937763994
(**SUCCESS**), senza assiomi ulteriori. Restano invariati
PR #16 Draft, nessun merge, nessuna modifica a `main` o V097.

## 15. Compattezza, positività e immagine densa propria certificate

**Nuova CI conclusa con SUCCESS il 29 ottobre 2026:**
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40943270510
(commit del workflow `30182ec7005668b997c61d40bb6489d02835f617`).

Il kernel Lean 4 ha compilato il modulo
`CompactPositivePolarProperDenseRange.lean` (9.115 operazioni).
L'audit di `exists_compact_positive_polar_proper_dense_range`
ha identificato esclusivamente `propext`, `Classical.choice`,
`Quot.sound`, senza `sorryAx` né `Lean.ofReduceBool`.

È certificata l'esistenza dell'ampiezza `P` sul vero spazio sorgente,
con compattezza, positività, autoaggiuntezza, iniettività e
`closure (range P) = ⊤`, ma `¬ Surjective P`, nonché
`C = W P` e `gram = P²`. Questa conclusione è più forte della
mera iniettività della trasformata e non afferma l'esistenza di un
inverso continuo.

**Nuovo corollario separato, NON ancora certificato:**
`CompactPositivePolarNonclosedRange.lean` dimostra come obiettivo
`¬ IsClosed (range P)`, mediante la densità e la mancata
suriettività appena certificate.

- Commit del modulo: `59ecd7bf2824983c9c479c1fc4e787e12796f241`.
- Commit del workflow: `99d9e37c1d4a72ee9d0cee8226a7edd830c6b284`.
- CI https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40957014776
  (avviata, da verificare con compilazione e audit).

**Radice quadrata CFC:** distinta e ancora non certificata,
nuovo percorso con strutture scalari locali nella CI
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40956634761
(da verificare).

PR #16 aperta in Draft, nessun merge, nessun intervento su
`main` e sul manoscritto V097.

## 16. Radice CFC canonica e immagine non chiusa — 29 ottobre 2026

**CI confermata SUCCESS, compattezza e immagine non chiusa:**
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40957014776,
sul commit `99d9e37c1d4a72ee9d0cee8226a7edd830c6b284`.
Il modulo `CompactPositivePolarNonclosedRange.lean` e il teorema
`exists_positive_polar_amplitude_nonclosed_range` compilano
(9.116 operazioni) con audit limitato agli assiomi standard
`propext`, `Classical.choice`, `Quot.sound`; senza
`sorryAx` e senza `Lean.ofReduceBool`. L'ampiezza positiva
`P` ha immagine densa e **non chiusa** nel suo spazio sorgente.

**CI CFC COMPLETATA CON SUCCESS e audit pulito:**
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40971780153,
commit `6c1396d48e8dfea93e2ba968201f2a0510bc0657`,
modulo `CanonicalCFCSqrtExplicitScalarBridge.lean`.
I teoremi Lean
`exists_cfc_sqrt_with_explicit_scalar_commutation` e
`exists_cfc_sqrt_full_polar_adjoint_outputGram_explicit`
dimostrano la vera identificazione della radice del Gram
`P = CFC.sqrt (C* C)` insieme alle identità
`C = W P`, `C* = P W⁻¹`, `C C* = W P² W⁻¹`.
Le classi della CFC reale (`SMulCommClass`, `IsScalarTower`
e strutture di calcolo funzionale) sono costruite esplicitamente
nel contesto dei teoremi, non postulate come assiomi matematici.
Gli audit riportano solamente `propext`, `Classical.choice`
e `Quot.sound`. Questo checkpoint sostituisce la precedente
dicitura “CFC non certificata” delle sezioni storiche.

**Nuova verifica unificata, ANCORA IN CORSO:**
`CanonicalCFCCompactNonclosedRange.lean` formalizza direttamente
per l'operatore canonico `CFC.sqrt (gram ...)` la compattezza,
l'iniettività, la densità e non-chiusura dell'immagine, oltre alla
fattorizzazione `C=W(CFC.sqrt gram)`.
Il teorema candidato `exists_canonical_cfc_compact_nonclosed_range`
riusa gli argomenti già certificati e il lemma `CFC.sqrt_unique`.

- Commit sorgente: `576bb781f22621cc8c0ee9cc4b526ee3670c5d45`.
- Commit workflow: `6c2ec38b1e5b7f786b54ce4883db889b9646e8d1`.
- CI dedicata:
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40972647234
  (in coda; non dichiarare SUCCESS prima della compilazione e audit).

**Percorso alternativo:** la prima CI
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40956634761
per `LocalCFCGramSquareRoot.lean` è fallita in presenza
della classe `NonUnitalContinuousFunctionalCalculus`;
il commit `50c4926f617b35d344250101d227221728f7a212`
aggiunge esplicitamente le strutture CFC in entrambe le prove,
con verifica dedicata
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40972428658
(ancora in corso all'ultimo controllo). Questa CI non va confusa
con il successo già accertato del ponte CFC esplicito.

**Invarianti permanenti:** PR #16 Draft e aperta, nessun merge,
`main` e V097 immutati.
