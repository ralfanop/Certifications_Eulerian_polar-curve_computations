# M15 §§9–12: manuscript-to-Lean correspondence audit, 2026-11-27

## Scope and criteria

Source: Manuscript_15_20261125_EQ499_508_SEPARATE.pdf, 146 pages, §§9–12 (printed pp. 96–134 inspected; numbered statements below). This inventory covers all 31 numbered theorem/proposition/corollary/lemma/conjecture entries in those sections, but it is not yet a proof-complete or equation-by-equation audit. A declaration is counted only once by module/name, not once per CI or dependency compilation. “Partial” means some relevant formal declarations exist; it does not certify the whole manuscript statement. “Unmapped” means no exact correspondence established in the ten modules inspected, not proof of absence across the entire repository. Candidate modules are not treated as certified.

Main snapshot: 93dc60f93a344144f8bc2ca35421fa6f5775897d. The ten listed Lean source blobs were read on this snapshot. CI references are successful historical exact-HEAD runs, not a single combined compilation of this main snapshot.

| Module (under lean/Manuscript15/) | PR | Source blob SHA | Audited declaration inventory | CI run |
|---|---:|---|---:|---|
| CrossQuarticCurve20261125.lean | #613 | b62e7c186b615468ad92061a46b0c626103ccca6 | 20 | 45607167782 |
| CrossQuarticFibreClassification20261125.lean | #613 | a2e4bd109e22e8b518076215669913ee276d981a | 3 | 45607167643 |
| CrossQuarticFinitePeriod20261125.lean | #613 | 4f4de00fd86c91b07ac2dd99bb8e66abaadda38b | 6 | 45607167482 |
| CrossQuarticPeriodDifferential20261125.lean | #613 | 173107d509a1344f53440103d989ef0d5c3b43b9 | 4 | 45607167532 |
| CrossQuarticImproperPeriod20261125.lean | #625 | 2c707a226c1e4b14dc39b141331d51e15299fc3b | 7 | 45710059640 |
| Sections9To12Geometry20261125.lean | #623 | b7947501ed1683c31c37017dd4edd39876f5381f | 26 | 45776973062 |
| GeometryAnalysis20261126.lean | #626 | d0fb9fa339968bc1c9c04e923463a94f2fa7fca8 | 23 | 46011518125 |
| HydraulicIntegrals20261126.lean | #627 | 3e1fabaa1f0bdd69dddbf9940dd6f13413b195a1 | 16 | 46011532075 |
| DeltoidArclength20261127.lean | #669 | 1971276cdad09a9fca94e61b157d14b5c0cf03ce | 4 | 46012151293 |
| QuarticUniformTransfer20261127.lean | #670 | 0d4b2a6f5d51fcddf5e85e5cc5cdb999af4cba8a | 2 | 46015041289 |

Total 111 printed declarations in ten files. This is not a count of distinct mathematical results or a percentage of manuscript completion. The #625 CI log (job 139541857312) explicitly verifies seven declarations, not six; its PR title uses an equation number from another version. In this frozen manuscript equation (555) is a Dirichlet eigenvalue upper bound; the improper elliptic-period identity is equation (614). No inference about (555) follows from #625.

## Numbered-statement coverage matrix

| Manuscript statement | Relevant integrated evidence | Remaining obligations / scope |
|---|---|---|
| Prop 9.1 Junction and Fourier tail | #626 one-sided smoothing/derivative ingredients (not a Fourier-tail proof) | Exact jump, tangent angle and Fourier asymptotic proof unmapped |
| Thm 9.2 Centred anisotropic aperture | none mapped | Exact supremum and geometric admissibility |
| Prop 9.3 Self-dual rotation amplitudes | #623 self_dual_agnesi; #627 orbit_density_integrable; #613/#625 self-dual elliptic period | General real/imaginary amplitude, monotonicity uniqueness, singular value, complex continuation and genus not fully mapped |
| Prop 9.4 Metric and curvatures | #623 ridge_metric_determinant, positivity, normal orthogonality and norm; #626 immersion derivatives and second_form_* | Assemble all metric/curvature formulae and hypotheses with geometric normalisations |
| Cor 9.5 Exceptional crease curvature | #623 neck_curvature_zero_iff; #626 neck_gaussian, neck_mean | Torsion, one-sided angle, full geometric correspondence |
| Prop 10.1 First-order splitting of a circular doublet | none mapped | Shape derivatives with Dirichlet/Neumann doublets |
| Thm 10.2 Dirichlet spectral stability under radial smoothing | none mapped | Domain inclusion and min-max for Dirichlet spectrum |
| Prop 10.3 Transformation tensor | #623 tensor_det, tensor_inverse_left/right, tensor_quadratic_form/positive, throat_characteristic, golden_throat_roots | Complete pullback and physical PDE identification |
| Cor 10.4 First-order parity selection | none mapped in these ten files | Field reflection and derivative of Maxwell pencil |
| Thm 10.5 Positive Gaussian mixture of the rotation law | #623 self_dual_agnesi | Actual Gaussian double integral, positive measure, justified exchanges |
| Prop 10.6 Transmission eigenchannels and recovery | #626 flux_difference, flux_rayleigh_bounds, transmission_lower_norm/recovery_bound/recovery_sharp, selectivity_interval | Only under stipulated flux/lower-bound/attainment hypotheses; compression and spectral realization remain to be matched |
| Prop 10.7 Analytic extension of polar junction | #623 node_factorization | Actual analytic germs, inverse-function chart and ordinary node |
| Prop 10.8 Area increment and nodal smoothing | #623 quartic_difference/nonnegative, quartic_area_primitive, quartic_central_height_squared; #626 rounded_* and smoothing_integral | Uniform analytic remainders, actual area normalization |
| Prop 10.9 Partial Dirichlet threshold separation | none mapped | (555)–(556) actual rigorous spectral estimates; not certified by #625 |
| Lem 10.10 Strong convergence of transverse eigenspaces | none mapped | Spectral compactness, varying forms, strong H1 convergence and cluster bases |
| Lem 10.11 Local uniform integrability and compactness | none mapped | Actual weighted PEC Maxwell spaces, uniform local compactness under smoothing |
| Thm 10.12 Conditional continuity of vector scattering | #623 selectivity_error_bound | Norm estimate is conditional on convergence; actual scattering existence/compactness/nonthreshold regularity and convergence unmapped |
| Prop 10.13 Trapped modes and bounded-domain exclusion | candidate #677, not counted | Hilbert-space Riesz operator kernel under Hermiticity, then physical realization, exact traces, lead decay and point-spectrum assertions |
| Thm 10.14 Dihedral angle and frozen energy exponent | #623/#626 normal and curvature ingredients | Actual dihedral angle, Mellin spectrum and energy scaling |
| Cor 10.15 Minimum and its order in capped guide | none mapped | Global minimum and quadratic order |
| Thm 10.16 Longitudinal localisation of integral model | none mapped | Laplace asymptotic with logarithmic correction; distinct from vector scattering |
| Thm 10.17 Positive Dirichlet corrector and harmonic duality | none mapped | Existence, finite energy, coefficient positivity, duality |
| Cor 10.18 Fractional term of frozen scalar problem | none mapped | Homothetic rescaling and scalar asymptotic |
| Thm 10.19 Conditional selectivity coefficient | #623 selectivity_error_bound is only a related estimate | Actual Pauli expansion, differentiability and coefficient identity under assumed transmission expansion |
| Cor 10.20 Separation of extremal transmission coefficients | none mapped | Spectral projector derivatives and signed separation |
| Conjecture 10.21 Global fractional Maxwell response and nonvanishing | none; deliberately not certified | Conjecture, no unconditional formal proof or numerical enclosure inferred |
| Prop 10.22 A posteriori nonvanishing test | none mapped | Prove conditional error inequality, distinguish hypothetical certified error budgets from modal pilot |
| Prop 11.1 Hydraulic comparison at equal occupied area | #623 hydraulic_*; #626 deltoid_signed_area_integral; #627 polar_deficit_bound and derivative/integral results; #669 deltoid_arclength | Parametrized integrals verified; assemble actual area/perimeter identification, scaling and complete velocity comparison under hydraulic hypotheses |
| Cor 12.1 Quartic normalization and geodesic amplitude | #623 quartic_potential_bridge; #627 orbit_density_integrable; #625 self-dual period | External normalization and limit inputs, matching definitions and all constants |
| Prop 12.2 Degree-two map of quartic period curves | #613 affine equations, differential and two-point fibres, finite period; #625 actual improper period (614); candidate #674 | Complex homogeneous basepoint/rank proofs pending; projective descent/morphism, smooth projective model, degree and genus via Riemann–Hurwitz not yet certified |
| Prop 12.3 Quartic local form of self-dual crease | #613 exact polynomial jet and scaling; #670 conditional uniform-box estimate; candidate #676 | Actual analytic phase, uniform fifth-order phase and sixth-order crease errors, scaling limit as M→∞ remain |

## Deduplication and remaining work

- #669 imports #626; its 23 dependency declarations are not counted a second time. #670 imports #613; its existing dependency declarations are not counted again. #625 compiles #613 dependencies. The finite period and improper period are complementary steps, not independent certifications of genus one.
- Related algebraic and analytic statements with different names have not been completely deduplicated semantically. The 111 is a module/name inventory only.
- #674, #676 and #677 are separate candidate contributions (4 statements each); they must not be counted before exact-HEAD CI and axiom audit.
- Priorities: actual uniform Taylor remainder (615)–(617); complex projective descent and genus; full continuous Maxwell functional analysis; outstanding numbered statements and every equation; independent combined main-snapshot compilation with exact dependency/axiom inventory and semantic matching. No conjecture or numerical modal result is promoted to a theorem.
