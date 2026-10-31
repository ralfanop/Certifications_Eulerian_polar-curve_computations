import GegenbauerFock.CanonicalCFCApproximateNullFamily
import GegenbauerFock.GramApproximateZeroSpectrum

/-!
# V007 — a shared quantitative instability certificate for the polar factor

The true Gegenbauer--Fock operator C and its named canonical positive
CFC Gram square root P share exactly the same image norm under a
certified unitary factor W: C = W P. Their normalized approximate-null
vectors can therefore be chosen simultaneously, with the explicit
1/(n+1) estimate on both images.

This theorem combines compactness, injectivity, proper dense nonclosed
range, and quantitative instability into one reusable Lean result.
It makes no false claim of a nonzero kernel or a bounded inverse.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual canonical CFC square root and true Fock transform
have the same quantified approximate-null vectors, with identical
output norms, while the canonical square root remains a compact
injective operator with proper dense nonclosed image. -/
theorem exists_shared_cfc_polar_instability_family
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients)
      (u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam)),
      IsCompactOperator (localCFCGramSqrt lam alpha hlam ha) ∧
      Function.Injective (localCFCGramSqrt lam alpha hlam ha) ∧
      (localCFCGramSqrt lam alpha hlam ha).range.topologicalClosure =
        (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      ¬ IsClosed ((localCFCGramSqrt lam alpha hlam ha).range :
        Set (Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ f, C lam alpha hlam ha f =
        W (localCFCGramSqrt lam alpha hlam ha f)) ∧
      (∀ n : ℕ,
        ‖u n‖ = 1 ∧
        ‖C lam alpha hlam ha (u n)‖ =
          ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ ∧
        ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ <
          1 / ((n : ℝ) + 1)) := by
  classical
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_local_cfc_sqrt_compact_dense_nonclosed lam alpha hlam ha
  obtain ⟨u, hquant⟩ :=
    local_cfc_root_exists_normalized_approximate_null_family
      lam alpha hlam ha
  refine ⟨W, u, hcompact, hinj, hdense, hnotclosed, hC, ?_⟩
  intro n
  refine ⟨(hquant n).1, ?_, (hquant n).2⟩
  rw [hC (u n)]
  exact W.norm_map _

/-- A *single* normalized family tends strongly to zero under both
the canonical CFC Gram square root and the true Fock transform.
The inputs themselves stay on the unit sphere. -/
theorem exists_shared_cfc_polar_strong_null_sequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Filter.Tendsto
        (fun n : ℕ => localCFCGramSqrt lam alpha hlam ha (u n))
        Filter.atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      Filter.Tendsto
        (fun n : ℕ => C lam alpha hlam ha (u n))
        Filter.atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) := by
  classical
  obtain ⟨W, u, hcompact, hinj, hdense, hnotclosed, hpolar, hquant⟩ :=
    exists_shared_cfc_polar_instability_family lam alpha hlam ha
  have hP : Filter.Tendsto
      (fun n : ℕ => localCFCGramSqrt lam alpha hlam ha (u n))
      Filter.atTop
      (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero
      (fun n : ℕ =>
        norm_nonneg (localCFCGramSqrt lam alpha hlam ha (u n)))
      (fun n : ℕ => (hquant n).2.2.le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨u, (fun n => (hquant n).1), hP, ?_⟩
  have hW : Filter.Tendsto
      (fun n : ℕ => W (localCFCGramSqrt lam alpha hlam ha (u n)))
      Filter.atTop
      (nhds (W (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) :=
    W.continuous.continuousAt.tendsto.comp hP
  have hseq :
      (fun n : ℕ => C lam alpha hlam ha (u n)) =
      (fun n : ℕ => W (localCFCGramSqrt lam alpha hlam ha (u n))) := by
    funext n
    exact hpolar (u n)
  rw [hseq]
  simpa only [map_zero] using hW

/-- The same unit inputs are approximate-zero vectors simultaneously
for the Gegenbauer--Fock transform, its canonical CFC polar root, and
the genuine source Gram. In particular no extra selection of Gram
witnesses is necessary. -/
theorem exists_shared_cfc_fock_gram_strong_null_sequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Filter.Tendsto
        (fun n : ℕ => localCFCGramSqrt lam alpha hlam ha (u n))
        Filter.atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      Filter.Tendsto
        (fun n : ℕ => C lam alpha hlam ha (u n))
        Filter.atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      Filter.Tendsto
        (fun n : ℕ => gram lam alpha hlam ha (u n))
        Filter.atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
  obtain ⟨u, hunit, hP, hC⟩ :=
    exists_shared_cfc_polar_strong_null_sequence lam alpha hlam ha
  refine ⟨u, hunit, hP, hC, ?_⟩
  change Filter.Tendsto
    (fun n : ℕ => C_adjoint lam alpha hlam ha
      (C lam alpha hlam ha (u n)))
    Filter.atTop
    (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam)))
  have hG : Filter.Tendsto
      (fun n : ℕ => C_adjoint lam alpha hlam ha
        (C lam alpha hlam ha (u n)))
      Filter.atTop
      (nhds (C_adjoint lam alpha hlam ha
        (0 : InfiniteAnalysis.FockCoefficients))) :=
    (C_adjoint lam alpha hlam ha).continuous.continuousAt.tendsto.comp hC
  simpa only [map_zero] using hG

/-- A single unit sequence simultaneously controls the canonical
positive polar amplitude, the Fock transform and its source Gram.
The Gram estimate follows from the adjoint operator norm, not from
an assumed spectral gap. -/
theorem exists_shared_cfc_fock_gram_quantitative_family
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      ∀ n : ℕ,
        ‖u n‖ = 1 ∧
        ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ <
          1 / ((n : ℝ) + 1) ∧
        ‖C lam alpha hlam ha (u n)‖ =
          ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ ∧
        ‖gram lam alpha hlam ha (u n)‖ ≤
          ‖C_adjoint lam alpha hlam ha‖ * (1 / ((n : ℝ) + 1)) := by
  classical
  obtain ⟨W, u, hcompact, hinj, hdense, hnotclosed, hpolar, hquant⟩ :=
    exists_shared_cfc_polar_instability_family lam alpha hlam ha
  refine ⟨u, ?_⟩
  intro n
  refine ⟨(hquant n).1, (hquant n).2.2, (hquant n).2.1, ?_⟩
  have hCbound : ‖C lam alpha hlam ha (u n)‖ ≤
      1 / ((n : ℝ) + 1) := by
    rw [(hquant n).2.1]
    exact (hquant n).2.2.le
  calc
    ‖gram lam alpha hlam ha (u n)‖ =
        ‖C_adjoint lam alpha hlam ha (C lam alpha hlam ha (u n))‖ := rfl
    _ ≤ ‖C_adjoint lam alpha hlam ha‖ *
        ‖C lam alpha hlam ha (u n)‖ :=
      (C_adjoint lam alpha hlam ha).le_opNorm _
    _ ≤ ‖C_adjoint lam alpha hlam ha‖ * (1 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hCbound (norm_nonneg _)

/-- At every source point f there are norm-one perturbations which are
invisible in the limit simultaneously to the true Fock transform, its
canonical CFC positive root and the source Gram. This is a translated
form of the certified common normalized approximate-null sequence. -/
theorem exists_shared_cfc_fock_gram_everywhere_instability
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ∃ v : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖v n - f‖ = 1) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          localCFCGramSqrt lam alpha hlam ha (v n) -
            localCFCGramSqrt lam alpha hlam ha f)
        Filter.atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          C lam alpha hlam ha (v n) -
            C lam alpha hlam ha f)
        Filter.atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          gram lam alpha hlam ha (v n) -
            gram lam alpha hlam ha f)
        Filter.atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
  obtain ⟨u, hunit, hP, hC, hG⟩ :=
    exists_shared_cfc_fock_gram_strong_null_sequence lam alpha hlam ha
  refine ⟨(fun n => u n + f), ?_, ?_, ?_, ?_⟩
  · intro n
    simpa only [add_sub_cancel_right] using hunit n
  · simpa only [map_add, add_sub_cancel_right] using hP
  · simpa only [map_add, add_sub_cancel_right] using hC
  · simpa only [map_add, add_sub_cancel_right] using hG

/-- At any source f, perturbations of size exactly one can have
simultaneously arbitrarily small changes in the true Fock measurements,
the canonical CFC square-root image, and the Gram image. The bounds
are quantitative and use the *same* perturbation sequence. -/
theorem exists_shared_cfc_fock_gram_quantitative_everywhere_instability
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ∃ v : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      ∀ n : ℕ,
        ‖v n - f‖ = 1 ∧
        ‖localCFCGramSqrt lam alpha hlam ha (v n) -
          localCFCGramSqrt lam alpha hlam ha f‖ <
          1 / ((n : ℝ) + 1) ∧
        ‖C lam alpha hlam ha (v n) -
          C lam alpha hlam ha f‖ =
          ‖localCFCGramSqrt lam alpha hlam ha (v n) -
            localCFCGramSqrt lam alpha hlam ha f‖ ∧
        ‖gram lam alpha hlam ha (v n) -
          gram lam alpha hlam ha f‖ ≤
          ‖C_adjoint lam alpha hlam ha‖ *
            (1 / ((n : ℝ) + 1)) := by
  obtain ⟨u, hquant⟩ :=
    exists_shared_cfc_fock_gram_quantitative_family lam alpha hlam ha
  refine ⟨(fun n => u n + f), ?_⟩
  intro n
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [add_sub_cancel_right] using (hquant n).1
  · simpa only [map_add, add_sub_cancel_right] using (hquant n).2.1
  · simpa only [map_add, add_sub_cancel_right] using (hquant n).2.2.1
  · simpa only [map_add, add_sub_cancel_right] using (hquant n).2.2.2

/-- At any source and for any prescribed positive measurement error,
there exists a perturbation of norm exactly one whose three measured
changes (the canonical CFC root, Fock transform, and genuine source
Gram) are all smaller than that error. -/
theorem exists_unit_perturbation_with_arbitrarily_small_joint_measurements
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ v : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖v - f‖ = 1 ∧
      ‖localCFCGramSqrt lam alpha hlam ha v -
        localCFCGramSqrt lam alpha hlam ha f‖ < eps ∧
      ‖C lam alpha hlam ha v - C lam alpha hlam ha f‖ < eps ∧
      ‖gram lam alpha hlam ha v - gram lam alpha hlam ha f‖ < eps := by
  obtain ⟨v, hunit, hP, hC, hG⟩ :=
    exists_shared_cfc_fock_gram_everywhere_instability
      lam alpha hlam ha f
  have hIio : Set.Iio eps ∈ nhds (0 : ℝ) :=
    isOpen_Iio.mem_nhds heps
  have hPsmall : ∀ᶠ n in Filter.atTop,
      ‖localCFCGramSqrt lam alpha hlam ha (v n) -
        localCFCGramSqrt lam alpha hlam ha f‖ < eps := by
    have hnorm : Filter.Tendsto
        (fun n : ℕ =>
          ‖localCFCGramSqrt lam alpha hlam ha (v n) -
            localCFCGramSqrt lam alpha hlam ha f‖)
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa using hP.norm
    simpa only [Set.mem_Iio] using hnorm.eventually hIio
  have hCsmall : ∀ᶠ n in Filter.atTop,
      ‖C lam alpha hlam ha (v n) - C lam alpha hlam ha f‖ < eps := by
    have hnorm : Filter.Tendsto
        (fun n : ℕ =>
          ‖C lam alpha hlam ha (v n) - C lam alpha hlam ha f‖)
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa using hC.norm
    simpa only [Set.mem_Iio] using hnorm.eventually hIio
  have hGsmall : ∀ᶠ n in Filter.atTop,
      ‖gram lam alpha hlam ha (v n) - gram lam alpha hlam ha f‖ < eps := by
    have hnorm : Filter.Tendsto
        (fun n : ℕ =>
          ‖gram lam alpha hlam ha (v n) - gram lam alpha hlam ha f‖)
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa using hG.norm
    simpa only [Set.mem_Iio] using hnorm.eventually hIio
  obtain ⟨n, hn⟩ := (hPsmall.and (hCsmall.and hGsmall)).exists
  exact ⟨v n, hunit n, hn.1, hn.2.1, hn.2.2⟩

/-- Even a nonlinear exact reconstruction from all three joint
measurements (canonical CFC root, true Fock output and source Gram)
cannot be continuous at the measurements of *any* source point.
The inverse is allowed to be an arbitrary function on the whole
ambient product; no linearity or boundedness is assumed. -/
theorem joint_cfc_fock_gram_exact_reconstruction_discontinuous_everywhere
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ∀ (r :
      (Lp ℂ 2 (Ultraspherical.measure lam) ×
        (InfiniteAnalysis.FockCoefficients ×
          Lp ℂ 2 (Ultraspherical.measure lam))) →
        Lp ℂ 2 (Ultraspherical.measure lam)),
      (∀ x : Lp ℂ 2 (Ultraspherical.measure lam),
        r (localCFCGramSqrt lam alpha hlam ha x,
          (C lam alpha hlam ha x, gram lam alpha hlam ha x)) = x) →
      ¬ ContinuousAt r
        (localCFCGramSqrt lam alpha hlam ha f,
          (C lam alpha hlam ha f, gram lam alpha hlam ha f)) := by
  obtain ⟨v, hunit, hP, hC, hG⟩ :=
    exists_shared_cfc_fock_gram_everywhere_instability
      lam alpha hlam ha f
  have hPto : Filter.Tendsto
      (fun n : ℕ => localCFCGramSqrt lam alpha hlam ha (v n))
      Filter.atTop
      (nhds (localCFCGramSqrt lam alpha hlam ha f)) := by
    have hc : Continuous (fun z : Lp ℂ 2 (Ultraspherical.measure lam) =>
        z + localCFCGramSqrt lam alpha hlam ha f) :=
      continuous_id.add continuous_const
    have h := hc.continuousAt.tendsto.comp hP
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  have hCto : Filter.Tendsto
      (fun n : ℕ => C lam alpha hlam ha (v n))
      Filter.atTop (nhds (C lam alpha hlam ha f)) := by
    have hc : Continuous (fun z : InfiniteAnalysis.FockCoefficients =>
        z + C lam alpha hlam ha f) :=
      continuous_id.add continuous_const
    have h := hc.continuousAt.tendsto.comp hC
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  have hGto : Filter.Tendsto
      (fun n : ℕ => gram lam alpha hlam ha (v n))
      Filter.atTop (nhds (gram lam alpha hlam ha f)) := by
    have hc : Continuous (fun z : Lp ℂ 2 (Ultraspherical.measure lam) =>
        z + gram lam alpha hlam ha f) :=
      continuous_id.add continuous_const
    have h := hc.continuousAt.tendsto.comp hG
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  have hpair : Filter.Tendsto
      (fun n : ℕ =>
        (localCFCGramSqrt lam alpha hlam ha (v n),
          (C lam alpha hlam ha (v n), gram lam alpha hlam ha (v n))))
      Filter.atTop
      (nhds (localCFCGramSqrt lam alpha hlam ha f,
          (C lam alpha hlam ha f, gram lam alpha hlam ha f))) :=
    (hPto.prodMk_nhds (hCto.prodMk_nhds hGto))
  intro r hleft hcont
  have hrec : Filter.Tendsto
      (fun n : ℕ =>
        r (localCFCGramSqrt lam alpha hlam ha (v n),
          (C lam alpha hlam ha (v n), gram lam alpha hlam ha (v n))))
      Filter.atTop
      (nhds (r (localCFCGramSqrt lam alpha hlam ha f,
        (C lam alpha hlam ha f, gram lam alpha hlam ha f)))) :=
    hcont.tendsto.comp hpair
  have heq : (fun n : ℕ =>
        r (localCFCGramSqrt lam alpha hlam ha (v n),
          (C lam alpha hlam ha (v n), gram lam alpha hlam ha (v n)))) = v := by
    funext n
    exact hleft (v n)
  rw [heq, hleft f] at hrec
  have hdiff : Filter.Tendsto (fun n : ℕ => v n - f)
      Filter.atTop
      (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    have hc : Continuous (fun z : Lp ℂ 2 (Ultraspherical.measure lam) =>
        z - f) := continuous_id.sub continuous_const
    have h := hc.continuousAt.tendsto.comp hrec
    simpa only [Function.comp_def, sub_self] using h
  have hnormzero : Filter.Tendsto
      (fun n : ℕ => ‖v n - f‖)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hdiff.norm
  have hnormone : Filter.Tendsto
      (fun n : ℕ => ‖v n - f‖)
      Filter.atTop (nhds (1 : ℝ)) := by
    have hh : (fun n : ℕ => ‖v n - f‖) =
        (fun _ : ℕ => (1 : ℝ)) := by
      funext n
      exact hunit n
    rw [hh]
    exact tendsto_const_nhds
  have himpossible : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hnormzero hnormone
  norm_num at himpossible

/-- The joint measurement map into the true ambient product. -/
private def jointCFCFockGramMeasurements
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (x : Lp ℂ 2 (Ultraspherical.measure lam)) :
    Lp ℂ 2 (Ultraspherical.measure lam) ×
      (InfiniteAnalysis.FockCoefficients ×
        Lp ℂ 2 (Ultraspherical.measure lam)) :=
  (localCFCGramSqrt lam alpha hlam ha x,
    (C lam alpha hlam ha x, gram lam alpha hlam ha x))

/-- The exact inverse defined only on the *actual range* of the joint
CFC--Fock--Gram measurements (with its genuine subtype topology)
is discontinuous at the measured data of every source f.
Unlike a statement about an ambient-space extension, no extension
of the inverse outside the range is assumed. -/
theorem joint_cfc_fock_gram_inverse_on_actual_range_discontinuous_everywhere
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ∀ (r :
      Set.range (jointCFCFockGramMeasurements lam alpha hlam ha) →
        Lp ℂ 2 (Ultraspherical.measure lam)),
      (∀ x : Lp ℂ 2 (Ultraspherical.measure lam),
        r ⟨jointCFCFockGramMeasurements lam alpha hlam ha x,
          ⟨x, rfl⟩⟩ = x) →
      ¬ ContinuousAt r
        (⟨jointCFCFockGramMeasurements lam alpha hlam ha f,
          ⟨f, rfl⟩⟩ :
            Set.range (jointCFCFockGramMeasurements lam alpha hlam ha)) := by
  obtain ⟨v, hunit, hP, hC, hG⟩ :=
    exists_shared_cfc_fock_gram_everywhere_instability
      lam alpha hlam ha f
  have hPto : Filter.Tendsto
      (fun n : ℕ => localCFCGramSqrt lam alpha hlam ha (v n))
      Filter.atTop
      (nhds (localCFCGramSqrt lam alpha hlam ha f)) := by
    have hc : Continuous (fun z : Lp ℂ 2 (Ultraspherical.measure lam) =>
        z + localCFCGramSqrt lam alpha hlam ha f) :=
      continuous_id.add continuous_const
    have h := hc.continuousAt.tendsto.comp hP
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  have hCto : Filter.Tendsto
      (fun n : ℕ => C lam alpha hlam ha (v n))
      Filter.atTop (nhds (C lam alpha hlam ha f)) := by
    have hc : Continuous (fun z : InfiniteAnalysis.FockCoefficients =>
        z + C lam alpha hlam ha f) :=
      continuous_id.add continuous_const
    have h := hc.continuousAt.tendsto.comp hC
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  have hGto : Filter.Tendsto
      (fun n : ℕ => gram lam alpha hlam ha (v n))
      Filter.atTop (nhds (gram lam alpha hlam ha f)) := by
    have hc : Continuous (fun z : Lp ℂ 2 (Ultraspherical.measure lam) =>
        z + gram lam alpha hlam ha f) :=
      continuous_id.add continuous_const
    have h := hc.continuousAt.tendsto.comp hG
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  have hpair : Filter.Tendsto
      (fun n : ℕ => jointCFCFockGramMeasurements lam alpha hlam ha (v n))
      Filter.atTop
      (nhds (jointCFCFockGramMeasurements lam alpha hlam ha f)) := by
    change Filter.Tendsto
      (fun n : ℕ =>
        (localCFCGramSqrt lam alpha hlam ha (v n),
          (C lam alpha hlam ha (v n), gram lam alpha hlam ha (v n))))
      Filter.atTop
      (nhds (localCFCGramSqrt lam alpha hlam ha f,
        (C lam alpha hlam ha f, gram lam alpha hlam ha f)))
    exact (hPto.prodMk_nhds (hCto.prodMk_nhds hGto))
  intro r hleft hcont
  have hsub : Filter.Tendsto
      (fun n : ℕ =>
        (⟨jointCFCFockGramMeasurements lam alpha hlam ha (v n),
          ⟨v n, rfl⟩⟩ :
          Set.range (jointCFCFockGramMeasurements lam alpha hlam ha)))
      Filter.atTop
      (nhds (⟨jointCFCFockGramMeasurements lam alpha hlam ha f,
        ⟨f, rfl⟩⟩ :
        Set.range (jointCFCFockGramMeasurements lam alpha hlam ha))) := by
    apply tendsto_subtype_rng.mpr
    exact hpair
  have hrec : Filter.Tendsto
      (fun n : ℕ => r
        (⟨jointCFCFockGramMeasurements lam alpha hlam ha (v n),
          ⟨v n, rfl⟩⟩ :
          Set.range (jointCFCFockGramMeasurements lam alpha hlam ha)))
      Filter.atTop
      (nhds (r
        (⟨jointCFCFockGramMeasurements lam alpha hlam ha f,
          ⟨f, rfl⟩⟩ :
          Set.range (jointCFCFockGramMeasurements lam alpha hlam ha)))) :=
    hcont.tendsto.comp hsub
  have heq : (fun n : ℕ => r
        (⟨jointCFCFockGramMeasurements lam alpha hlam ha (v n),
          ⟨v n, rfl⟩⟩ :
          Set.range (jointCFCFockGramMeasurements lam alpha hlam ha))) = v := by
    funext n
    exact hleft (v n)
  rw [heq, hleft f] at hrec
  have hdiff : Filter.Tendsto (fun n : ℕ => v n - f)
      Filter.atTop
      (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    have hc : Continuous (fun z : Lp ℂ 2 (Ultraspherical.measure lam) =>
        z - f) := continuous_id.sub continuous_const
    have h := hc.continuousAt.tendsto.comp hrec
    simpa only [Function.comp_def, sub_self] using h
  have hnormzero : Filter.Tendsto
      (fun n : ℕ => ‖v n - f‖)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hdiff.norm
  have hnormone : Filter.Tendsto
      (fun n : ℕ => ‖v n - f‖)
      Filter.atTop (nhds (1 : ℝ)) := by
    have hh : (fun n : ℕ => ‖v n - f‖) =
        (fun _ : ℕ => (1 : ℝ)) := by
      funext n
      exact hunit n
    rw [hh]
    exact tendsto_const_nhds
  have himpossible : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hnormzero hnormone
  norm_num at himpossible

/-- There is no globally continuous exact reconstruction map from
the actual joint CFC--Fock--Gram measurement range to its full source
Hilbert space. The inverse is tested on the genuine subtype range,
rather than on an artificial enlargement of the data domain. -/
theorem joint_cfc_fock_gram_no_continuous_exact_inverse_on_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ ∃ (r :
      Set.range (jointCFCFockGramMeasurements lam alpha hlam ha) →
        Lp ℂ 2 (Ultraspherical.measure lam)),
      Continuous r ∧
      ∀ x : Lp ℂ 2 (Ultraspherical.measure lam),
        r ⟨jointCFCFockGramMeasurements lam alpha hlam ha x,
          ⟨x, rfl⟩⟩ = x := by
  rintro ⟨r, hcont, hleft⟩
  exact (joint_cfc_fock_gram_inverse_on_actual_range_discontinuous_everywhere
    lam alpha hlam ha
    (0 : Lp ℂ 2 (Ultraspherical.measure lam))
    r hleft) hcont.continuousAt

#print axioms GegenbauerFock.GeneralUltrasphericalFock.joint_cfc_fock_gram_no_continuous_exact_inverse_on_range

#print axioms GegenbauerFock.GeneralUltrasphericalFock.joint_cfc_fock_gram_inverse_on_actual_range_discontinuous_everywhere

#print axioms GegenbauerFock.GeneralUltrasphericalFock.joint_cfc_fock_gram_exact_reconstruction_discontinuous_everywhere

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_unit_perturbation_with_arbitrarily_small_joint_measurements

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_fock_gram_quantitative_everywhere_instability

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_fock_gram_everywhere_instability

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_fock_gram_quantitative_family

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_fock_gram_strong_null_sequence

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_polar_strong_null_sequence

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_polar_instability_family

end GegenbauerFock.GeneralUltrasphericalFock
