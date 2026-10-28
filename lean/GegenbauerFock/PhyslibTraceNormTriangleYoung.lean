/-
Copyright (c) 2026 Tom Ole Diem.
Released under Apache-2.0.
Adapted for V007 from PhyslibAlpha/ProbabilisticTheory/HilbertSpace/
TraceClass/IdealNorm.lean, using an elementary quadratic (Young) bound.
-/
import GegenbauerFock.PhyslibTraceNormSqrtAbsEnergy
import GegenbauerFock.PhyslibHSRightBasisEnergyBound
import GegenbauerFock.PhyslibTraceClassAdditionFromHS

/-!
# V007 — full CFC trace-norm triangle inequality from HS energy duality

The core argument avoids assuming any trace-norm triangle property.
For trace class T and a contraction W, write T = R*S with
S = sqrt(|T|), R = polarFactor(T)*S.  The norm of the diagonal
pairing is bounded by (‖R* W e_i‖²+‖S e_i‖²)/2.
The sharp S₂ right-ideal energy estimate and the pointwise left
polar contraction both bound those energies by the HS energy of S,
which is exactly the trace norm of T.

Apply the bound separately to the two summands, using the polar
factor of their sum, to obtain full subadditivity. In contrast with
previous positive-cone results, no positivity or finite rank of
either summand is assumed.

This is a separately audited candidate. Do not count it as
kernel-certified until exact-SHA CI and the axiom audit succeed.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Absolute diagonal pairing against an arbitrary contraction
is summable and has sum at most the CFC trace norm. -/
theorem norm_inner_contraction_tsum_le_traceNorm_young
    (T W : H →L[ℂ] H) (hT : IsTraceClass T) (hW : ‖W‖ ≤ 1)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => ‖inner ℂ (W (b i)) (T (b i))‖) ∧
      (∑' i : w, ‖inner ℂ (W (b i)) (T (b i))‖) ≤ traceNorm T hT := by
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  let R : H →L[ℂ] H := (Polar.polarFactor T).comp S
  let D : H →L[ℂ] H := R.adjoint.comp W
  have hR : HilbertSchmidt.IsHilbertSchmidt R :=
    traceClass_polar_sqrt_abs_isHS T hT
  have hS : HilbertSchmidt.IsHilbertSchmidt S :=
    traceClass_sqrt_abs_isHS T hT
  have hRstar : HilbertSchmidt.IsHilbertSchmidt R.adjoint :=
    HilbertSchmidt.isHilbertSchmidt_adjoint R hR
  have hD : HilbertSchmidt.IsHilbertSchmidt D :=
    HilbertSchmidt.isHilbertSchmidt_comp_right R.adjoint hRstar W
  have hDSum : Summable (fun i : w => ‖D (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hD
  have hSSum : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hS
  have hRSum : Summable (fun i : w => ‖R (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hR
  have hRstarSum : Summable (fun i : w => ‖R.adjoint (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hRstar
  have hSS : S * S = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  have hfactor : R * S = T := by
    calc
      R * S = (Polar.polarFactor T * S) * S := rfl
      _ = Polar.polarFactor T * (S * S) := mul_assoc _ _ _
      _ = Polar.polarFactor T * CFC.abs T := by rw [hSS]
      _ = T := Polar.polarFactor_mul_absOperator T
  have hpoint (i : w) :
      inner ℂ (W (b i)) (T (b i)) =
        inner ℂ (D (b i)) (S (b i)) := by
    calc
      inner ℂ (W (b i)) (T (b i)) =
          inner ℂ (W (b i)) (R (S (b i))) := by
        rw [← hfactor]
        rfl
      _ = inner ℂ (R.adjoint (W (b i))) (S (b i)) :=
        (ContinuousLinearMap.adjoint_inner_left R (S (b i)) (W (b i))).symm
      _ = inner ℂ (D (b i)) (S (b i)) := rfl
  have hYoung (i : w) :
      ‖inner ℂ (W (b i)) (T (b i))‖ ≤
        (1/2 : ℝ) * (‖D (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2) := by
    rw [hpoint i]
    have hc : ‖inner ℂ (D (b i)) (S (b i))‖ ≤
        ‖D (b i)‖ * ‖S (b i)‖ :=
      norm_inner_le_norm _ _
    nlinarith [sq_nonneg (‖D (b i)‖ - ‖S (b i)‖)]
  have hMajor : Summable (fun i : w =>
      (1/2 : ℝ) * (‖D (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2)) :=
    (hDSum.add hSSum).mul_left (1/2 : ℝ)
  have hPair : Summable (fun i : w =>
      ‖inner ℂ (W (b i)) (T (b i))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hYoung hMajor
  have hDleRstar :
      (∑' i : w, ‖D (b i)‖ ^ 2) ≤
      ∑' i : w, ‖R.adjoint (b i)‖ ^ 2 := by
    change (∑' i : w, ‖(R.adjoint.comp W) (b i)‖ ^ 2) ≤ _
    have h := HilbertSchmidt.right_basis_energy_le R.adjoint hRstar W b
    have hWsq : ‖W‖ ^ 2 ≤ (1:ℝ) :=
      (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hW
    have hsumNonneg :
        (0:ℝ) ≤ ∑' i : w, ‖R.adjoint (b i)‖ ^ 2 :=
      tsum_nonneg (fun i => sq_nonneg _)
    calc
      _ ≤ ‖W‖ ^ 2 * (∑' i : w, ‖R.adjoint (b i)‖ ^ 2) := h
      _ ≤ (1:ℝ) * (∑' i : w, ‖R.adjoint (b i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hWsq hsumNonneg
      _ = _ := one_mul _
  have hRstarEqR :
      (∑' i : w, ‖R.adjoint (b i)‖ ^ 2) =
      ∑' i : w, ‖R (b i)‖ ^ 2 :=
    (HilbertSchmidt.hasSum_norm_sq_apply_eq_adjoint b b hRSum).tsum_eq
  have hRleS :
      (∑' i : w, ‖R (b i)‖ ^ 2) ≤
      ∑' i : w, ‖S (b i)‖ ^ 2 := by
    have hp (i : w) : ‖R (b i)‖ ^ 2 ≤ ‖S (b i)‖ ^ 2 := by
      have hc : ‖R (b i)‖ ≤ ‖S (b i)‖ :=
        Polar.polarFactor_norm_le T (S (b i))
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hc
    exact hRSum.tsum_le_tsum hp hSSum
  have hDleS :
      (∑' i : w, ‖D (b i)‖ ^ 2) ≤
      ∑' i : w, ‖S (b i)‖ ^ 2 := by
    calc
      _ ≤ ∑' i : w, ‖R.adjoint (b i)‖ ^ 2 := hDleRstar
      _ = ∑' i : w, ‖R (b i)‖ ^ 2 := hRstarEqR
      _ ≤ ∑' i : w, ‖S (b i)‖ ^ 2 := hRleS
  constructor
  · exact hPair
  · calc
      (∑' i : w, ‖inner ℂ (W (b i)) (T (b i))‖) ≤
          ∑' i : w, (1/2 : ℝ) *
            (‖D (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2) :=
        hPair.tsum_le_tsum hYoung hMajor
      _ = (1/2 : ℝ) *
          ((∑' i : w, ‖D (b i)‖ ^ 2) +
            (∑' i : w, ‖S (b i)‖ ^ 2)) := by
        rw [tsum_mul_left, hDSum.tsum_add hSSum]
      _ ≤ (1/2 : ℝ) *
          ((∑' i : w, ‖S (b i)‖ ^ 2) +
            (∑' i : w, ‖S (b i)‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add_right hDleS _) (by norm_num)
      _ = ∑' i : w, ‖S (b i)‖ ^ 2 := by ring
      _ = traceNorm T hT := (traceNorm_eq_sqrt_abs_basisEnergy T hT b).symm

/-- The unrestricted Schatten-S₁ norm triangle inequality
for arbitrary bounded trace-class endomorphisms. -/
theorem traceNorm_add_le_via_hsYoung
    (T V : H →L[ℂ] H)
    (hT : IsTraceClass T) (hV : IsTraceClass V)
    (hTV : IsTraceClass (T + V)) :
    traceNorm (T + V) hTV ≤ traceNorm T hT + traceNorm V hV := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let W : H →L[ℂ] H := Polar.polarFactor (T + V)
  have hW : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le (T + V)
  have hPairTV := (norm_inner_contraction_tsum_le_traceNorm_young
    (T + V) W hTV hW b).1
  have hPairT := norm_inner_contraction_tsum_le_traceNorm_young T W hT hW b
  have hPairV := norm_inner_contraction_tsum_le_traceNorm_young V W hV hW b
  have hreal : Summable (fun i : w =>
      (inner ℂ (b i) (CFC.abs (T + V) (b i))).re) :=
    summable_inner_abs_of_hilbertBasis hTV b
  have hpolar (i : w) :
      inner ℂ (b i) (CFC.abs (T + V) (b i)) =
        inner ℂ (W (b i)) ((T + V) (b i)) := by
    have h := Polar.star_polarFactor_mul_self (T + V)
    change star W * (T + V) = CFC.abs (T + V) at h
    rw [← h, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_right W
      (b i) ((T + V) (b i))
  have htri (i : w) :
      ‖inner ℂ (W (b i)) ((T + V) (b i))‖ ≤
        ‖inner ℂ (W (b i)) (T (b i))‖ +
        ‖inner ℂ (W (b i)) (V (b i))‖ := by
    rw [ContinuousLinearMap.add_apply, inner_add_right]
    exact norm_add_le _ _
  calc
    traceNorm (T + V) hTV =
        ∑' i : w, (inner ℂ (b i) (CFC.abs (T + V) (b i))).re :=
      traceNorm_eq_of_hilbertBasis hTV b
    _ ≤ ∑' i : w, ‖inner ℂ (W (b i)) ((T + V) (b i))‖ :=
      hreal.tsum_le_tsum
        (fun i => by rw [hpolar i]; exact Complex.re_le_norm _)
        hPairTV
    _ ≤ ∑' i : w, (‖inner ℂ (W (b i)) (T (b i))‖ +
        ‖inner ℂ (W (b i)) (V (b i))‖) :=
      hPairTV.tsum_le_tsum htri (hPairT.1.add hPairV.1)
    _ = (∑' i : w, ‖inner ℂ (W (b i)) (T (b i))‖) +
        (∑' i : w, ‖inner ℂ (W (b i)) (V (b i))‖) :=
      hPairT.1.tsum_add hPairV.1
    _ ≤ traceNorm T hT + traceNorm V hV :=
      add_le_add hPairT.2 hPairV.2

#print axioms ProbabilisticTheory.norm_inner_contraction_tsum_le_traceNorm_young
#print axioms ProbabilisticTheory.traceNorm_add_le_via_hsYoung

end ProbabilisticTheory
