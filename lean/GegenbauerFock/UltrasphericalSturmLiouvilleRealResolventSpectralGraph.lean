import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedFullResolvent
import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedSymmetry

/-!
# V007 — concrete full-L² positive resolvent and closed Sturm spectral graph

The bounded positive-shift resolvent already constructed from the finite
polynomial inverse is now related to the genuine closed Sturm graph
in BOTH directions. In particular the closure graph equals the range
of the bounded resolvent parametrization

  f ↦ (R_t f, t R_t f - f).

The resolvent is Hilbert symmetric, an essential prerequisite to
applying the bounded selfadjoint spectral theorem later. This is an
exact resolvent characterization of the graph, not a construction
of a full discrete Gegenbauer orthonormal eigenbasis.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Genuine symmetry of the bounded full weighted-real-L² resolvent,
proved from symmetry of the CLOSED Sturm graph and its full inverse
relation, for all L² vectors (not just polynomials). -/
theorem sturmRealPositiveResolventFullCLM_inner_symmetric
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f g : SturmH lam) :
    inner ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht f) g =
      inner ℝ f (sturmRealPositiveResolventFullCLM lam t hlam ht g) := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  obtain ⟨x, hx⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f)
  obtain ⟨y, hy⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht g)
  have hxf : (x : SturmH lam) = R f := congrArg Prod.fst hx
  have hax : A.closure x = t • R f - f := congrArg Prod.snd hx
  have hyg : (y : SturmH lam) = R g := congrArg Prod.fst hy
  have hay : A.closure y = t • R g - g := congrArg Prod.snd hy
  have hsym := sturmRealPartialOperator_closure_symmetric lam hlam x y
  rw [hxf, hax, hyg, hay] at hsym
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right] at hsym
  dsimp [R]
  linarith

/-- The canonical closed Sturm operator has a concrete inverse for
all strictly positive shifts. Applying the bounded resolvent to
(tI - Abar)x RECOVERS the original domain vector x exactly. -/
theorem sturmRealPositiveResolventFullCLM_left_inverse_closed_shift
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
      (t • (x : SturmH lam) -
        (sturmRealPartialOperator lam hlam).closure x) =
      (x : SturmH lam) := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let f : SturmH lam := t • (x : SturmH lam) - A.closure x
  obtain ⟨y, hy⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f)
  have hy1 : (y : SturmH lam) = R f := congrArg Prod.fst hy
  have hy2 : A.closure y = t • R f - f := congrArg Prod.snd hy
  have hshift_y : t • (y : SturmH lam) - A.closure y = f := by
    rw [hy1, hy2]
    abel
  have hzero :
      t • ((y - x : A.closure.domain) : SturmH lam) -
        A.closure (y - x) = 0 := by
    have hmap : A.closure (y - x) =
        A.closure y - A.closure x := A.closure.map_sub y x
    rw [hmap]
    simp only [Submodule.coe_sub]
    calc
      t • ((y : SturmH lam) - (x : SturmH lam)) -
          (A.closure y - A.closure x) =
        (t • (y : SturmH lam) - A.closure y) -
          (t • (x : SturmH lam) - A.closure x) := by abel
      _ = 0 := sub_eq_zero.mpr hshift_y
  have hxy : y = x :=
    sub_eq_zero.mp (sturmRealClosedPositiveShift_kernel
      lam t hlam ht (y - x) hzero)
  change R f = (x : SturmH lam)
  exact hy1.symm.trans (congrArg Subtype.val hxy)

/-- The COMPLETE closed Sturm graph is parametrized exactly by
the bounded full-Hilbert resolvent; the reverse inclusion uses
injectivity of the closed positive shift. -/
theorem sturmRealClosed_graph_eq_full_resolvent_range
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ((sturmRealPartialOperator lam hlam).closure.graph :
      Set (SturmH lam × SturmH lam)) =
    Set.range (fun f : SturmH lam =>
      (sturmRealPositiveResolventFullCLM lam t hlam ht f,
       t • sturmRealPositiveResolventFullCLM lam t hlam ht f - f)) := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (A.closure.mem_graph_iff').mp hz
    let f : SturmH lam := t • (x : SturmH lam) - A.closure x
    refine ⟨f, ?_⟩
    have hR : R f = (x : SturmH lam) :=
      sturmRealPositiveResolventFullCLM_left_inverse_closed_shift
        lam t hlam ht x
    change (R f, t • R f - f) = z
    rw [hR, ← hx]
    simp only [f]
    congr 1
    abel
  · rintro ⟨f, rfl⟩
    exact sturmRealPositiveResolventFullCLM_closed_graph
      lam t hlam ht f

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_inner_symmetric
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_left_inverse_closed_shift
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_graph_eq_full_resolvent_range

end GegenbauerFock.Ultraspherical
