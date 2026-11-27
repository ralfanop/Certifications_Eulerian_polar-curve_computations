import Mathlib
import M16KreinSpatial
import M16KreinDomains
import M16KreinOperator

namespace M16KreinGraphGap
open M16KreinDomains

-- Proposition 9.12: the Hilbert pairing induced by conjugate fundamental symmetries.
theorem fundamental_pairing_transport {E R : Type*}
    (p : E → E → R) (u : E ≃ E) (s s' : E → E)
    (hu : ∀ x y, p (u x) (u y) = p x y)
    (hs : ∀ y, s' (u y) = u (s y)) :
    ∀ x y, p (u x) (s' (u y)) = p x (s y) := by
  intro x y
  rw [hs, hu]

-- A bounded resolvent is an equivalence on a graph, not a total extension
-- of the densely defined diagonal realization.
def GraphResolvent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : Set (E × E)) (z : ℂ) (R : E →L[ℂ] E) : Prop :=
  ∀ x f, (x, f + z • x) ∈ G ↔ x = R f

theorem transport_graph_resolvent {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u : E ≃L[ℂ] F) (G : Set (E × E)) (z : ℂ) (R : E →L[ℂ] E)
    (h : GraphResolvent G z R) :
    GraphResolvent (transport u.toLinearEquiv.toEquiv G) z
      (u.toContinuousLinearMap.comp (R.comp u.symm.toContinuousLinearMap)) := by
  intro x f
  change (u.symm x, u.symm (f + z • x)) ∈ G ↔ x = u (R (u.symm f))
  rw [map_add, map_smul, h (u.symm x) (u.symm f)]
  constructor
  · intro hh
    calc
      x = u (u.symm x) := (u.apply_symm_apply x).symm
      _ = _ := congrArg u hh
  · intro hh
    rw [hh, u.symm_apply_apply]

def diagonalGraph {E F : Type*} (GA : Set (E × E)) (GD : Set (F × F)) :
    Set ((E × F) × (E × F)) :=
  {w | (w.1.1,w.2.1) ∈ GA ∧ (w.1.2,w.2.2) ∈ GD}

def weightedPair {E F : Type*} (pE : E → E → ℂ) (pF : F → F → ℂ)
    (x y : E × F) : ℂ := pE x.1 y.1 - 2 * pF x.2 y.2

-- Equality of the entire diagonal adjoint graphs, using the two zero
-- vectors to recover each adjoint-domain condition separately.
theorem adjGraph_weighted_diagonal {E F : Type*} [Zero E] [Zero F]
    (pE : E → E → ℂ) (pF : F → F → ℂ)
    (GA : Set (E × E)) (GD : Set (F × F))
    (hE0 : ∀ x, pE 0 x = 0) (hF0 : ∀ x, pF 0 x = 0)
    (hGA0 : (0,0) ∈ GA) (hGD0 : (0,0) ∈ GD) :
    adjGraph (weightedPair pE pF) (diagonalGraph GA GD) =
      diagonalGraph (adjGraph pE GA) (adjGraph pF GD) := by
  ext w
  change (∀ x y : E × F, ((x.1,y.1) ∈ GA ∧ (x.2,y.2) ∈ GD) →
    weightedPair pE pF y w.1 = weightedPair pE pF x w.2) ↔
    ((∀ x y, (x,y) ∈ GA → pE y w.1.1 = pE x w.2.1) ∧
     (∀ x y, (x,y) ∈ GD → pF y w.1.2 = pF x w.2.2))
  constructor
  · intro h
    constructor
    · intro x y hxy
      have hh := h (x,0) (y,0) ⟨hxy,hGD0⟩
      simpa [weightedPair,hF0] using hh
    · intro x y hxy
      have hh := h (0,x) (0,y) ⟨hGA0,hxy⟩
      simp only [weightedPair, hE0, zero_sub] at hh
      linear_combination (-1/2 : ℂ) * hh
  · rintro ⟨hE,hF⟩ x y ⟨hx,hy⟩
    unfold weightedPair
    rw [hE _ _ hx, hF _ _ hy]

-- Proposition 9.13: full graph equality, conditional on the diagonal
-- adjoint graph equalities as in the proposition. Both cross-pairing
-- identities express weighted symmetry in the complexification.
theorem weighted_block_selfAdjoint_graph {E F : Type*}
    [AddCommGroup E] [AddCommGroup F]
    (pE : E → E → ℂ) (pF : F → F → ℂ)
    (GA : Set (E × E)) (GD : Set (F × F))
    (X : F → E) (Y : E → F)
    (hE0 : ∀ x, pE 0 x = 0) (hF0 : ∀ x, pF 0 x = 0)
    (hGA0 : (0,0) ∈ GA) (hGD0 : (0,0) ∈ GD)
    (he : ∀ x y z, pE (x+y) z = pE x z + pE y z)
    (hf : ∀ x y z, pF (x+y) z = pF x z + pF y z)
    (hes : ∀ x y z, pE x (y-z) = pE x y - pE x z)
    (hfs : ∀ x y z, pF x (y-z) = pF x y - pF x z)
    (hA : adjGraph pE GA = GA) (hD : adjGraph pF GD = GD)
    (hx : ∀ v a, pE (X v) a = -2 * pF v (Y a))
    (hy : ∀ a v, -2 * pF (Y a) v = pE a (X v)) :
    adjGraph (weightedPair pE pF)
      (perturb (diagonalGraph GA GD) (fun x : E × F => (X x.2,Y x.1))) =
      perturb (diagonalGraph GA GD) (fun x : E × F => (X x.2,Y x.1)) := by
  let k : E × F → E × F := fun x => (X x.2,Y x.1)
  change adjGraph (weightedPair pE pF) (perturb (diagonalGraph GA GD) k) =
    perturb (diagonalGraph GA GD) k
  have hadd : ∀ x y z : E × F, weightedPair pE pF (x+y) z =
      weightedPair pE pF x z + weightedPair pE pF y z := by
    intro x y z
    change pE (x.1+y.1) z.1 - 2*pF (x.2+y.2) z.2 = _
    rw [he,hf]
    unfold weightedPair
    ring
  have hsub : ∀ x y z : E × F, weightedPair pE pF x (y-z) =
      weightedPair pE pF x y - weightedPair pE pF x z := by
    intro x y z
    change pE x.1 (y.1-z.1) - 2*pF x.2 (y.2-z.2) = _
    rw [hes,hfs]
    unfold weightedPair
    ring
  have hk : ∀ x y, weightedPair pE pF (k x) y = weightedPair pE pF x (k y) := by
    intro x y
    change pE (X x.2) y.1 - 2*pF (Y x.1) y.2 =
      pE x.1 (X y.2) - 2*pF x.2 (Y y.1)
    rw [hx]
    linear_combination hy x.1 y.2
  rw [adjGraph_perturb _ _ k k hadd hsub hk,
    adjGraph_weighted_diagonal pE pF GA GD hE0 hF0 hGA0 hGD0, hA,hD]

-- Corollary 9.14: convert the root inequality to the actual four
-- continuous-linear-map norm condition. The shifted diagonal bounds
-- and the factor-of-two coupling bound are explicit hypotheses.
theorem disk_small_coupling {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F)
    (a d t : ℝ) (ht : t < M16Krein.gapRadius a d ‖y‖)
    (hra : ‖ra‖ ≤ 1/(a-t)) (hrd : ‖rd‖ ≤ 1/(d-t))
    (hx : ‖x‖ ≤ 2*‖y‖) :
    ‖ra‖*‖x‖*‖rd‖*‖y‖ < 1 := by
  have ha : 0 < a-t := sub_pos.mpr (lt_of_lt_of_le ht (M16Krein.gap_radius_le_a a d ‖y‖))
  have hd : 0 < d-t := sub_pos.mpr (lt_of_lt_of_le ht (M16Krein.gap_radius_le_d a d ‖y‖))
  have hg := M16Krein.gap_polynomial_positive a d ‖y‖ t ht
  have hq := (M16KreinOperator.schur_bound (a-t) (d-t) ‖y‖ ha hd (norm_nonneg _) hg).1
  calc
    _ ≤ (1/(a-t))*(2*‖y‖)*(1/(d-t))*‖y‖ := by
      gcongr
    _ = 2*‖y‖^2/((a-t)*(d-t)) := by
      field_simp [ne_of_gt ha, ne_of_gt hd] <;> ring
    _ < 1 := hq

-- The equations on the full unbounded graph are equivalent to the
-- two bounded-resolvent fixed point equations.
theorem block_graph_shift_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (GA : Set (E × E)) (GD : Set (F × F)) (z : ℂ)
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F)
    (hA : GraphResolvent GA z ra) (hD : GraphResolvent GD z rd)
    (w f : E × F) :
    (w,f+z • w) ∈ perturb (diagonalGraph GA GD) (fun u : E × F => (x u.2,y u.1)) ↔
      (w.1 = ra (f.1-x w.2) ∧ w.2 = rd (f.2-y w.1)) := by
  change ((w.1, f.1+z • w.1-x w.2) ∈ GA ∧
    (w.2, f.2+z • w.2-y w.1) ∈ GD) ↔ _
  rw [show f.1+z • w.1-x w.2 = (f.1-x w.2)+z • w.1 by abel,
      show f.2+z • w.2-y w.1 = (f.2-y w.1)+z • w.2 by abel,
      hA w.1 (f.1-x w.2), hD w.2 (f.2-y w.1)]

-- Bounded full graph inverse for every point in the disk, not merely
-- algebraic elimination. Geometric diagonal bounds remain inputs.
theorem disk_graph_resolvent {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (GA : Set (E × E)) (GD : Set (F × F)) (z : ℂ)
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F)
    (a d : ℝ) (ht : ‖z‖ < M16Krein.gapRadius a d ‖y‖)
    (hra : ‖ra‖ ≤ 1/(a-‖z‖)) (hrd : ‖rd‖ ≤ 1/(d-‖z‖))
    (hx : ‖x‖ ≤ 2*‖y‖)
    (hA : GraphResolvent GA z ra) (hD : GraphResolvent GD z rd) :
    ∃ R : E × F →L[ℂ] E × F,
      GraphResolvent (perturb (diagonalGraph GA GD) (fun u : E × F => (x u.2,y u.1))) z R := by
  have hk := disk_small_coupling ra rd x y a d ‖z‖ ht hra hrd hx
  obtain ⟨R,hR⟩ := M16KreinOperator.block_resolvent_small_coupling ra rd x y hk
  refine ⟨R, ?_⟩
  intro w f
  rw [block_graph_shift_iff GA GD z ra rd x y hA hD w f]
  obtain ⟨h1,h2,hu⟩ := hR f.1 f.2
  have hf : (f.1,f.2) = f := Prod.eta f
  rw [hf] at h1 h2 hu
  constructor
  · exact hu w
  · intro hw
    rw [hw]
    exact ⟨h1,h2⟩

-- The actual Schur graph correction is symmetric at real resolvent
-- points when the diagonal graph and its resolvent are self-adjoint.
theorem schur_selfAdjoint_graph {E F : Type*}
    [AddCommGroup E]
    (pE : E → E → ℂ) (pF : F → F → ℂ)
    (GA : Set (E × E)) (x : F → E) (y : E → F) (rd : F → F)
    (hA : adjGraph pE GA = GA)
    (he : ∀ a b c, pE (a+b) c = pE a c + pE b c)
    (hs : ∀ a b c, pE a (b-c) = pE a b - pE a c)
    (hnl : ∀ a b, pE (-a) b = -pE a b)
    (hnr : ∀ a b, pE a (-b) = -pE a b)
    (hx : ∀ v a, pE (x v) a = -2*pF v (y a))
    (hy : ∀ a v, pE a (x v) = -2*pF (y a) v)
    (hr : ∀ a b, pF (rd a) b = pF a (rd b)) :
    adjGraph pE (perturb GA (fun u => -x (rd (y u)))) =
      perturb GA (fun u => -x (rd (y u))) := by
  let k : E → E := fun u => -x (rd (y u))
  have hk : ∀ u v, pE (k u) v = pE u (k v) := by
    intro u v
    change pE (-x (rd (y u))) v = pE u (-x (rd (y v)))
    rw [hnl, hnr, hx, hy, hr]
  change adjGraph pE (perturb GA k) = perturb GA k
  rw [adjGraph_perturb pE GA k k he hs hk, hA]

-- Equation (173): bounded inverse of the effective Schur graph,
-- with the printed norm bound. Here a,d are the shifted positive gaps.
theorem schur_graph_inverse_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (GA : Set (E × E)) (z : ℂ)
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F)
    (a d : ℝ) (ha : 0<a) (hd : 0<d)
    (hg : 2*‖y‖^2<a*d)
    (hra : ‖ra‖ ≤ 1/a) (hrd : ‖rd‖ ≤ 1/d)
    (hx : ‖x‖ ≤ 2*‖y‖) (hA : GraphResolvent GA z ra) :
    ∃ rs : E →L[ℂ] E,
      GraphResolvent (perturb GA (fun u => -x (rd (y u)))) z rs ∧
      ‖rs‖ ≤ d/(a*d-2*‖y‖^2) := by
  let k := ((ra.comp x).comp rd).comp y
  let q : ℝ := 2*‖y‖^2/(a*d)
  have hq : q < 1 :=
    (M16KreinOperator.schur_bound a d ‖y‖ ha hd (norm_nonneg _) hg).1
  have hkn : ‖k‖ ≤ q := by
    calc
      _ ≤ ‖(ra.comp x).comp rd‖*‖y‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖ra.comp x‖*‖rd‖)*‖y‖ := by
        gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖ra‖*‖x‖)*‖rd‖*‖y‖ := by
        gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1/a)*(2*‖y‖)*(1/d)*‖y‖ := by gcongr
      _ = q := by
        dsimp [q]
        field_simp [ne_of_gt ha, ne_of_gt hd] <;> ring
  have hk : ‖k‖ < 1 := lt_of_le_of_lt hkn hq
  obtain ⟨v,h1,h2,hn⟩ := M16KreinOperator.neumann_inverse k hk
  have hleft : ∀ u, v (u-ra (x (rd (y u)))) = u := by
    intro u
    have hh := congrArg (fun w : E →L[ℂ] E => w u) h2
    simpa [k] using hh
  have hright : ∀ u, v u-ra (x (rd (y (v u)))) = u := by
    intro u
    have hh := congrArg (fun w : E →L[ℂ] E => w u) h1
    simpa [k] using hh
  have hvq : ‖v‖ ≤ 1/(1-q) := by
    apply le_trans hn
    apply (div_le_div_iff₀ (sub_pos.mpr hk) (sub_pos.mpr hq)).2
    nlinarith only [hkn]
  refine ⟨v.comp ra, ?_, ?_⟩
  · intro u f
    change (u,f+z • u - (-x (rd (y u)))) ∈ GA ↔ u = v (ra f)
    rw [show f+z • u-(-x (rd (y u))) = (f+x (rd (y u)))+z • u by abel,
      hA u (f+x (rd (y u))), map_add]
    constructor
    · intro hu
      have hfix : u-ra (x (rd (y u))) = ra f := by
        calc
          _ = (ra f+ra (x (rd (y u))))-ra (x (rd (y u))) :=
            congrArg (fun w : E => w-ra (x (rd (y u)))) hu
          _ = _ := add_sub_cancel_right _ _
      calc
        u = v (u-ra (x (rd (y u)))) := (hleft u).symm
        _ = _ := congrArg v hfix
    · intro hu
      rw [hu]
      calc
        _ = (v (ra f)-ra (x (rd (y (v (ra f))))))+ra (x (rd (y (v (ra f))))) := by abel
        _ = _ := by rw [hright]
  · calc
      _ ≤ ‖v‖*‖ra‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1/(1-q))*(1/a) := mul_le_mul hvq hra (norm_nonneg _) (by positivity)
      _ = (1/a)/(1-q) := by simp only [div_eq_mul_inv, one_mul]; ring
      _ = d/(a*d-2*‖y‖^2) :=
        (M16KreinOperator.schur_bound a d ‖y‖ ha hd (norm_nonneg _) hg).2

#print axioms fundamental_pairing_transport
#print axioms transport_graph_resolvent
#print axioms adjGraph_weighted_diagonal
#print axioms weighted_block_selfAdjoint_graph
#print axioms disk_small_coupling
#print axioms block_graph_shift_iff
#print axioms disk_graph_resolvent
#print axioms schur_selfAdjoint_graph
#print axioms schur_graph_inverse_bound
end M16KreinGraphGap
