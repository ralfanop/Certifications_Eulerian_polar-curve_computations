import Mathlib
import M16KreinSpatial
import M16KreinDomains
import M16KreinOperator
import Manuscript16.DiracMaxwellCoefficientModel20261124

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
 

namespace M16KreinGraphGap

open scoped BigOperators
open M16KreinDomains
open Manuscript16.V166L2SpectralInverse
open Manuscript16.DiracMaxwellCoefficientModel20261124

-- Spectral model of the coclosed Hodge modes, with both polarizations.
def HodgeIndex := Σ n : ℕ, Fin (2 * ((n+2)^2-1))

def hodgeEigen (j : HodgeIndex) : ℝ := ((j.1 : ℝ)+2)^2

theorem hodgeEigen_lower (j : HodgeIndex) : 4 ≤ hodgeEigen j := by
  unfold hodgeEigen
  nlinarith [Nat.cast_nonneg (α := ℝ) j.1]

theorem diracEigen_lower (j : DiracIndex) : (3:ℝ)/2 ≤ |diracEigen j| := by
  unfold diracEigen
  split <;> simp only [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (j.1 : ℝ)+3/2)] <;> linarith [Nat.cast_nonneg (α := ℝ) j.1]

noncomputable def hodgeRealization : L2 HodgeIndex →ₗ.[ℂ] L2 HodgeIndex :=
  multOp (fun j => (hodgeEigen j : ℂ))

noncomputable def diracRealization : L2 DiracIndex →ₗ.[ℂ] L2 DiracIndex :=
  multOp (fun j => (diracEigen j : ℂ))

theorem reference_realizations_closed :
    hodgeRealization.IsClosed ∧ diracRealization.IsClosed :=
  ⟨multOp_isClosed _,multOp_isClosed _⟩

-- A finite union of finite spectral multiplicities is finite.
theorem hodge_finite_levels (N : ℕ) : {j : HodgeIndex | j.1 < N}.Finite := by
  let f : (Σ n : Fin N, Fin (2*((n.val+2)^2-1))) → HodgeIndex :=
    fun j => ⟨j.1.val,j.2⟩
  apply (Set.finite_range f).subset
  intro j hj
  exact ⟨⟨⟨j.1,hj⟩,j.2⟩,rfl⟩

noncomputable def heatSymbol (t : ℝ) (j : HodgeIndex) : ℂ :=
  (Real.exp (-t*hodgeEigen j) : ℂ)

theorem heatSymbol_bound (t : ℝ) (ht : 0 ≤ t) (j : HodgeIndex) :
    ‖heatSymbol t j‖ ≤ 1 := by
  rw [heatSymbol, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hj := hodgeEigen_lower j
  nlinarith [mul_nonneg ht (show 0 ≤ hodgeEigen j by linarith)]

noncomputable def heat (t : ℝ) (ht : 0 ≤ t) : L2 HodgeIndex →L[ℂ] L2 HodgeIndex :=
  diagonal (heatSymbol t) 1 (by norm_num) (heatSymbol_bound t ht)

theorem heatSymbol_finite (t : ℝ) (ht : 0 < t) (δ : ℝ) (hδ : 0 < δ) :
    {j : HodgeIndex | δ < ‖heatSymbol t j‖}.Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt (|Real.log δ|/t)
  apply (hodge_finite_levels N).subset
  intro j hj
  change j.1 < N
  by_contra! hjN
  have hNt : |Real.log δ| < (N:ℝ)*t := (div_lt_iff₀ ht).mp hN
  have hjN' : (N:ℝ) ≤ (j.1:ℝ) := by exact_mod_cast hjN
  have hlev : (j.1:ℝ) ≤ hodgeEigen j := by
    unfold hodgeEigen
    nlinarith [Nat.cast_nonneg (α := ℝ) j.1]
  have hprod : (N:ℝ)*t ≤ hodgeEigen j*t :=
    mul_le_mul_of_nonneg_right (hjN'.trans hlev) ht.le
  have hlog : -t*hodgeEigen j ≤ Real.log δ := by
    have hh := neg_abs_le (Real.log δ)
    nlinarith
  have hbound : ‖heatSymbol t j‖ ≤ δ := by
    rw [heatSymbol,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_log hδ]
    exact Real.exp_le_exp.mpr hlog
  exact (not_lt_of_ge hbound) hj

theorem heat_compact (t : ℝ) (ht : 0 < t) : IsCompactOperator (heat t ht.le) :=
  diagonal_isCompactOperator _ 1 (by norm_num) (heatSymbol_bound t ht.le)
    (fun δ hδ => heatSymbol_finite t ht δ hδ)

theorem heat_semigroup (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heat (s+t) (add_nonneg hs ht) = (heat s hs).comp (heat t ht) := by
  ext x j
  simp only [heat, ContinuousLinearMap.comp_apply, diagonal_apply,heatSymbol]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

-- Actual bounded Hilbert-space maps, with the geometric multiplication
-- map M and the heat/projection operator H left as explicit inputs.
section Couplings
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def couplingY (M : E →L[ℝ] F) (H : E →L[ℝ] E) (e : ℝ) :
    E →L[ℝ] F := e • (M.comp H)

noncomputable def couplingX (M : E →L[ℝ] F) (H : E →L[ℝ] E) (e : ℝ) :
    F →L[ℝ] E := (-2*e) • (H.comp (ContinuousLinearMap.adjoint M))

theorem coupling_adjoint (M : E →L[ℝ] F) (H : E →L[ℝ] E) (e : ℝ)
    (hH : ContinuousLinearMap.adjoint H = H) :
    couplingX M H e = (-2:ℝ) • (ContinuousLinearMap.adjoint (couplingY M H e)) := by
  unfold couplingX couplingY
  rw [map_smul,ContinuousLinearMap.adjoint_comp,hH,smul_smul]

theorem couplingY_bound (M : E →L[ℝ] F) (H : E →L[ℝ] E) (e C : ℝ)
    (hC : 0 ≤ C) (h : ∀ a, ‖M (H a)‖ ≤ C*‖a‖) :
    ‖couplingY M H e‖ ≤ |e|*C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg e) hC)
  intro a
  change ‖e • M (H a)‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,mul_assoc]
  exact mul_le_mul_of_nonneg_left (h a) (abs_nonneg e)

theorem coupling_norm_factor (X : F →L[ℝ] E) (Y : E →L[ℝ] F)
    (h : X = (-2:ℝ) • (ContinuousLinearMap.adjoint Y)) :
    ‖X‖ = 2*‖Y‖ := by
  rw [h,norm_smul]
  simp

theorem coupling_compact (M : E →L[ℝ] F) (H : E →L[ℝ] E) (e : ℝ)
    (hH : IsCompactOperator (H : E → E)) :
    IsCompactOperator (couplingX M H e : F → E) ∧
    IsCompactOperator (couplingY M H e : E → F) := by
  unfold couplingX couplingY
  exact ⟨(hH.comp_clm (ContinuousLinearMap.adjoint M)).smul _,(hH.clm_comp M).smul _⟩
end Couplings

-- Explicit norm-convergent series, not just existence of an inverse.
theorem neumann_series {R : Type*} [NormedRing R] [CompleteSpace R]
    [NormOneClass R] (k : R) (hk : ‖k‖ < 1) :
    HasSum (fun n : ℕ => k^n) (∑' n : ℕ, k^n) ∧
    (1-k)*(∑' n : ℕ, k^n) = 1 ∧
    (∑' n : ℕ, k^n)*(1-k) = 1 ∧
    ‖∑' n : ℕ, k^n‖ ≤ 1/(1-‖k‖) := by
  refine ⟨(summable_geometric_of_norm_lt_one hk).hasSum,
    mul_neg_geom_series k hk,geom_series_mul_neg k hk,?_⟩
  obtain ⟨v,h1,h2,hn⟩ := M16KreinOperator.neumann_inverse k hk
  have he : (∑' n : ℕ, k^n) = v := by
    calc
      _ = (∑' n : ℕ, k^n)*((1-k)*v) := by rw [h1,mul_one]
      _ = v := by rw [← mul_assoc,geom_series_mul_neg k hk,one_mul]
  rwa [he]

-- A bounded zero-shift inverse with gap g yields (175)-(176) for any
-- bounded perturbation V. The graph includes the original domain.
theorem perturbed_diagonal_resolvent {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (G : Set (E × E)) (R : E →L[ℂ] E) (V : E →L[ℂ] E) (z : ℂ)
    (g : ℝ) (hg : 0 < g) (hR : ‖R‖ ≤ 1/g)
    (hgap : ‖V‖+‖z‖ < g) (hG : GraphResolvent G 0 R) :
    ∃ S : E →L[ℂ] E, GraphResolvent (perturb G V) z S ∧
      ‖S‖ ≤ 1/(g-‖V‖-‖z‖) := by
  let P : E →L[ℂ] E := z • (1 : E →L[ℂ] E)-V
  let K := R.comp P
  let b := ‖V‖+‖z‖
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hP : ‖P‖ ≤ b := by
    calc
      _ ≤ ‖z • (1 : E →L[ℂ] E)‖+‖V‖ := norm_sub_le _ _
      _ = b := by simp [b,norm_smul,add_comm]
  have hK : ‖K‖ ≤ b/g := by
    calc
      _ ≤ ‖R‖*‖P‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1/g)*b := mul_le_mul hR hP (norm_nonneg _) (by positivity)
      _ = b/g := by ring
  have hq : b/g < 1 := (div_lt_one hg).2 hgap
  have hk : ‖K‖ < 1 := hK.trans_lt hq
  let W : E →L[ℂ] E := ∑' n : ℕ, K^n
  obtain ⟨_,h1,h2,hn⟩ := neumann_series K hk
  change (1-K)*W = 1 at h1
  change W*(1-K) = 1 at h2
  change ‖W‖ ≤ 1/(1-‖K‖) at hn
  have hleft (u : E) : W (u-K u) = u := by
    have hh := congrArg (fun T : E →L[ℂ] E => T u) h2
    simpa using hh
  have hright (u : E) : W u-K (W u) = u := by
    have hh := congrArg (fun T : E →L[ℂ] E => T u) h1
    simpa using hh
  refine ⟨W.comp R,?_,?_⟩
  · intro x f
    change (x,f+z • x-V x) ∈ G ↔ x = W (R f)
    have hh : f+z • x-V x = (f+P x)+ (0:ℂ) • x := by
      simp [P,sub_eq_add_neg,add_assoc]
    rw [hh,hG x (f+P x),map_add]
    change (x = R f+K x) ↔ _
    constructor
    · intro hx
      have he : x-K x = R f := by rw [hx,add_sub_cancel_right]
      rw [← he,hleft]
    · intro hx
      rw [hx]
      have he := hright (R f)
      exact eq_add_of_sub_eq he
  · have hW : ‖W‖ ≤ 1/(1-b/g) := by
      apply le_trans hn
      exact (div_le_div_iff₀ (sub_pos.mpr hk) (sub_pos.mpr hq)).2 (by nlinarith)
    calc
      _ ≤ ‖W‖*‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1/(1-b/g))*(1/g) := mul_le_mul hW hR (norm_nonneg _) (by positivity)
      _ = 1/(g-b) := by
        have hgb : g-b ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
        have hd : 1-b/g ≠ 0 := ne_of_gt (sub_pos.mpr hq)
        field_simp [ne_of_gt hg,hgb,hd] <;> ring
      _ = _ := by congr 1 <;> dsimp [b] <;> ring

-- Zero resolvent in the maximal coefficient domain.
theorem reference_zero_graph {ι : Type*} (lam : ι → ℝ) (g : ℝ)
    (hg : 0 < g) (hl : ∀ j, g ≤ |lam j|) :
    ∃ R : L2 ι →L[ℂ] L2 ι,
      GraphResolvent ((multOp (fun j => (lam j : ℂ))).graph : Set (L2 ι × L2 ι)) 0 R ∧
      ‖R‖ ≤ 1/g := by
  let w : ι → ℂ := fun j => (lam j : ℂ)⁻¹
  have hne (j : ι) : (lam j : ℂ) ≠ 0 := by
    intro h
    have hh : lam j = 0 := by exact_mod_cast h
    have hj := hl j
    rw [hh,abs_zero] at hj
    linarith
  have hw (j : ι) : ‖w j‖ ≤ 1/g := by
    rw [w,norm_inv,Complex.norm_real,Real.norm_eq_abs,← one_div]
    exact one_div_le_one_div_of_le hg (hl j)
  let R := diagonal w (1/g) (by positivity) hw
  refine ⟨R,?_,diagonal_norm_le _ _ _ _⟩
  intro x f
  simp only [zero_smul,add_zero]
  rw [SetLike.mem_coe,mem_graph_multOp_iff]
  constructor
  · intro h
    apply lp.ext
    funext j
    rw [diagonal_apply,h j]
    dsimp [w]
    rw [← mul_assoc,inv_mul_cancel₀ (hne j),one_mul]
  · intro h j
    rw [h,diagonal_apply]
    dsimp [w]
    rw [← mul_assoc,mul_inv_cancel₀ (hne j),one_mul]

-- Specialize the two diagonal estimates to the printed constants.
theorem hodge_shift_bound (V : L2 HodgeIndex →L[ℂ] L2 HodgeIndex) (z : ℂ)
    (h : ‖V‖+‖z‖ < 4) :
    ∃ R : L2 HodgeIndex →L[ℂ] L2 HodgeIndex,
      GraphResolvent (perturb (hodgeRealization.graph : Set _) V) z R ∧
      ‖R‖ ≤ 1/(4-‖V‖-‖z‖) := by
  obtain ⟨R,hR,hn⟩ := reference_zero_graph hodgeEigen 4 (by norm_num)
    (fun j => le_trans (hodgeEigen_lower j) (le_abs_self _))
  exact perturbed_diagonal_resolvent _ R V z 4 (by norm_num) hn h hR

theorem dirac_shift_bound (V : L2 DiracIndex →L[ℂ] L2 DiracIndex) (z : ℂ)
    (h : ‖V‖+‖z‖ < 3/2) :
    ∃ R : L2 DiracIndex →L[ℂ] L2 DiracIndex,
      GraphResolvent (perturb (diracRealization.graph : Set _) V) z R ∧
      ‖R‖ ≤ 1/(3/2-‖V‖-‖z‖) := by
  obtain ⟨R,hR,hn⟩ := reference_zero_graph diracEigen (3/2) (by norm_num) diracEigen_lower
  exact perturbed_diagonal_resolvent _ R V z (3/2) (by norm_num) hn h hR

-- Equation (174) implies the gap condition (170) once the
-- background multiplication estimate (147) is available.
theorem background_gap (c e H p a d : ℝ)
    (hc : 0 ≤ c) (hH : 0 ≤ H) (hp : 0 ≤ p)
    (hb : c ≤ |e|*H*p)
    (hg : 2*|e|^2*H^2*p^2 < a*d) : 2*c^2 < a*d := by
  have hh : 0 ≤ |e|*H*p := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ |e|*H*p+c by positivity)]

theorem schur_series_converges {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F)
    (a d t : ℝ) (ht : t < M16Krein.gapRadius a d ‖y‖)
    (hra : ‖ra‖ ≤ 1/(a-t)) (hrd : ‖rd‖ ≤ 1/(d-t))
    (hx : ‖x‖ ≤ 2*‖y‖) :
    let k := ((ra.comp x).comp rd).comp y
    HasSum (fun n : ℕ => k^n) (∑' n : ℕ, k^n) ∧
      (1-k)*(∑' n : ℕ, k^n) = 1 ∧
      (∑' n : ℕ, k^n)*(1-k) = 1 := by
  dsimp only
  let k := ((ra.comp x).comp rd).comp y
  have h := disk_small_coupling ra rd x y a d t ht hra hrd hx
  have hk : ‖k‖ < 1 := by
    apply lt_of_le_of_lt _ h
    dsimp [k]
    calc
      _ ≤ ‖(ra.comp x).comp rd‖*‖y‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖ra.comp x‖*‖rd‖)*‖y‖ := by
        gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖ra‖*‖x‖)*‖rd‖*‖y‖ := by
        gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
  obtain ⟨hs,h1,h2,_⟩ := neumann_series k hk
  exact ⟨hs,h1,h2⟩

#print axioms hodge_shift_bound
#print axioms dirac_shift_bound
#print axioms background_gap
#print axioms schur_series_converges
#print axioms hodgeEigen_lower
#print axioms diracEigen_lower
#print axioms reference_realizations_closed
#print axioms hodge_finite_levels
#print axioms heatSymbol_bound
#print axioms heatSymbol_finite
#print axioms heat_compact
#print axioms heat_semigroup
#print axioms coupling_adjoint
#print axioms couplingY_bound
#print axioms coupling_norm_factor
#print axioms coupling_compact
#print axioms neumann_series
#print axioms perturbed_diagonal_resolvent
#print axioms reference_zero_graph
end M16KreinGraphGap
