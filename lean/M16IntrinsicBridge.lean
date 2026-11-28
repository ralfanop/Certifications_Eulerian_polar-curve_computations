import M16S3Frame
import M16ComplexHilbert

noncomputable section
open M16S3Geometry M16S3Frame M16KreinDomains M16KreinGraphGap
open M16KreinGeometricRealization M16ComplexHilbert
open scoped InnerProductSpace

namespace M16IntrinsicBridge

-- The curve is on S³, not merely a first-order tangent vector.
def unitArc (a b c : ℝ) (t : ℝ) : Q :=
  (Real.cos t,a*Real.sin t,b*Real.sin t,c*Real.sin t)

theorem unitArc_on_sphere (a b c : ℝ) (h : a^2+b^2+c^2=1) (t : ℝ) :
    qSq (unitArc a b c t) = 1 := by
  simp only [qSq,unitArc]
  calc
    _ = Real.cos t ^ 2+(a^2+b^2+c^2)*Real.sin t^2 := by ring
    _ = 1 := by rw [h,one_mul,add_comm,Real.sin_sq_add_cos_sq]

theorem unitArc_deriv (a b c : ℝ) :
    HasDerivAt (unitArc a b c) (0,a,b,c) 0 := by
  have hcos : HasDerivAt Real.cos 0 0 := by simpa using Real.hasDerivAt_cos 0
  have hsin : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
  have ha : HasDerivAt (fun t => a*Real.sin t) a 0 := by
    simpa using hsin.const_mul a
  have hb : HasDerivAt (fun t => b*Real.sin t) b 0 := by
    simpa using hsin.const_mul b
  have hc : HasDerivAt (fun t => c*Real.sin t) c 0 := by
    simpa using hsin.const_mul c
  exact hcos.prodMk (ha.prodMk (hb.prodMk hc))

def sphereArc (x : Q) (a b c : ℝ) (t : ℝ) : Q :=
  qMul x (unitArc a b c t)

theorem sphereArc_on_sphere (x : S3) (a b c : ℝ) (h : a^2+b^2+c^2=1) (t : ℝ) :
    qSq (sphereArc x.val a b c t) = 1 := by
  unfold sphereArc
  rw [qSq_mul,x.property,unitArc_on_sphere a b c h,one_mul]

theorem sphereArc_zero (x : Q) (a b c : ℝ) :
    sphereArc x a b c 0 = x := by
  have h : unitArc a b c 0 = qOne := by simp [unitArc,qOne]
  rw [sphereArc,h,qMul_one]

theorem sphereArc_deriv (x : Q) (a b c : ℝ) :
    HasDerivAt (sphereArc x a b c) (qMul x (0,a,b,c)) 0 := by
  have h := (leftMap x).hasFDerivAt.comp_hasDerivAt 0 (unitArc_deriv a b c)
  exact h

-- Intrinsic first derivative: two differentiable extensions agreeing on
-- S³ have equal derivative along every unit imaginary quaternion direction.
theorem frameDeriv_restriction (x : S3) (a b c : ℝ)
    (hu : a^2+b^2+c^2=1) (f g : Q → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : ∀ y : S3, f y.val = g y.val) :
    frameDeriv (0,a,b,c) f x.val = frameDeriv (0,a,b,c) g x.val := by
  let p := sphereArc x.val a b c
  have h0 : p 0 = x.val := sphereArc_zero _ _ _ _
  have hp : HasDerivAt p (qMul x.val (0,a,b,c)) 0 := sphereArc_deriv _ _ _ _
  have h1 := (hf (p 0)).hasFDerivAt.comp_hasDerivAt 0 hp
  have h2 := (hg (p 0)).hasFDerivAt.comp_hasDerivAt 0 hp
  have he : (fun t => f (p t)) = (fun t => g (p t)) := by
    funext t
    exact hfg ⟨p t,sphereArc_on_sphere x a b c hu t⟩
  have hh := h1.deriv
  have hh' := h2.deriv
  change deriv (fun t => f (p t)) 0 = _ at hh
  change deriv (fun t => g (p t)) 0 = _ at hh'
  rw [he,hh'] at hh
  simpa [frameDeriv,h0] using hh.symm

theorem frameDeriv_restriction_three (x : S3) (f g : Q → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : ∀ y : S3, f y.val = g y.val) :
    frameDeriv qi f x.val = frameDeriv qi g x.val ∧
    frameDeriv qj f x.val = frameDeriv qj g x.val ∧
    frameDeriv qk f x.val = frameDeriv qk g x.val := by
  exact ⟨frameDeriv_restriction x 1 0 0 (by norm_num) f g hf hg hfg,
    frameDeriv_restriction x 0 1 0 (by norm_num) f g hf hg hfg,
    frameDeriv_restriction x 0 0 1 (by norm_num) f g hf hg hfg⟩

def SameFields (v w : Fields) : Prop :=
  ∀ x : S3, v.1 x.val = w.1 x.val ∧
    v.2.1 x.val = w.2.1 x.val ∧ v.2.2 x.val = w.2.2 x.val

theorem curl_restriction (v w : Fields) (hv : Smooth1 v) (hw : Smooth1 w)
    (h : SameFields v w) : SameFields (curlFrame v) (curlFrame w) := by
  intro x
  obtain ⟨h1,h2,h3⟩ := frameDeriv_restriction_three x v.1 w.1 hv.1 hw.1 (fun y => (h y).1)
  obtain ⟨h4,h5,h6⟩ := frameDeriv_restriction_three x v.2.1 w.2.1 hv.2.1 hw.2.1 (fun y => (h y).2.1)
  obtain ⟨h7,h8,h9⟩ := frameDeriv_restriction_three x v.2.2 w.2.2 hv.2.2 hw.2.2 (fun y => (h y).2.2)
  simp only [curlFrame,h1,h2,h3,h4,h5,h6,h7,h8,h9,(h x).1,(h x).2.1,(h x).2.2]
  exact ⟨trivial,trivial,trivial⟩

theorem codiff_restriction (v w : Fields) (hv : Smooth1 v) (hw : Smooth1 w)
    (h : SameFields v w) (x : S3) :
    codiffFrame v x.val = codiffFrame w x.val := by
  obtain ⟨h1,_,_⟩ := frameDeriv_restriction_three x v.1 w.1 hv.1 hw.1 (fun y => (h y).1)
  obtain ⟨_,h2,_⟩ := frameDeriv_restriction_three x v.2.1 w.2.1 hv.2.1 hw.2.1 (fun y => (h y).2.1)
  obtain ⟨_,_,h3⟩ := frameDeriv_restriction_three x v.2.2 w.2.2 hv.2.2 hw.2.2 (fun y => (h y).2.2)
  simp only [codiffFrame,h1,h2,h3]

theorem grad_restriction (f g : Q → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (h : ∀ x : S3, f x.val = g x.val) :
    SameFields (gradFrame f) (gradFrame g) := by
  intro x
  exact frameDeriv_restriction_three x f g hf hg h

theorem hodge_restriction (v w : Fields) (hv : Smooth1 v) (hw : Smooth1 w)
    (hc : Smooth1 (curlFrame v)) (hc' : Smooth1 (curlFrame w))
    (hd : Differentiable ℝ (codiffFrame v)) (hd' : Differentiable ℝ (codiffFrame w))
    (h : SameFields v w) : SameFields (hodgeFrame v) (hodgeFrame w) := by
  have hcurl := curl_restriction (curlFrame v) (curlFrame w) hc hc'
    (curl_restriction v w hv hw h)
  have hgrad := grad_restriction (codiffFrame v) (codiffFrame w) hd hd'
    (codiff_restriction v w hv hw h)
  intro x
  exact ⟨congrArg₂ (· + ·) (hcurl x).1 (hgrad x).1,
    congrArg₂ (· + ·) (hcurl x).2.1 (hgrad x).2.1,
    congrArg₂ (· + ·) (hcurl x).2.2 (hgrad x).2.2⟩

-- Compact symmetric inverse spectral theorem: completeness is derived
-- from compactness, not from an assumed complete geometric eigenfamily.
theorem compact_inverse_total {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (R : E →L[ℂ] E) (hc : IsCompactOperator (R : E → E))
    (hs : R.toLinearMap.IsSymmetric) :
    (⨆ μ : ℂ, Module.End.eigenspace R.toLinearMap μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs

theorem inverse_eigenvector_graph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (G : Submodule ℂ (E × E))
    (R : E →L[ℂ] E) (hR : GraphResolvent (G : Set _) 0 R)
    (v : E) (μ : ℂ) (hμ : μ ≠ 0) (hv : R v = μ • v) :
    (v,μ⁻¹ • v) ∈ G := by
  have h : (R v,v) ∈ G := by
    have hh := (hR (R v) v).2 rfl
    simpa using hh
  rw [hv] at h
  have hh := G.smul_mem μ⁻¹ h
  change (μ⁻¹ • (μ • v),μ⁻¹ • v) ∈ G at hh
  simpa only [smul_smul,inv_mul_cancel₀ hμ,one_smul] using hh

theorem inverse_no_zero_eigenvector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (G : Set (E × E))
    (hG : ∀ y, (0,y) ∈ G → y = 0)
    (R : E →L[ℂ] E) (hR : GraphResolvent G 0 R)
    (v : E) (hv : R v = 0) : v = 0 := by
  apply hG
  have h := (hR 0 v).2 hv.symm
  simpa using h

-- The imported Hilbert complexification carries the genuine ℓ² norm.
-- Reuse the previously certified componentwise graph adjoint theorem,
-- now on that complex Hilbert type.
open M16ComplexHilbert.Complexification

def hilbertGraph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Set (E × E)) : Set (Complexification E × Complexification E) :=
  {w | (w.1.1,w.2.1) ∈ G ∧ (w.1.2,w.2.2) ∈ G}

theorem hilbertGraph_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Set (E × E)) (h0 : (0,0) ∈ G) :
    adjGraph (inner ℂ) (hilbertGraph G) = hilbertGraph (adjGraph (inner ℝ) G) := by
  exact pairGraph_adjoint G (inner ℝ) h0 (fun x => inner_zero_left x)

theorem hilbertGraph_selfAdjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Set (E × E)) (h0 : (0,0) ∈ G) (hs : adjGraph (inner ℝ) G = G) :
    adjGraph (inner ℂ) (hilbertGraph G) = hilbertGraph G := by
  rw [hilbertGraph_adjoint G h0,hs]

theorem hilbertGraph_closed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Set (E × E)) (hG : IsClosed G) : IsClosed (hilbertGraph G) := by
  have c1 : Continuous (fun u : Complexification E => u.1) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun u v : Complexification E => by
      simp only [dist_eq_norm,NNReal.coe_one,one_mul]
      exact norm_fst_le (u-v))).continuous
  have c2 : Continuous (fun u : Complexification E => u.2) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun u v : Complexification E => by
      simp only [dist_eq_norm,NNReal.coe_one,one_mul]
      exact norm_snd_le (u-v))).continuous
  change IsClosed
    ((fun w : Complexification E × Complexification E => (w.1.1,w.2.1)) ⁻¹' G ∩
     (fun w : Complexification E × Complexification E => (w.1.2,w.2.2)) ⁻¹' G)
  exact (hG.preimage ((c1.comp continuous_fst).prodMk (c1.comp continuous_snd))).inter
    (hG.preimage ((c2.comp continuous_fst).prodMk (c2.comp continuous_snd)))

#print axioms unitArc_on_sphere
#print axioms unitArc_deriv
#print axioms sphereArc_on_sphere
#print axioms sphereArc_zero
#print axioms sphereArc_deriv
#print axioms frameDeriv_restriction
#print axioms frameDeriv_restriction_three
#print axioms curl_restriction
#print axioms codiff_restriction
#print axioms grad_restriction
#print axioms hodge_restriction
#print axioms compact_inverse_total
#print axioms inverse_eigenvector_graph
#print axioms inverse_no_zero_eigenvector
#print axioms hilbertGraph_adjoint
#print axioms hilbertGraph_selfAdjoint
#print axioms hilbertGraph_closed
end M16IntrinsicBridge
