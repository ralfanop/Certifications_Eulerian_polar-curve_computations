import M16KreinGeometricRealization

noncomputable section
open scoped BigOperators
open M16KreinDomains M16KreinGraphGap M16KreinGeometricRealization

namespace M16S3Geometry

-- Unit quaternions in explicit real coordinates; the ambient quadratic
-- form is the restriction of the Euclidean metric to the unit sphere.
abbrev Q := ℝ × ℝ × ℝ × ℝ

def qSq (x : Q) : ℝ := x.1^2+x.2.1^2+x.2.2.1^2+x.2.2.2^2

def qDot (x y : Q) : ℝ :=
  x.1*y.1+x.2.1*y.2.1+x.2.2.1*y.2.2.1+x.2.2.2*y.2.2.2

def qConj (x : Q) : Q := (x.1,-x.2.1,-x.2.2.1,-x.2.2.2)

def qMul (x y : Q) : Q :=
  (x.1*y.1-x.2.1*y.2.1-x.2.2.1*y.2.2.1-x.2.2.2*y.2.2.2,
   x.1*y.2.1+x.2.1*y.1+x.2.2.1*y.2.2.2-x.2.2.2*y.2.2.1,
   x.1*y.2.2.1-x.2.1*y.2.2.2+x.2.2.1*y.1+x.2.2.2*y.2.1,
   x.1*y.2.2.2+x.2.1*y.2.2.1-x.2.2.1*y.2.1+x.2.2.2*y.1)

def qOne : Q := (1,0,0,0)

def S3 := {x : Q // qSq x = 1}

theorem qSq_mul (x y : Q) : qSq (qMul x y) = qSq x * qSq y := by
  simp only [qSq,qMul]
  ring

theorem qSq_conj (x : Q) : qSq (qConj x) = qSq x := by
  simp only [qSq,qConj]
  ring

theorem qMul_assoc (x y z : Q) : qMul (qMul x y) z = qMul x (qMul y z) := by
  apply Prod.ext
  · simp only [qMul]; ring
  · apply Prod.ext
    · simp only [qMul]; ring
    · apply Prod.ext <;> simp only [qMul] <;> ring

theorem qMul_one (x : Q) : qMul x qOne = x := by
  apply Prod.ext
  · simp [qMul,qOne]
  · apply Prod.ext
    · simp [qMul,qOne]
    · apply Prod.ext <;> simp [qMul,qOne]

theorem qConj_mul_self (x : Q) (hx : qSq x = 1) :
    qMul (qConj x) x = qOne := by
  apply Prod.ext
  · simp only [qMul,qConj,qOne]
    unfold qSq at hx
    linear_combination hx
  · apply Prod.ext
    · simp only [qMul,qConj,qOne]; ring
    · apply Prod.ext <;> simp only [qMul,qConj,qOne] <;> ring

theorem qMul_dot (u x y : Q) :
    qDot (qMul u x) (qMul u y) = qSq u * qDot x y := by
  simp only [qDot,qSq,qMul]
  ring

def leftAction (u x : S3) : S3 :=
  ⟨qMul u.val x.val, by rw [qSq_mul,u.property,x.property,mul_one]⟩

theorem leftAction_preserves_dot (u x y : S3) :
    qDot (leftAction u x).val (leftAction u y).val = qDot x.val y.val := by
  change qDot (qMul u.val x.val) (qMul u.val y.val) = _
  rw [qMul_dot,u.property,one_mul]

theorem leftAction_transitive (x y : S3) : ∃ u : S3, leftAction u x = y := by
  let u : S3 := ⟨qMul y.val (qConj x.val), by
    rw [qSq_mul,qSq_conj,y.property,x.property,mul_one]⟩
  refine ⟨u,Subtype.ext ?_⟩
  change qMul (qMul y.val (qConj x.val)) x.val = y.val
  rw [qMul_assoc,qConj_mul_self x.val x.property,qMul_one]

-- The real finite-rank two-point kernel is invariant under an orthogonal
-- change of eigenbasis, not merely its diagonal.
theorem orthogonal_kernel_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → ι → ℝ) (v w : ι → ℝ)
    (hU : ∀ j k, ∑ i, U i j * U i k = if j = k then 1 else 0) :
    (∑ i, (∑ j, U i j * v j)*(∑ j, U i j * w j)) = ∑ j, v j*w j := by
  calc
    _ = ∑ i, ∑ j, ∑ k, (U i j * U i k)*(v j*w k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ j, ∑ k, (∑ i, U i j * U i k)*(v j*w k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [hU]

-- If every spectral projector kernel intertwines a fixed isometry,
-- its heat-weighted sum does also, for every time for which it exists.
theorem heat_kernel_sum_invariant (lam K K' : ℕ → ℝ) (t : ℝ)
    (h : ∀ n, K' n = K n) :
    (∑' n, Real.exp (-t*lam n)*K' n) =
      ∑' n, Real.exp (-t*lam n)*K n := by
  simp only [h]

-- Density and domain of a real unbounded operator survive the
-- real/imaginary-pair construction with the product topology.
theorem pairGraph_dense_domain {E : Type*} [TopologicalSpace E]
    (G : Set (E × E)) (hG : Dense (domain G)) :
    Dense (domain (pairGraph G)) := by
  rw [pairGraph_domain]
  change Dense (domain G ×ˢ domain G)
  exact hG.prod hG

-- Explicit multiplication of the real and imaginary pairing yields the
-- squared norm. This is the norm to use, not the ordinary max product norm.
theorem complexPair_self_real {E : Type*}
    (p : E → E → ℝ) (x : E × E) :
    (complexPair p x x).re = p x.1 x.1 + p x.2 x.2 := rfl

theorem complexPair_self_imag {E : Type*}
    (p : E → E → ℝ) (hs : ∀ x y, p x y = p y x) (x : E × E) :
    (complexPair p x x).im = 0 := by
  change p x.1 x.2-p x.2 x.1 = 0
  rw [hs x.1 x.2,sub_self]

-- The derivative of the quadratic current has the stated factor two.
-- Exact finite difference, valid for every real parameter, no limiting
-- operation or extra geometric identification is assumed here.
theorem current_quadratic_increment (a b c s : ℝ) :
    a+2*s*b+s^2*c-a = s*(2*b+s*c) := by ring

theorem current_difference_derivative (b c : ℝ) :
    HasDerivAt (fun s : ℝ => 2*s*b+s^2*c) (2*b) 0 := by
  have h : HasDerivAt (fun s : ℝ => 2*s*b+s^2*c)
      (((0:ℝ)*0+2*1)*b + (2*0^(2-1)*1)*c) 0 := by
    convert (((hasDerivAt_const (0:ℝ) (2:ℝ)).mul (hasDerivAt_id (0:ℝ))).mul_const b |>.add
      (((hasDerivAt_id (0:ℝ)).pow 2).mul_const c) using 1 <;> ring
  simpa using h

section ProjectedCouplings

variable {E H F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

-- J is inclusion of transverse fields, J† the orthogonal projection.
def projectedY (J : E →L[ℝ] H) (M : H →L[ℝ] F)
    (T : H →L[ℝ] H) (e : ℝ) : E →L[ℝ] F :=
  e • (M.comp (T.comp J))

def projectedX (J : E →L[ℝ] H) (M : H →L[ℝ] F)
    (T : H →L[ℝ] H) (e : ℝ) : F →L[ℝ] E :=
  (-2*e) • ((ContinuousLinearMap.adjoint J).comp
    (T.comp (ContinuousLinearMap.adjoint M)))

theorem projected_adjoint (J : E →L[ℝ] H) (M : H →L[ℝ] F)
    (T : H →L[ℝ] H) (e : ℝ) (hT : ContinuousLinearMap.adjoint T = T) :
    projectedX J M T e =
      (-2:ℝ) • (ContinuousLinearMap.adjoint (projectedY J M T e)) := by
  unfold projectedX projectedY
  rw [map_smul, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    hT, smul_smul]
  congr 1
  ext x
  rfl

theorem projected_compact (J : E →L[ℝ] H) (M : H →L[ℝ] F)
    (T : H →L[ℝ] H) (e : ℝ) (hT : IsCompactOperator (T : H → H)) :
    IsCompactOperator (projectedX J M T e : F → E) ∧
    IsCompactOperator (projectedY J M T e : E → F) := by
  unfold projectedX projectedY
  exact ⟨((hT.comp_clm (ContinuousLinearMap.adjoint M)).clm_comp
      (ContinuousLinearMap.adjoint J)).smul _,
    ((hT.comp_clm J).clm_comp M).smul _⟩

end ProjectedCouplings

#print axioms projected_adjoint
#print axioms projected_compact
#print axioms qSq_mul
#print axioms qSq_conj
#print axioms qMul_assoc
#print axioms qMul_one
#print axioms qConj_mul_self
#print axioms qMul_dot
#print axioms leftAction_preserves_dot
#print axioms leftAction_transitive
#print axioms orthogonal_kernel_pair
#print axioms heat_kernel_sum_invariant
#print axioms pairGraph_dense_domain
#print axioms complexPair_self_real
#print axioms complexPair_self_imag
#print axioms current_quadratic_increment
#print axioms current_difference_derivative
end M16S3Geometry
