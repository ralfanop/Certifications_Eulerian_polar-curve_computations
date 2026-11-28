import Manuscript15.ProjectiveQuarticCharts20261127

/-! M15 section 12: projective descent on complex points and the two
affine branch polynomials. The quotient is by nonzero homogeneous
scalars; this is a construction on complex points, not a scheme morphism.
The simple-root criterion is a prerequisite to a genus computation,
not a formal proof of Riemann-Hurwitz or of the genus. -/

noncomputable section
namespace Manuscript15.ProjectiveQuarticDescent20261128
open Manuscript15.ProjectiveQuarticCharts20261127

structure ConePoint (p q : ℂ) where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  conic : b^2 = a*c
  cover : d^2 = a^2+p*a*c+q*c^2
  nonzero : ¬ (a=0 ∧ b=0 ∧ c=0 ∧ d=0)

def ConeRel {p q : ℂ} (x y : ConePoint p q) : Prop :=
  ∃ s : ℂ, s ≠ 0 ∧ y.a=s*x.a ∧ y.b=s*x.b ∧ y.c=s*x.c ∧ y.d=s*x.d

theorem coneRel_equivalence (p q : ℂ) : Equivalence (@ConeRel p q) := by
  constructor
  · intro x
    exact ⟨1, one_ne_zero, by simp, by simp, by simp, by simp⟩
  · intro x y h
    rcases h with ⟨s,hs,ha,hb,hc,hd⟩
    refine ⟨s⁻¹,inv_ne_zero hs,?_,?_,?_,?_⟩
    · rw [ha,← mul_assoc,inv_mul_cancel₀ hs,one_mul]
    · rw [hb,← mul_assoc,inv_mul_cancel₀ hs,one_mul]
    · rw [hc,← mul_assoc,inv_mul_cancel₀ hs,one_mul]
    · rw [hd,← mul_assoc,inv_mul_cancel₀ hs,one_mul]
  · intro x y z hxy hyz
    rcases hxy with ⟨s,hs,ha,hb,hc,hd⟩
    rcases hyz with ⟨t,ht,ha',hb',hc',hd'⟩
    refine ⟨t*s,mul_ne_zero ht hs,?_,?_,?_,?_⟩
    · rw [ha',ha,mul_assoc]
    · rw [hb',hb,mul_assoc]
    · rw [hc',hc,mul_assoc]
    · rw [hd',hd,mul_assoc]

def coneSetoid (p q : ℂ) : Setoid (ConePoint p q) :=
  ⟨ConeRel,coneRel_equivalence p q⟩

def ProjectiveCone (p q : ℂ) := Quotient (coneSetoid p q)

def projectiveClass {p q : ℂ} (x : ConePoint p q) : ProjectiveCone p q :=
  Quotient.mk (coneSetoid p q) x

def mapCone (x : ConePoint 0 1) : ConePoint 3 2 := by
  have hd : x.d^2=x.a^2+x.c^2 := by simpa using x.cover
  have h := homogeneous_map_equations x.a x.b x.c x.d x.conic hd
  refine ⟨(x.a-x.c)^2,(↑(Real.sqrt (2:ℝ)) : ℂ)*x.b*(x.a-x.c),
    2*x.b^2,(x.a+x.c)*x.d,?_,h.2,?_⟩
  · calc
      _ = (↑(Real.sqrt (2:ℝ)) : ℂ)^2*x.b^2*(x.a-x.c)^2 := by ring
      _ = _ := h.1
  · exact no_homogeneous_basepoint x.a x.b x.c x.d x.conic hd x.nonzero

theorem mapCone_respects_scalars (x y : ConePoint 0 1)
    (h : ConeRel x y) : ConeRel (mapCone x) (mapCone y) := by
  rcases h with ⟨s,hs,ha,hb,hc,hd⟩
  have hh := homogeneous_scaling x.a x.b x.c x.d s
  refine ⟨s^2,pow_ne_zero _ hs,?_,?_,?_,?_⟩
  · change (y.a-y.c)^2 = s^2*(x.a-x.c)^2
    rw [ha,hc]
    exact hh.1
  · change (↑(Real.sqrt (2:ℝ)) : ℂ)*y.b*(y.a-y.c) =
      s^2*((↑(Real.sqrt (2:ℝ)) : ℂ)*x.b*(x.a-x.c))
    rw [ha,hb,hc]
    exact hh.2.1
  · change 2*y.b^2 = s^2*(2*x.b^2)
    rw [hb]
    exact hh.2.2.1
  · change (y.a+y.c)*y.d = s^2*((x.a+x.c)*x.d)
    rw [ha,hc,hd]
    exact hh.2.2.2

def projectiveMap : ProjectiveCone 0 1 → ProjectiveCone 3 2 :=
  Quotient.lift (fun x => projectiveClass (mapCone x))
    (fun x y h => Quotient.sound (mapCone_respects_scalars x y h))

theorem projectiveMap_on_representative (x : ConePoint 0 1) :
    projectiveMap (projectiveClass x) = projectiveClass (mapCone x) := rfl

theorem normalized_representative_unique {p q : ℂ} (x y : ConePoint p q)
    (hx : x.c=1) (hy : y.c=1) (h : ConeRel x y) :
    x.a=y.a ∧ x.b=y.b ∧ x.c=y.c ∧ x.d=y.d := by
  rcases h with ⟨s,_,ha,hb,hc,hd⟩
  have hs : s=1 := by simpa [hx,hy] using hc.symm
  simp only [hs,one_mul] at ha hb hd
  exact ⟨ha.symm,hb.symm,hx.trans hy.symm,hd.symm⟩

theorem affine_coordinate_equations {p q : ℂ} (x : ConePoint p q)
    (hc : x.c ≠ 0) :
    (x.b/x.c)^2=x.a/x.c ∧
    (x.d/x.c)^2=(x.b/x.c)^4+p*(x.b/x.c)^2+q := by
  have hb : (x.b/x.c)^2=x.a/x.c := by
    rw [div_pow,x.conic]
    field_simp [hc]
  refine ⟨hb,?_⟩
  calc
    _ = (x.a^2+p*x.a*x.c+q*x.c^2)/x.c^2 := by rw [div_pow,x.cover]
    _ = (x.a/x.c)^2+p*(x.a/x.c)+q := by field_simp [hc] <;> ring
    _ = _ := by rw [← hb]; ring

def affinePoint (p q t w : ℂ) (h : w^2=t^4+p*t^2+q) : ConePoint p q := by
  refine ⟨t^2,t,1,w,?_,?_,?_⟩
  · ring
  · rw [h]; ring
  · simp

theorem affine_point_recovers_projective_class {p q : ℂ} (x : ConePoint p q)
    (hc : x.c ≠ 0) :
    projectiveClass x =
      projectiveClass (affinePoint p q (x.b/x.c) (x.d/x.c)
        (affine_coordinate_equations x hc).2) := by
  apply Quotient.sound
  refine ⟨x.c⁻¹,inv_ne_zero hc,?_,?_,?_,?_⟩
  · change (x.b/x.c)^2=x.c⁻¹*x.a
    rw [(affine_coordinate_equations x hc).1,div_eq_mul_inv,mul_comm]
  · change x.b/x.c=x.c⁻¹*x.b
    rw [div_eq_mul_inv,mul_comm]
  · change 1=x.c⁻¹*x.c
    exact (inv_mul_cancel₀ hc).symm
  · change x.d/x.c=x.c⁻¹*x.d
    rw [div_eq_mul_inv,mul_comm]

theorem branch_polynomial_simple (p q t : ℂ) (hq : q ≠ 0)
    (hdisc : 4*q-p^2 ≠ 0) (h : t^4+p*t^2+q=0) :
    4*t^3+2*p*t ≠ 0 := by
  intro hder
  have ht : t ≠ 0 := by
    intro ht
    exact hq (by simpa [ht] using h)
  have hfactor : (2*t)*(2*t^2+p)=0 := by linear_combination hder
  have he : 2*t^2+p=0 :=
    (mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero (by norm_num) ht)
  apply hdisc
  linear_combination 4*h-(2*t^2+p)*he

theorem source_branch_polynomial_simple (t : ℂ) (h : t^4+1=0) :
    4*t^3 ≠ 0 := by
  have hh := branch_polynomial_simple 0 1 t (by norm_num) (by norm_num)
    (by simpa using h)
  simpa using hh

theorem target_branch_polynomial_simple (t : ℂ) (h : t^4+3*t^2+2=0) :
    4*t^3+6*t ≠ 0 := by
  have hh := branch_polynomial_simple 3 2 t (by norm_num) (by norm_num) h
  norm_num at hh
  exact hh

theorem infinity_coordinates {p q : ℂ} (x : ConePoint p q) (hc : x.c=0) :
    x.b=0 ∧ x.a ≠ 0 ∧ (x.d=x.a ∨ x.d= -x.a) := by
  have hb2 : x.b^2=0 := by simpa [hc] using x.conic
  have hb : x.b=0 := by
    by_contra h
    exact (pow_ne_zero 2 h) hb2
  have hd : x.d^2=x.a^2 := by simpa [hc] using x.cover
  have ha : x.a ≠ 0 := by
    intro ha
    have hd2 : x.d^2=0 := by simpa [ha] using hd
    have hd0 : x.d=0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hd2
    exact x.nonzero ⟨ha,hb,hc,hd0⟩
  have hf : (x.d-x.a)*(x.d+x.a)=0 := by linear_combination hd
  rcases mul_eq_zero.mp hf with h | h
  · exact ⟨hb,ha,Or.inl (sub_eq_zero.mp h)⟩
  · exact ⟨hb,ha,Or.inr (eq_neg_of_add_eq_zero_left h)⟩

end Manuscript15.ProjectiveQuarticDescent20261128

#print axioms Manuscript15.ProjectiveQuarticDescent20261128.coneRel_equivalence
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.mapCone
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.mapCone_respects_scalars
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.projectiveMap
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.projectiveMap_on_representative
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.normalized_representative_unique
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.affine_coordinate_equations
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.affine_point_recovers_projective_class
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.branch_polynomial_simple
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.source_branch_polynomial_simple
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.target_branch_polynomial_simple
#print axioms Manuscript15.ProjectiveQuarticDescent20261128.infinity_coordinates
