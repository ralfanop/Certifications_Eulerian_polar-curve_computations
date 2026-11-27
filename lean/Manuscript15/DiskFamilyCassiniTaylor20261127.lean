import Manuscript15.DiskFamily20261127

/-! M15 Lemma 8.1, equation (355): local Cassini graph, with
an explicit fourth-order remainder, and curvature contact with the circle.
Candidate formalization; exact-head CI must confirm the proofs. -/
noncomputable section
open Complex
namespace Manuscript15.DiskFamily20261127

def cassiniLevel (x y : ℝ) : ℝ :=
  (1+y^2)^2+2*x^2*(y^2-1)+x^4

def cassiniGraph (t x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt ((1+t^2)^2+4*x^2)-1-x^2)

def cassiniCurvature (t : ℝ) : ℝ :=
  (1-t^2)/(t*(1+t^2))

theorem cassini_level_identity (x y : ℝ) :
    ‖(⟨x,y⟩ : ℂ)^2-1‖^2=cassiniLevel x y := by
  rw [norm_sub_rev,Complex.sq_norm,Complex.normSq_apply,one_sub_sq_re,one_sub_sq_im]
  change (1-x^2+y^2)^2+(-(2*x*y))^2=_
  unfold cassiniLevel
  ring

theorem cassini_graph_on_level {t x : ℝ} (ht : 0 < t)
    (hx : x^2 ≤ t^2) :
    0 ≤ cassiniGraph t x ∧
      cassiniLevel x (cassiniGraph t x)=(1+t^2)^2 := by
  let a := 1+t^2
  let q := Real.sqrt (a^2+4*x^2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hq : a ≤ q := by
    dsimp [q]
    rw [← Real.sqrt_sq ha]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hqn : 0 ≤ q-1-x^2 := by dsimp [a] at hq; linarith
  have hy : (cassiniGraph t x)^2=q-1-x^2 := by
    unfold cassiniGraph
    exact Real.sq_sqrt hqn
  have hq2 : q^2=a^2+4*x^2 := Real.sq_sqrt (by positivity)
  refine ⟨Real.sqrt_nonneg _,?_⟩
  unfold cassiniLevel
  rw [hy]
  dsimp [a] at hq2
  nlinarith

/-- The nonnegative local graph is uniquely determined by the Cassini level. -/
theorem cassini_graph_unique {t x y : ℝ} (hy : 0 ≤ y)
    (he : cassiniLevel x y=(1+t^2)^2) :
    y=cassiniGraph t x := by
  have hq : (1+x^2+y^2)^2=(1+t^2)^2+4*x^2 := by
    unfold cassiniLevel at he
    nlinarith
  have hq' : Real.sqrt ((1+t^2)^2+4*x^2)=1+x^2+y^2 := by
    rw [← hq,Real.sqrt_sq (by positivity)]
  unfold cassiniGraph
  rw [hq']
  rw [show 1+x^2+y^2-1-x^2=y^2 by ring,Real.sqrt_sq hy]

/-- Explicit bound for the fourth-order remainder, proved by algebraic
rationalization of the actual level-set equation (no Taylor axiom). -/
theorem cassini_level_remainder {t x y : ℝ} (ht : 0 < t) (hy : 0 ≤ y)
    (he : cassiniLevel x y=(1+t^2)^2) :
    |y-t-cassiniCurvature t*x^2/2| ≤
      ((2+9/t^2)/(2*t))*x^4 := by
  let a := 1+t^2
  let d := x^2+y^2-t^2
  let e := y-t
  have ha : 1 ≤ a := by dsimp [a]; nlinarith
  have hap : 0 < a := by linarith
  have hsum : 0 < 2*a+d := by dsimp [a,d]; nlinarith [sq_nonneg t,sq_nonneg x,sq_nonneg y]
  have hp : d*(2*a+d)=4*x^2 := by
    dsimp [a,d]
    unfold cassiniLevel at he
    nlinarith
  have hd0 : 0 ≤ d := by
    by_contra! hneg
    have := mul_neg_of_neg_of_pos hneg hsum
    nlinarith [sq_nonneg x]
  have hd2 : d ≤ 2*x^2 := by
    have hmul := mul_nonneg hd0 (show 0 ≤ 2*a+d-2 by linarith)
    nlinarith
  have heprod : e*(y+t)=d-x^2 := by dsimp [e,d]; ring
  have hb : |d-x^2| ≤ x^2 := by
    rw [abs_le]
    constructor <;> linarith
  have heabs : |e|*t ≤ x^2 := by
    have hpos : 0 ≤ y+t := by linarith
    have h1 : |e|*(y+t)=|d-x^2| := by
      rw [← abs_of_nonneg hpos,← abs_mul,heprod]
    have h2 := mul_le_mul_of_nonneg_left (show t ≤ y+t by linarith) (abs_nonneg e)
    exact h2.trans (h1.le.trans hb)
  have hediv : |e| ≤ 3*x^2/t := by
    apply (le_div_iff₀ ht).2
    nlinarith [sq_nonneg x]
  have hesq : e^2 ≤ 9*x^4/t^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg e) hediv 2
    rw [sq_abs,div_pow] at h
    convert h using 1 <;> ring
  have hrel : 2*t*e+e^2=d-x^2 := by dsimp [e,d]; ring
  have hcoef : cassiniCurvature t=(2-a)/(t*a) := by unfold cassiniCurvature; dsimp [a]; ring
  have hdform : d = 2*x^2/a-d^2/(2*a) := by
    field_simp [hap.ne']
    nlinarith [hp]
  have hcoeff : 2*t*(cassiniCurvature t*x^2/2)=2*x^2/a-x^2 := by
    rw [hcoef]
    field_simp [ht.ne',hap.ne'] <;> ring
  have herr : 2*t*(e-cassiniCurvature t*x^2/2) = -(d^2/(2*a))-e^2 := by
    calc
      _ = 2*t*e-(2*x^2/a-x^2) := by rw [← hcoeff]; ring
      _ = _ := by linarith [hrel,hdform]
  have hdSq : d^2 ≤ 4*x^4 := by
    have h := pow_le_pow_left₀ hd0 hd2 2
    convert h using 1 <;> ring
  have hddiv : d^2/(2*a) ≤ 2*x^4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*a)).2
    have hmul := mul_nonneg (show 0 ≤ a-1 by linarith) (show 0 ≤ x^4 by positivity)
    nlinarith
  have hnonneg : 0 ≤ d^2/(2*a)+e^2 := by positivity
  have hAbs : (2*t)*|e-cassiniCurvature t*x^2/2| = d^2/(2*a)+e^2 := by
    rw [← abs_of_pos (by positivity : 0 < 2*t),← abs_mul,herr]
    rw [show -(d^2/(2*a))-e^2 = -(d^2/(2*a)+e^2) by ring,abs_neg,abs_of_nonneg hnonneg]
  have hfinal : (2*t)*|e-cassiniCurvature t*x^2/2| ≤
      (2+9/t^2)*x^4 := by
    rw [hAbs]
    calc
      _ ≤ 2*x^4+9*x^4/t^2 := add_le_add hddiv hesq
      _ = _ := by ring
  have hden : 0 < 2*t := by positivity
  change |e-cassiniCurvature t*x^2/2| ≤ ((2+9/t^2)/(2*t))*x^4
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  simpa [mul_comm] using hfinal

theorem cassini_graph_remainder {t x : ℝ} (ht : 0 < t) (hx : x^2 ≤ t^2) :
    |cassiniGraph t x-t-cassiniCurvature t*x^2/2| ≤
      ((2+9/t^2)/(2*t))*x^4 := by
  obtain ⟨hy,he⟩ := cassini_graph_on_level ht hx
  exact cassini_level_remainder ht hy he

/-- The lower circle graph has its own explicit fourth-order remainder. -/
def lowerCircleGraph (r x : ℝ) : ℝ := 1-Real.sqrt (r^2-x^2)

theorem lower_circle_remainder {r x : ℝ} (hr : 0 < r) (hx : x^2 ≤ r^2) :
    |lowerCircleGraph r x-(1-r)-x^2/(2*r)| ≤ x^4/(2*r^3) := by
  let s := Real.sqrt (r^2-x^2)
  let d := r-s
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=r^2-x^2 := Real.sq_sqrt (sub_nonneg.mpr hx)
  have hsr : s ≤ r := by
    by_contra! hh
    have hp := mul_pos (sub_pos.mpr hh) (show 0 < s+r by linarith)
    nlinarith [sq_nonneg x]
  have hd : 0 ≤ d := sub_nonneg.mpr hsr
  have hp : d*(r+s)=x^2 := by dsimp [d]; nlinarith
  have hdiv : d ≤ x^2/r := by
    apply (le_div_iff₀ hr).2
    have hm := mul_nonneg hd hs
    nlinarith
  have hsq : d^2 ≤ x^4/r^2 := by
    have h := pow_le_pow_left₀ hd hdiv 2
    rw [div_pow] at h
    convert h using 1 <;> ring
  have he : d-x^2/(2*r)=d^2/(2*r) := by
    have h : 2*r*d=x^2+d^2 := by dsimp [d]; nlinarith
    field_simp [hr.ne']
    nlinarith
  have hnon : 0 ≤ d^2/(2*r) := by positivity
  change |1-s-(1-r)-x^2/(2*r)| ≤ _
  rw [show 1-s-(1-r)=d by dsimp [d]; ring,he,abs_of_nonneg hnon]
  calc
    _ ≤ (x^4/r^2)/(2*r) := div_le_div_of_nonneg_right hsq (by positivity)
    _ = _ := by field_simp [hr.ne']; ring

theorem cassini_circle_curvature_contact {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    cassiniCurvature (1-r)=1/r ↔ r=threshold := by
  have ht : 0 < 1-r := by linarith
  have ht1 : 1-r < 1 := by linarith
  have h := curvature_contact ht ht1
  unfold cassiniCurvature
  rw [show 1-(1-r)=r by ring] at h
  rw [h]
  unfold threshold
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg 2
  constructor
  · intro he
    have hf : (r-(2-Real.sqrt 2))*(r-(2+Real.sqrt 2))=0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · linarith
    · linarith
  · intro he
    rw [he]
    nlinarith

end Manuscript15.DiskFamily20261127
#print axioms Manuscript15.DiskFamily20261127.cassini_level_identity
#print axioms Manuscript15.DiskFamily20261127.cassini_graph_on_level
#print axioms Manuscript15.DiskFamily20261127.cassini_graph_unique
#print axioms Manuscript15.DiskFamily20261127.cassini_level_remainder
#print axioms Manuscript15.DiskFamily20261127.cassini_graph_remainder
#print axioms Manuscript15.DiskFamily20261127.lower_circle_remainder
#print axioms Manuscript15.DiskFamily20261127.cassini_circle_curvature_contact
