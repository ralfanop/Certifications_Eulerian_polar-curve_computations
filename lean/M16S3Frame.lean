import M16S3Geometry

noncomputable section
open M16S3Geometry

namespace M16S3Frame

def qi : Q := (0,1,0,0)
def qj : Q := (0,0,1,0)
def qk : Q := (0,0,0,1)

def frame1 (x : Q) : Q := qMul x qi
def frame2 (x : Q) : Q := qMul x qj
def frame3 (x : Q) : Q := qMul x qk

theorem radial_tangent (x : Q) :
    qDot x (frame1 x) = 0 ∧ qDot x (frame2 x) = 0 ∧
      qDot x (frame3 x) = 0 := by
  simp only [frame1,frame2,frame3,qDot,qMul,qi,qj,qk]
  constructor
  · ring
  · constructor <;> ring

theorem orthonormal_frame (x : S3) :
    qDot (frame1 x.val) (frame1 x.val) = 1 ∧
    qDot (frame2 x.val) (frame2 x.val) = 1 ∧
    qDot (frame3 x.val) (frame3 x.val) = 1 ∧
    qDot (frame1 x.val) (frame2 x.val) = 0 ∧
    qDot (frame1 x.val) (frame3 x.val) = 0 ∧
    qDot (frame2 x.val) (frame3 x.val) = 0 := by
  simp [frame1,frame2,frame3,qMul_dot,x.property,qDot,qi,qj,qk]

theorem qMul_self_conj (x : Q) (hx : qSq x = 1) :
    qMul x (qConj x) = qOne := by
  apply Prod.ext
  · simp only [qMul,qConj,qOne]
    unfold qSq at hx
    linear_combination hx
  · apply Prod.ext
    · simp only [qMul,qConj,qOne]; ring
    · apply Prod.ext <;> simp only [qMul,qConj,qOne] <;> ring

theorem qOne_mul (x : Q) : qMul qOne x = x := by
  apply Prod.ext
  · simp [qMul,qOne]
  · apply Prod.ext
    · simp [qMul,qOne]
    · apply Prod.ext <;> simp [qMul,qOne]

theorem tangent_coordinates (x v : Q) :
    (qMul (qConj x) v).1 = qDot x v := by
  simp only [qMul,qConj,qDot]
  ring

-- Every radial-orthogonal vector has unique imaginary quaternion coordinates.
theorem tangent_frame_spans (x : S3) (v : Q) (hv : qDot x.val v = 0) :
    ∃ a b c : ℝ, qMul x.val (0,a,b,c) = v := by
  let w := qMul (qConj x.val) v
  have hw : w.1 = 0 := (tangent_coordinates x.val v).trans hv
  have h : (0,w.2.1,w.2.2.1,w.2.2.2) = w := by
    apply Prod.ext
    · exact hw.symm
    · rfl
  refine ⟨w.2.1,w.2.2.1,w.2.2.2,?_⟩
  rw [h]
  change qMul x.val (qMul (qConj x.val) v) = v
  rw [← qMul_assoc,qMul_self_conj x.val x.property,qOne_mul]

theorem tangent_frame_unique (x : S3) (a b c d e f : ℝ)
    (h : qMul x.val (0,a,b,c) = qMul x.val (0,d,e,f)) :
    a = d ∧ b = e ∧ c = f := by
  have hh := congrArg (qMul (qConj x.val)) h
  rw [← qMul_assoc,← qMul_assoc,qConj_mul_self x.val x.property,
    qOne_mul,qOne_mul] at hh
  exact ⟨congrArg (fun v : Q => v.2.1) hh,
    congrArg (fun v : Q => v.2.2.1) hh,
    congrArg (fun v : Q => v.2.2.2) hh⟩

theorem frame_left_covariant (u x j : Q) :
    qMul u (qMul x j) = qMul (qMul u x) j :=
  (qMul_assoc u x j).symm

def leftLinear (u : Q) : Q →ₗ[ℝ] Q where
  toFun := qMul u
  map_add' := by
    intro x y
    apply Prod.ext
    · simp [qMul]; ring
    · apply Prod.ext
      · simp [qMul]; ring
      · apply Prod.ext <;> simp [qMul] <;> ring
  map_smul' := by
    intro a x
    apply Prod.ext
    · simp [qMul,smul_eq_mul]; ring
    · apply Prod.ext
      · simp [qMul,smul_eq_mul]; ring
      · apply Prod.ext <;> simp [qMul,smul_eq_mul] <;> ring

def leftMap (u : Q) : Q →L[ℝ] Q :=
  (leftLinear u).toContinuousLinearMap

def frameDeriv (j : Q) (f : Q → ℝ) (x : Q) : ℝ :=
  fderiv ℝ f x (qMul x j)

-- Actual chain rule on ambient smooth extensions, not merely a formal
-- commutation premise for an abstract derivative.
theorem frameDeriv_pullback (u j : Q) (f : Q → ℝ)
    (hf : Differentiable ℝ f) (x : Q) :
    frameDeriv j (fun y => f (qMul u y)) x =
      frameDeriv j f (qMul u x) := by
  have h := (hf (qMul u x)).hasFDerivAt.comp x (leftMap u).hasFDerivAt
  have hh := h.fderiv
  change fderiv ℝ (fun y => f (qMul u y)) x =
    (fderiv ℝ f (qMul u x)).comp (leftMap u) at hh
  unfold frameDeriv
  rw [hh]
  change fderiv ℝ f (qMul u x) (qMul u (qMul x j)) =
    fderiv ℝ f (qMul u x) (qMul (qMul u x) j)
  rw [qMul_assoc]

abbrev Fields := (Q → ℝ) × (Q → ℝ) × (Q → ℝ)

def pullFields (u : Q) (v : Fields) : Fields :=
  (fun x => v.1 (qMul u x), fun x => v.2.1 (qMul u x),
    fun x => v.2.2 (qMul u x))

def Smooth1 (v : Fields) : Prop :=
  Differentiable ℝ v.1 ∧ Differentiable ℝ v.2.1 ∧ Differentiable ℝ v.2.2

-- Coordinate expression for *d on the left frame with [E_j,E_k]=2E_i.
def curlFrame (v : Fields) : Fields :=
  (fun x => frameDeriv qj v.2.2 x-frameDeriv qk v.2.1 x-2*v.1 x,
   fun x => frameDeriv qk v.1 x-frameDeriv qi v.2.2 x-2*v.2.1 x,
   fun x => frameDeriv qi v.2.1 x-frameDeriv qj v.1 x-2*v.2.2 x)

def codiffFrame (v : Fields) (x : Q) : ℝ :=
  -(frameDeriv qi v.1 x+frameDeriv qj v.2.1 x+frameDeriv qk v.2.2 x)

def gradFrame (f : Q → ℝ) : Fields :=
  (frameDeriv qi f,frameDeriv qj f,frameDeriv qk f)

def hodgeFrame (v : Fields) : Fields :=
  curlFrame (curlFrame v) + gradFrame (codiffFrame v)

theorem curlFrame_pullback (u : Q) (v : Fields) (h : Smooth1 v) :
    curlFrame (pullFields u v) = pullFields u (curlFrame v) := by
  obtain ⟨h1,h2,h3⟩ := h
  apply Prod.ext
  · funext x
    simp [curlFrame,pullFields,frameDeriv_pullback,h1,h2,h3]
  · apply Prod.ext
    · funext x
      simp [curlFrame,pullFields,frameDeriv_pullback,h1,h2,h3]
    · funext x
      simp [curlFrame,pullFields,frameDeriv_pullback,h1,h2,h3]

theorem codiffFrame_pullback (u : Q) (v : Fields) (h : Smooth1 v) :
    codiffFrame (pullFields u v) = fun x => codiffFrame v (qMul u x) := by
  obtain ⟨h1,h2,h3⟩ := h
  funext x
  simp [codiffFrame,pullFields,frameDeriv_pullback,h1,h2,h3]

theorem gradFrame_pullback (u : Q) (f : Q → ℝ) (h : Differentiable ℝ f) :
    gradFrame (fun x => f (qMul u x)) = pullFields u (gradFrame f) := by
  apply Prod.ext
  · funext x; exact frameDeriv_pullback u qi f h x
  · apply Prod.ext
    · funext x; exact frameDeriv_pullback u qj f h x
    · funext x; exact frameDeriv_pullback u qk f h x

theorem pullFields_add (u : Q) (v w : Fields) :
    pullFields u (v+w) = pullFields u v+pullFields u w := by
  rfl

theorem hodgeFrame_pullback (u : Q) (v : Fields)
    (h : Smooth1 v) (hc : Smooth1 (curlFrame v))
    (hd : Differentiable ℝ (codiffFrame v)) :
    hodgeFrame (pullFields u v) = pullFields u (hodgeFrame v) := by
  unfold hodgeFrame
  rw [curlFrame_pullback u v h,curlFrame_pullback u (curlFrame v) hc,
    codiffFrame_pullback u v h,gradFrame_pullback u (codiffFrame v) hd,pullFields_add]

def constantField (a b c : ℝ) : Fields :=
  (fun _ => a,fun _ => b,fun _ => c)

theorem frameDeriv_const (j x : Q) (c : ℝ) :
    frameDeriv j (fun _ => c) x = 0 := by
  simp [frameDeriv]

theorem curlFrame_constant (a b c : ℝ) :
    curlFrame (constantField a b c) = constantField (-2*a) (-2*b) (-2*c) := by
  apply Prod.ext
  · funext x; simp [curlFrame,constantField,frameDeriv_const]; ring
  · apply Prod.ext
    · funext x; simp [curlFrame,constantField,frameDeriv_const]; ring
    · funext x; simp [curlFrame,constantField,frameDeriv_const]; ring

theorem codiffFrame_constant (a b c : ℝ) :
    codiffFrame (constantField a b c) = fun _ => 0 := by
  funext x
  simp [codiffFrame,constantField,frameDeriv_const]

theorem hodgeFrame_constant (a b c : ℝ) :
    hodgeFrame (constantField a b c) = constantField (4*a) (4*b) (4*c) := by
  unfold hodgeFrame
  rw [curlFrame_constant,curlFrame_constant,codiffFrame_constant]
  apply Prod.ext
  · funext x; simp [gradFrame,constantField,frameDeriv_const]; ring
  · apply Prod.ext
    · funext x; simp [gradFrame,constantField,frameDeriv_const]; ring
    · funext x; simp [gradFrame,constantField,frameDeriv_const]; ring

#print axioms radial_tangent
#print axioms orthonormal_frame
#print axioms qMul_self_conj
#print axioms qOne_mul
#print axioms tangent_coordinates
#print axioms tangent_frame_spans
#print axioms tangent_frame_unique
#print axioms frame_left_covariant
#print axioms frameDeriv_pullback
#print axioms curlFrame_pullback
#print axioms codiffFrame_pullback
#print axioms gradFrame_pullback
#print axioms pullFields_add
#print axioms hodgeFrame_pullback
#print axioms frameDeriv_const
#print axioms curlFrame_constant
#print axioms codiffFrame_constant
#print axioms hodgeFrame_constant
end M16S3Frame
