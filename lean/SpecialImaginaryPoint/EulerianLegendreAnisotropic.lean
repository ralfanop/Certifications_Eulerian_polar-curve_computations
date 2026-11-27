import SpecialImaginaryPoint.EulerianLegendreInverseRate

/-! Actual coupled potential, quantitative remainder, and uniform anisotropic scaling.
The rotation and coupling are those of Proposition 11.1. All remainder bounds
are derived from the actual normalized Legendre rate, not imposed as axioms. -/
namespace M14.EulerianLegendre
noncomputable section

def rotationQ : ℝ := 1 / Real.sqrt 2

theorem rotationQ_sq : rotationQ^2 = 1/2 := by
  rw [rotationQ, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem rotationQ_nonneg : 0 ≤ rotationQ := by unfold rotationQ; positivity

def actualCoupledPotential (a u w : ℝ) : ℝ :=
  normalizedRate ((u+w)*rotationQ) + normalizedRate ((u-w)*rotationQ)
    - a*((u+w)*rotationQ)*((u-w)*rotationQ)

def coupledApproximation (a u w : ℝ) : ℝ :=
  w^2 + (u^4+6*u^2*w^2+w^4)/40 + (1-a)*(u^2-w^2)/2

theorem actualCoupledPotential_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a u w : ℝ, |u| ≤ 1/4 → |w| ≤ 1/4 →
      |actualCoupledPotential a u w - coupledApproximation a u w|
        ≤ C*(u^2+w^2)^3 := by
  obtain ⟨C,hC,h⟩ := normalizedRate_order_six_bound
  refine ⟨2*C, by positivity, fun a u w hu hw => ?_⟩
  let s := (u+w)*rotationQ
  let t := (u-w)*rotationQ
  have hq := rotationQ_sq
  have hq0 := rotationQ_nonneg
  have hq1 : rotationQ ≤ 1 := by nlinarith [sq_nonneg (rotationQ-1)]
  have hs0 : |u+w| ≤ 1/2 := (abs_add_le u w).trans (by linarith)
  have ht0 : |u-w| ≤ 1/2 := by
    rw [sub_eq_add_neg]
    exact (abs_add_le u (-w)).trans (by rw [abs_neg]; linarith)
  have hs : |s| ≤ 1/2 := by
    dsimp [s]
    rw [abs_mul, abs_of_nonneg hq0]
    nlinarith [mul_nonneg (abs_nonneg (u+w)) (sub_nonneg.mpr hq1)]
  have ht : |t| ≤ 1/2 := by
    dsimp [t]
    rw [abs_mul, abs_of_nonneg hq0]
    nlinarith [mul_nonneg (abs_nonneg (u-w)) (sub_nonneg.mpr hq1)]
  have hst : s^2+t^2 = u^2+w^2 := by
    calc
      _ = 2*rotationQ^2*(u^2+w^2) := by dsimp [s,t]; ring
      _ = _ := by rw [hq]; ring
  have hpower (r : ℝ) (hr : r^2 ≤ u^2+w^2) :
      |r|^6 ≤ (u^2+w^2)^3 := by
    have hr2 : |r|^2 = r^2 := by rw [← abs_pow]; exact abs_of_nonneg (sq_nonneg r)
    calc
      |r|^6 = (|r|^2)^3 := by ring
      _ = (r^2)^3 := by rw [hr2]
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg r) hr 3
  have hsp := hpower s (by nlinarith [sq_nonneg t])
  have htp := hpower t (by nlinarith [sq_nonneg s])
  have hq4 : rotationQ^4 = 1/4 := by
    calc
      _ = (rotationQ^2)^2 := by ring
      _ = _ := by rw [hq]; norm_num
  have hj : (s^2/2+s^4/20)+(t^2/2+t^4/20)-a*s*t =
      coupledApproximation a u w := by
    calc
      _ = rotationQ^2*(u^2+w^2) +
        rotationQ^4*(u^4+6*u^2*w^2+w^4)/10-a*rotationQ^2*(u^2-w^2) := by
          dsimp [s,t]; ring
      _ = _ := by rw [hq,hq4]; unfold coupledApproximation; ring
  have he : actualCoupledPotential a u w-coupledApproximation a u w =
      (normalizedRate s-(s^2/2+s^4/20))+(normalizedRate t-(t^2/2+t^4/20)) := by
    change normalizedRate s + normalizedRate t - a*s*t - coupledApproximation a u w = _
    rw [← hj]
    ring
  rw [he]
  calc
    _ ≤ |normalizedRate s-(s^2/2+s^4/20)| +
        |normalizedRate t-(t^2/2+t^4/20)| := abs_add_le _ _
    _ ≤ C*|s|^6+C*|t|^6 := add_le_add (h s hs) (h t ht)
    _ ≤ 2*C*(u^2+w^2)^3 := by
      linarith [mul_le_mul_of_nonneg_left hsp hC, mul_le_mul_of_nonneg_left htp hC]

def anisotropicLimit (v z l : ℝ) : ℝ := z^2+v^4/40+6*l*v^2

def actualScaledPotential (e v z l : ℝ) : ℝ :=
  actualCoupledPotential (1/(1+12*l*e^2)) (e*v) (e^2*z) / e^4

theorem actualScaledPotential_box_bound (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e v z l : ℝ,
      0 < e → e ≤ 1/(24*R) → |v| ≤ R → |z| ≤ R → |l| ≤ R →
        |actualScaledPotential e v z l - anisotropicLimit v z l| ≤ C*e^2 := by
  obtain ⟨A,hA,hrem⟩ := actualCoupledPotential_remainder
  let D : ℝ := R^2+12*R^3
  let C : ℝ := A*(2*R^2)^3+7*R^4/40+12*R*D
  have hR0 : 0 ≤ R := by linarith
  have hRp : 0 < R := by linarith
  have hB : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C, by dsimp [C]; positivity, fun e v z l he hcut hv hz hl => ?_⟩
  have heR : e*R ≤ 1/24 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 24*R)).mp hcut
    nlinarith
  have he1 : e ≤ 1 := by linarith [mul_le_mul_of_nonneg_left hR he.le]
  have he21 : e^2 ≤ 1 := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1)]
  have he2 : e^2 ≤ e := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1)]
  have hv2 : v^2 ≤ R^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg v) hv 2
    rw [← abs_pow, abs_of_nonneg (sq_nonneg v)] at hh
    exact hh
  have hz2 : z^2 ≤ R^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg z) hz 2
    rw [← abs_pow, abs_of_nonneg (sq_nonneg z)] at hh
    exact hh
  have hu : |e*v| ≤ 1/4 := by
    rw [abs_mul, abs_of_pos he]
    linarith [mul_le_mul_of_nonneg_left hv he.le]
  have hw : |e^2*z| ≤ 1/4 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg e)]
    have hh := mul_le_mul_of_nonneg_left hz (sq_nonneg e)
    linarith [mul_le_mul_of_nonneg_right he2 hR0]
  let d := 1+12*l*e^2
  have hde : |12*l*e^2| ≤ 1/2 := by
    calc
      _ = 12*|l| *e^2 := by rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg e)]; norm_num
      _ ≤ 12*R*e^2 := by gcongr
      _ ≤ 12*R*e := by gcongr
      _ ≤ _ := by nlinarith
  have hd : 1/2 ≤ d := by dsimp [d]; linarith [(abs_le.mp hde).1]
  have hdp : 0 < d := by linarith
  have he4 : e^4 ≤ e^2 := by
    have hh := mul_le_mul_of_nonneg_right he21 (sq_nonneg e)
    nlinarith
  have hrad : (e*v)^2+(e^2*z)^2 ≤ e^2*(2*R^2) := by
    have h1 := mul_le_mul_of_nonneg_left hv2 (sq_nonneg e)
    have h2 := mul_le_mul_of_nonneg_left hz2 (sq_nonneg e)
    have h3 := mul_le_mul_of_nonneg_right he4 (sq_nonneg z)
    nlinarith
  have hrem' :
      |actualCoupledPotential (1/d) (e*v) (e^2*z) -
        coupledApproximation (1/d) (e*v) (e^2*z)| ≤ A*(2*R^2)^3*e^6 := by
    calc
      _ ≤ A*((e*v)^2+(e^2*z)^2)^3 := hrem _ _ _ hu hw
      _ ≤ A*(e^2*(2*R^2))^3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hrad 3) hA
      _ = _ := by ring
  have hj : coupledApproximation (1/d) (e*v) (e^2*z) -
      e^4*anisotropicLimit v z l =
      e^6*((6*v^2*z^2+e^2*z^4)/40-6*l*(z^2+12*l*v^2)/d) := by
    unfold coupledApproximation anisotropicLimit
    dsimp [d] at *
    field_simp [ne_of_gt hdp] <;> ring
  have hprod := mul_le_mul hv2 hz2 (sq_nonneg z) (sq_nonneg R)
  have hz4 : z^4 ≤ R^4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg z) hz 4
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ z^4)] at hh
    exact hh
  have hquad : |(6*v^2*z^2+e^2*z^4)/40| ≤ 7*R^4/40 := by
    rw [abs_of_nonneg (by positivity)]
    have hh := mul_le_mul_of_nonneg_right he21 (by positivity : 0 ≤ z^4)
    nlinarith
  have hterm : |z^2+12*l*v^2| ≤ D := by
    calc
      _ ≤ |z^2| +|12*l*v^2| := abs_add_le _ _
      _ = z^2+12*|l| *v^2 := by
        rw [abs_of_nonneg (sq_nonneg z),abs_mul,abs_mul,abs_of_nonneg (sq_nonneg v)]
        norm_num
      _ ≤ D := by
        have hh := mul_le_mul hl hv2 (sq_nonneg v) hR0
        dsimp [D]
        nlinarith
  have hnum : |6*l*(z^2+12*l*v^2)| ≤ 6*R*D := by
    calc
      _ = 6*|l| *|z^2+12*l*v^2| := by simp [abs_mul]
      _ ≤ _ := by gcongr
  have hdiv : |6*l*(z^2+12*l*v^2)/d| ≤ 12*R*D := by
    rw [abs_div,abs_of_pos hdp]
    apply (div_le_iff₀ hdp).2
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 12*R*D)
    nlinarith
  have hinner : |(6*v^2*z^2+e^2*z^4)/40-6*l*(z^2+12*l*v^2)/d| ≤
      7*R^4/40+12*R*D := by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add hquad hdiv)
  have hjet : |coupledApproximation (1/d) (e*v) (e^2*z)-e^4*anisotropicLimit v z l|
      ≤ (7*R^4/40+12*R*D)*e^6 := by
    rw [hj, abs_mul, abs_of_nonneg (by positivity : 0 ≤ e^6)]
    calc
      _ ≤ e^6*(7*R^4/40+12*R*D) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = _ := by ring
  have hcombined : |actualCoupledPotential (1/d) (e*v) (e^2*z)-e^4*anisotropicLimit v z l|
      ≤ C*e^6 := by
    have hsplit : actualCoupledPotential (1/d) (e*v) (e^2*z)-e^4*anisotropicLimit v z l =
      (actualCoupledPotential (1/d) (e*v) (e^2*z)-coupledApproximation (1/d) (e*v) (e^2*z))+
      (coupledApproximation (1/d) (e*v) (e^2*z)-e^4*anisotropicLimit v z l) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    calc
      _ ≤ A*(2*R^2)^3*e^6+(7*R^4/40+12*R*D)*e^6 := add_le_add hrem' hjet
      _ = _ := by dsimp [C]; ring
  have he4p : 0 < e^4 := pow_pos he _
  change |actualCoupledPotential (1/d) (e*v) (e^2*z)/e^4-anisotropicLimit v z l| ≤ C*e^2
  rw [show actualCoupledPotential (1/d) (e*v) (e^2*z)/e^4-anisotropicLimit v z l =
    (actualCoupledPotential (1/d) (e*v) (e^2*z)-e^4*anisotropicLimit v z l)/e^4 by
      field_simp [ne_of_gt he4p] <;> ring, abs_div, abs_of_pos he4p]
  apply (div_le_iff₀ he4p).2
  convert hcombined using 1 <;> ring

theorem actualScaledPotential_locally_uniform (R η : ℝ) (hR : 1 ≤ R) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e v z l : ℝ,
      0 < e → e ≤ δ → |v| ≤ R → |z| ≤ R → |l| ≤ R →
        |actualScaledPotential e v z l-anisotropicLimit v z l| < η := by
  obtain ⟨C,hC,h⟩ := actualScaledPotential_box_bound R hR
  have hRp : 0 < R := by linarith
  let δ := min (1/(24*R)) (min 1 (η/(2*(C+1))))
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  refine ⟨δ,hδ,fun e v z l he heδ hv hz hl => ?_⟩
  have hecut := heδ.trans (min_le_left _ _)
  have hemin := heδ.trans (min_le_right _ _)
  have he1 : e ≤ 1 := hemin.trans (min_le_left _ _)
  have heη : e ≤ η/(2*(C+1)) := hemin.trans (min_le_right _ _)
  have he2 : e^2 ≤ e := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1)]
  have hsmall := (le_div_iff₀ (by positivity : 0 < 2*(C+1))).mp heη
  have hh := h e v z l he hecut hv hz hl
  nlinarith [mul_le_mul_of_nonneg_left he2 hC]

def scaleM (M : ℝ) : ℝ := 1 / Real.sqrt (Real.sqrt M)

def actualPotentialM (M l u w : ℝ) : ℝ :=
  actualCoupledPotential (1/(12*(1/12+l/Real.sqrt M))) u w

theorem scaleM_pos (M : ℝ) (hM : 0 < M) : 0 < scaleM M := by
  unfold scaleM
  positivity

theorem scaleM_sq (M : ℝ) (hM : 0 < M) : scaleM M ^ 2 = 1/Real.sqrt M := by
  rw [scaleM,div_pow,one_pow,Real.sq_sqrt (Real.sqrt_nonneg M)]

theorem scaleM_fourth (M : ℝ) (hM : 0 < M) : scaleM M ^ 4 = 1/M := by
  calc
    _ = (scaleM M^2)^2 := by ring
    _ = _ := by rw [scaleM_sq M hM,div_pow,one_pow,Real.sq_sqrt hM.le]

theorem actualPotentialM_scaling (M v z l : ℝ) (hM : 0 < M) :
    M*actualPotentialM M l (scaleM M*v) ((scaleM M)^2*z) =
      actualScaledPotential (scaleM M) v z l := by
  have hd : 1+12*l*(scaleM M)^2 = 12*(1/12+l/Real.sqrt M) := by
    rw [scaleM_sq M hM]; ring
  unfold actualPotentialM actualScaledPotential
  rw [hd,scaleM_fourth M hM]
  field_simp [ne_of_gt hM] <;> ring

theorem actualPotentialM_locally_uniform (R η : ℝ) (hR : 1 ≤ R) (hη : 0 < η) :
    ∃ M0 : ℝ, 0 < M0 ∧ ∀ M v z l : ℝ,
      M0 ≤ M → |v| ≤ R → |z| ≤ R → |l| ≤ R →
      |M*actualPotentialM M l (scaleM M*v) ((scaleM M)^2*z)-anisotropicLimit v z l| < η := by
  obtain ⟨δ,hδ,h⟩ := actualScaledPotential_locally_uniform R η hR hη
  let M0 := 1/δ^4
  have hM0 : 0 < M0 := by dsimp [M0]; positivity
  refine ⟨M0,hM0,fun M v z l hM hv hz hl => ?_⟩
  have hMp : 0 < M := hM0.trans_le hM
  have he := scaleM_pos M hMp
  have hpow : (scaleM M)^4 ≤ δ^4 := by
    rw [scaleM_fourth M hMp]
    have hh := one_div_le_one_div_of_le hM0 hM
    dsimp [M0] at hh
    simpa using hh
  have heδ : scaleM M ≤ δ := by
    by_contra! hh
    have hlt : δ^4 < (scaleM M)^4 := by gcongr
    linarith
  rw [actualPotentialM_scaling M v z l hMp]
  exact h _ v z l he heδ hv hz hl

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.rotationQ_sq
#print axioms M14.EulerianLegendre.rotationQ_nonneg
#print axioms M14.EulerianLegendre.actualCoupledPotential_remainder
#print axioms M14.EulerianLegendre.actualScaledPotential_box_bound
#print axioms M14.EulerianLegendre.actualScaledPotential_locally_uniform
#print axioms M14.EulerianLegendre.scaleM_pos
#print axioms M14.EulerianLegendre.scaleM_sq
#print axioms M14.EulerianLegendre.scaleM_fourth
#print axioms M14.EulerianLegendre.actualPotentialM_scaling
#print axioms M14.EulerianLegendre.actualPotentialM_locally_uniform
