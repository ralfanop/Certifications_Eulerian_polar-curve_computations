import EulerianGrothendieck.KreinBilateralJacobi20261127
import Mathlib.Analysis.SpecialFunctions.Exp

/-! M12 Theorem 5.16: uniform exponential resolvent localisation.
The bounded capped diagonal conjugation is on the literal bilateral
Hilbert space. The norm estimate uses the resolvent identity directly,
so no global Taylor expansion of unbounded formal arrays is required. -/
noncomputable section
open scoped ENNReal
namespace M12JacobiResolventWeights
open M12BilateralJacobi Manuscript16.V166L2SpectralInverse

theorem exp_diff_le (a γ : ℝ) (hγ : 0 ≤ γ) (ha : |a| ≤ γ) :
    |Real.exp a-1| ≤ Real.exp γ-1 := by
  have hu := Real.exp_le_exp.mpr (abs_le.mp ha).2
  have hl := Real.exp_le_exp.mpr (abs_le.mp ha).1
  have hprod : Real.exp (-γ)*Real.exp γ = 1 := by
    rw [← Real.exp_add]; simp
  have hsum : 2 ≤ Real.exp (-γ)+Real.exp γ := by
    have h := sq_nonneg (Real.exp γ-1)
    have hp := Real.exp_pos γ
    apply (le_of_mul_le_mul_right _ hp)
    nlinarith [hprod]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def cap (l : ℤ) (L : ℝ) (k : ℤ) : ℝ := min |(k:ℝ)-l| L

theorem cap_nonneg (l : ℤ) {L : ℝ} (hL : 0 ≤ L) (k : ℤ) : 0 ≤ cap l L k :=
  le_min (abs_nonneg _) hL

theorem cap_le (l : ℤ) (L : ℝ) (k : ℤ) : cap l L k ≤ L := min_le_right _ _

theorem cap_lipschitz (l : ℤ) (L : ℝ) (k m : ℤ) :
    |cap l L k-cap l L m| ≤ |(k:ℝ)-m| := by
  have h := abs_abs_sub_abs_le_abs_sub ((k:ℝ)-l) ((m:ℝ)-l)
  rw [show (k:ℝ)-l-((m:ℝ)-l)=(k:ℝ)-m by ring] at h
  unfold cap
  rw [abs_le] at h ⊢
  by_cases hk : |(k:ℝ)-l| ≤ L <;> by_cases hm : |(m:ℝ)-l| ≤ L
  · rw [min_eq_left hk,min_eq_left hm]; exact h
  · rw [min_eq_left hk,min_eq_right (le_of_not_ge hm)]; constructor <;> linarith [h.1,h.2,abs_nonneg ((k:ℝ)-m)]
  · rw [min_eq_right (le_of_not_ge hk),min_eq_left hm]; constructor <;> linarith [h.1,h.2,abs_nonneg ((k:ℝ)-m)]
  · rw [min_eq_right (le_of_not_ge hk),min_eq_right (le_of_not_ge hm)]; constructor <;> linarith [abs_nonneg ((k:ℝ)-m)]

section Weighted
variable (ρ : ℤ → ℝ) (L γ : ℝ) (hγ : 0 ≤ γ)
variable (hρ0 : ∀ k, 0 ≤ ρ k) (hρL : ∀ k, ρ k ≤ L)

def Wplus : Op :=
  diagonal (fun k => (Real.exp (γ*ρ k):ℂ)) (Real.exp (γ*L)) (Real.exp_nonneg _)
    (fun k => by
      rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hρL k) hγ))

def Wminus : Op :=
  diagonal (fun k => (Real.exp (-(γ*ρ k)):ℂ)) 1 zero_le_one
    (fun k => by
      rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hγ (hρ0 k))))

theorem weights_inverse :
    Wplus ρ L γ hγ hρL * Wminus ρ γ hγ hρ0 = 1 ∧
    Wminus ρ γ hγ hρ0 * Wplus ρ L γ hγ hρL = 1 := by
  constructor <;> ext x k
  · change (Real.exp (γ*ρ k):ℂ)*((Real.exp (-(γ*ρ k)):ℂ)*x k) = x k
    rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
    simp
  · change (Real.exp (-(γ*ρ k)):ℂ)*((Real.exp (γ*ρ k):ℂ)*x k) = x k
    rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
    simp

def perturbationCoeff (u : Bonds) (d : ℤ) (k : ℤ) : ℂ :=
  ((if d = -1 then u.1 k else u.1 (k+1)) *
    (Real.exp (γ*(ρ k-ρ (k+d)))-1):ℝ)

theorem perturbationCoeff_bound (u : Bonds) (d : ℤ)
    (hstep : ∀ k, |ρ k-ρ (k+d)| ≤ 1) (k : ℤ) :
    ‖perturbationCoeff ρ γ u d k‖ ≤ (Real.exp γ-1)/2 := by
  have hg : 0 ≤ Real.exp γ-1 := sub_nonneg.mpr (Real.one_le_exp.mpr hγ)
  have harg : |γ*(ρ k-ρ (k+d))| ≤ γ := by
    rw [abs_mul,abs_of_nonneg hγ]
    simpa using mul_le_mul_of_nonneg_left (hstep k) hγ
  unfold perturbationCoeff
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul]
  have hu0 : 0 ≤ (if d = -1 then u.1 k else u.1 (k+1)) := by
    split_ifs <;> exact (u.2 _).1
  have hu1 : (if d = -1 then u.1 k else u.1 (k+1)) ≤ 1/2 := by
    split_ifs <;> exact (u.2 _).2
  rw [abs_of_nonneg hu0]
  calc
    _ ≤ (1/2)*(Real.exp γ-1) :=
      mul_le_mul hu1 (exp_diff_le _ _ hγ harg) (abs_nonneg _) (by norm_num)
    _ = _ := by ring

def deltaOp (u : Bonds) (d : ℤ) (hstep : ∀ k, |ρ k-ρ (k+d)| ≤ 1) : Op :=
  diagonal (perturbationCoeff ρ γ u d) ((Real.exp γ-1)/2)
    (by have := Real.one_le_exp.mpr hγ; linarith)
    (perturbationCoeff_bound ρ γ hγ u d hstep) * shift d

theorem deltaOp_norm (u : Bonds) (d : ℤ) (hstep : ∀ k, |ρ k-ρ (k+d)| ≤ 1) :
    ‖deltaOp ρ γ hγ u d hstep‖ ≤ (Real.exp γ-1)/2 := by
  unfold deltaOp
  calc
    _ ≤ ‖diagonal (perturbationCoeff ρ γ u d) ((Real.exp γ-1)/2)
      (by have := Real.one_le_exp.mpr hγ; linarith)
      (perturbationCoeff_bound ρ γ hγ u d hstep)‖ * ‖shift d‖ := norm_mul_le _ _
    _ ≤ ((Real.exp γ-1)/2)*1 := mul_le_mul
      (diagonal_norm_le _ _ _ _) (shift_norm_le d) (norm_nonneg _)
      (by have := Real.one_le_exp.mpr hγ; linarith)
    _ = _ := mul_one _

theorem conjugated_difference (u : Bonds)
    (hm : ∀ k, |ρ k-ρ (k+(-1))| ≤ 1) (hp : ∀ k, |ρ k-ρ (k+1)| ≤ 1) :
    Wplus ρ L γ hγ hρL * J u * Wminus ρ γ hγ hρ0 - J u =
      deltaOp ρ γ hγ u (-1) hm + deltaOp ρ γ hγ u 1 hp := by
  ext x k
  change (Real.exp (γ*ρ k):ℂ) * (J u (Wminus ρ γ hγ hρ0 x) k) - J u x k =
    perturbationCoeff ρ γ u (-1) k * x (k+(-1)) +
    perturbationCoeff ρ γ u 1 k * x (k+1)
  rw [J_apply,J_apply]
  change (Real.exp (γ*ρ k):ℂ)*((u.1 k:ℂ)*((Real.exp (-(γ*ρ (k-1))):ℂ)*x (k-1))+
    (u.1 (k+1):ℂ)*((Real.exp (-(γ*ρ (k+1))):ℂ)*x (k+1))) -
    ((u.1 k:ℂ)*x (k-1)+(u.1 (k+1):ℂ)*x (k+1)) = _
  have he (m : ℤ) : (Real.exp (γ*(ρ k-ρ m)):ℂ) =
      (Real.exp (γ*ρ k):ℂ)*(Real.exp (-(γ*ρ m)):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 1
    ring
  simp only [perturbationCoeff,if_pos rfl,show (1:ℤ) ≠ -1 by norm_num,if_false,
    Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,← sub_eq_add_neg,he]
  ring

theorem conjugated_norm (u : Bonds)
    (hm : ∀ k, |ρ k-ρ (k+(-1))| ≤ 1) (hp : ∀ k, |ρ k-ρ (k+1)| ≤ 1) :
    ‖Wplus ρ L γ hγ hρL * J u * Wminus ρ γ hγ hρ0 - J u‖ ≤ Real.exp γ-1 := by
  rw [conjugated_difference ρ L γ hγ hρ0 hρL u hm hp]
  calc
    _ ≤ ‖deltaOp ρ γ hγ u (-1) hm‖+‖deltaOp ρ γ hγ u 1 hp‖ := norm_add_le _ _
    _ ≤ (Real.exp γ-1)/2+(Real.exp γ-1)/2 :=
      add_le_add (deltaOp_norm ρ γ hγ u (-1) hm) (deltaOp_norm ρ γ hγ u 1 hp)
    _ = _ := by ring

end Weighted

/-- Exact resolvent comparison for a bounded similarity. -/
theorem similarity_resolvent_bound (J R W V : Op) (z : ℂ) (δ : ℝ)
    (hWV : W*V=1) (hVW : V*W=1)
    (hR₁ : (z • (1:Op)-J)*R=1) (hR₂ : R*(z • (1:Op)-J)=1)
    (hδ : ‖W*J*V-J‖ ≤ δ) (hsmall : ‖R‖*δ ≤ 1/2) :
    ‖W*R*V‖ ≤ 2*‖R‖ := by
  let Z : Op := z • (1:Op)
  let K := W*J*V
  let S := W*R*V
  have hz : W*Z*V = Z := by
    dsimp [Z]
    rw [mul_smul_comm,smul_mul_assoc,mul_one,hWV]
  have hK : Z-K = W*(Z-J)*V := by
    rw [mul_sub,sub_mul,hz]
  have hS : (Z-K)*S=1 := by
    rw [hK]
    change (W*(Z-J)*V)*(W*R*V)=1
    calc
      _ = W*((Z-J)*(V*W)*R)*V := by noncomm_ring
      _ = 1 := by rw [hVW,mul_one,hR₁,mul_one,hWV]
  have hdiff : (Z-J)*S=1+(K-J)*S := by
    calc
      _ = (Z-K)*S+(K-J)*S := by noncomm_ring
      _ = _ := by rw [hS]
  have hrec : S=R+R*(K-J)*S := by
    calc
      S = (R*(Z-J))*S := by rw [hR₂,one_mul]
      _ = R*((Z-J)*S) := by rw [mul_assoc]
      _ = _ := by rw [hdiff,mul_add,mul_one,mul_assoc]
  have hn : ‖S‖ ≤ ‖R‖+(‖R‖*δ)*‖S‖ := by
    calc
      ‖S‖ = ‖R+R*(K-J)*S‖ := congrArg norm hrec
      _ ≤ ‖R‖+‖R*(K-J)*S‖ := norm_add_le _ _
      _ ≤ ‖R‖+‖R*(K-J)‖*‖S‖ :=
        add_le_add_left (norm_mul_le _ _) _
      _ ≤ ‖R‖+(‖R‖*δ)*‖S‖ := add_le_add_left
        (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left hδ (norm_nonneg _))) (norm_nonneg _)) _
  have h := mul_le_mul_of_nonneg_right hsmall (norm_nonneg S)
  linarith

end M12JacobiResolventWeights
#print axioms M12JacobiResolventWeights.exp_diff_le
#print axioms M12JacobiResolventWeights.cap_nonneg
#print axioms M12JacobiResolventWeights.cap_le
#print axioms M12JacobiResolventWeights.cap_lipschitz
#print axioms M12JacobiResolventWeights.weights_inverse
#print axioms M12JacobiResolventWeights.perturbationCoeff_bound
#print axioms M12JacobiResolventWeights.deltaOp_norm
#print axioms M12JacobiResolventWeights.conjugated_difference
#print axioms M12JacobiResolventWeights.conjugated_norm
#print axioms M12JacobiResolventWeights.similarity_resolvent_bound
