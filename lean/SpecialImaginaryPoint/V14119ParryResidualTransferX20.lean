import Mathlib

/-! Concrete finite residuals for the M14 Parry development through degree
11 in t=x², before division by t. Coefficients are those already audited
in V14119ParryX20 (a is shifted by one degree for log(B(t))/t).
The residual factorization is an exact polynomial identity for all t.
The analytic log-composition remainder still requires a proof. -/
namespace Manuscript14.ParryResidual

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def a : ℕ → ℚ
  | 0 => (1 / 6 : ℚ)
  | 1 => (-1 / 180 : ℚ)
  | 2 => (1 / 2835 : ℚ)
  | 3 => (-1 / 37800 : ℚ)
  | 4 => (1 / 467775 : ℚ)
  | 5 => (-691 / 3831077250 : ℚ)
  | 6 => (2 / 127702575 : ℚ)
  | 7 => (-3617 / 2605132530000 : ℚ)
  | 8 => (43867 / 350813659321125 : ℚ)
  | 9 => (-174611 / 15313294652906250 : ℚ)
  | 10 => (155366 / 147926426347074375 : ℚ)
  | 11 => (-236364091 / 2423034863565078262500 : ℚ)
  | _ => 0

def c : ℕ → ℚ
  | 0 => (0 : ℚ)
  | 1 => (1 / 20 : ℚ)
  | 2 => (-1 / 16800 : ℚ)
  | 3 => (-1 / 756000 : ℚ)
  | 4 => (89 / 3104640000 : ℚ)
  | 5 => (-1579 / 4540536000000 : ℚ)
  | 6 => (5069 / 2288430144000000 : ℚ)
  | 7 => (1013 / 64838854080000000 : ℚ)
  | 8 => (-133302011 / 182129747556556800000000 : ℚ)
  | 9 => (230510617 / 18440636940101376000000000 : ℚ)
  | 10 => (-106522465321 / 857694513680715110400000000000 : ℚ)
  | 11 => (42162599 / 233916685549285939200000000000 : ℚ)
  | _ => 0

def p : ℕ → ℚ
  | 0 => (6 : ℚ)
  | 1 => (1 / 5 : ℚ)
  | 2 => (-19 / 3150 : ℚ)
  | 3 => (31 / 94500 : ℚ)
  | 4 => (-14089 / 654885000 : ℚ)
  | 5 => (132731 / 85135050000 : ℚ)
  | 6 => (-19378097 / 160905244500000 : ℚ)
  | 7 => (798055301 / 82061674695000000 : ℚ)
  | 8 => (-8765082658861 / 10805060707090650000000 : ℚ)
  | 9 => (188905177031 / 2723964884140500000000 : ℚ)
  | 10 => (-369024804546778819 / 61060478561839972215000000000 : ℚ)
  | 11 => (326577481196239877 / 610604785618399722150000000000 : ℚ)
  | _ => 0

def r : ℕ → ℚ
  | 0 => (0 : ℚ)
  | 1 => (-3 / 10 : ℚ)
  | 2 => (-27 / 2800 : ℚ)
  | 3 => (9 / 28000 : ℚ)
  | 4 => (-23 / 1379840 : ℚ)
  | 5 => (121483 / 112112000000 : ℚ)
  | 6 => (-106721 / 1358280000000 : ℚ)
  | 7 => (18232603 / 3001798800000000 : ℚ)
  | 8 => (-74462871059417 / 151774789630464000000000 : ℚ)
  | 9 => (4697904816091 / 114787656023040000000000 : ℚ)
  | 10 => (-3000951506527034377 / 857694513680715110400000000000 : ℚ)
  | 11 => (1238782192338196421 / 4062763485856018944000000000000 : ℚ)
  | _ => 0

def atail : ℕ → ℚ
  | 0 => (-3560975164237866304211 / 76166840958039181340991000000000000 : ℚ)
  | 1 => (35582369561941614187 / 15233368191607836268198200000000000 : ℚ)
  | 2 => (-5951720617583607374551 / 38845088888599982483905410000000000000 : ℚ)
  | 3 => (85669312988549172204703 / 7953531949940846413579632697500000000000 : ℚ)
  | 4 => (-3528452928454288546444991 / 4533513211466282455740390637575000000000000 : ℚ)
  | 5 => (3390130184370950691825823 / 59842374391354928415773156415990000000000000 : ℚ)
  | 6 => (-154185432525581295236267399 / 37700695866553604901937088542073700000000000000 : ℚ)
  | 7 => (368503824584564462374027 / 1280594288945434949114710887978046875000000000 : ℚ)
  | 8 => (-202241473979594549300819 / 10527340774702953971743310951676562500000000000 : ℚ)
  | 9 => (34066950999332476055739809 / 29590333668261260647407872369460095287500000000000 : ℚ)
  | 10 => (-77191189484018831145056807 / 1479516683413063032370393618473004764375000000000000 : ℚ)
  | _ => 0

def ctail : ℕ → ℚ
  | 0 => (-31447811794104399839 / 1165455486236736414720000000000000 : ℚ)
  | 1 => (2155194393349936614253 / 99993391206451438068172800000000000000 : ℚ)
  | 2 => (28613359178509946345623 / 31569342080893954018665984000000000000000 : ℚ)
  | 3 => (-89053873752241482574481 / 5069664934167087910056360960000000000000000 : ℚ)
  | 4 => (1207218477141321828372959243 / 6110400849533221180687492666521600000000000000000 : ℚ)
  | 5 => (-2450158651746146552294604427 / 2383056331317956260468122139943424000000000000000000 : ℚ)
  | 6 => (-404732610383230753317761647 / 29437754680986518511665038199301120000000000000000000 : ℚ)
  | 7 => (21428116475627686784286855313 / 45039764661909373322847508444930713600000000000000000000 : ℚ)
  | 8 => (-3510879711766119234290369891141 / 471341137186881591823599175876199917824000000000000000000000 : ℚ)
  | 9 => (106075010180105489009580380461 / 1571137123956271972745330586253999726080000000000000000000000 : ℚ)
  | 10 => (-13769355382107102241760323 / 142830647632388361158666416932181793280000000000000000000000 : ℚ)
  | _ => 0

noncomputable def eval (f : ℕ → ℚ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (f i : ℝ) * t^i

noncomputable def A12 (t : ℝ) : ℝ := eval a 12 t
noncomputable def P12 (t : ℝ) : ℝ := eval p 12 t
noncomputable def C12 (t : ℝ) : ℝ := eval c 12 t
noncomputable def R12 (t : ℝ) : ℝ := eval r 12 t

theorem reciprocal_residual_exact (t : ℝ) :
    A12 t * P12 t - 1 = t^12 * eval atail 11 t := by
  norm_num [A12, P12, eval, a, p, atail, Finset.sum_range_succ] <;> ring

theorem product_residual_exact (t : ℝ) :
    -(P12 t * C12 t) - R12 t = t^12 * eval ctail 11 t := by
  norm_num [P12, C12, R12, eval, p, c, r, ctail, Finset.sum_range_succ] <;> ring

theorem eval_abs_bound (f : ℕ → ℚ) (n : ℕ) (t : ℝ) (ht : |t| ≤ 1) :
    |eval f n t| ≤ ∑ i ∈ Finset.range n, |(f i : ℝ)| := by
  unfold eval
  calc
    _ ≤ ∑ i ∈ Finset.range n, |(f i : ℝ) * t^i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) ht)

theorem reciprocal_tail_bound (t : ℝ) (ht : |t| ≤ 1) :
    |eval atail 11 t| ≤ 1 := by
  apply (eval_abs_bound atail 11 t ht).trans
  norm_num [atail, Finset.sum_range_succ]

theorem product_tail_bound (t : ℝ) (ht : |t| ≤ 1) :
    |eval ctail 11 t| ≤ 1 := by
  apply (eval_abs_bound ctail 11 t ht).trans
  norm_num [ctail, Finset.sum_range_succ]

theorem p_bound (t : ℝ) (ht : |t| ≤ 1) : |P12 t| ≤ 7 := by
  unfold P12
  apply (eval_abs_bound p 12 t ht).trans
  norm_num [p, Finset.sum_range_succ]

theorem c_bound (t : ℝ) (ht : |t| ≤ 1) : |C12 t| ≤ 1 := by
  unfold C12
  apply (eval_abs_bound c 12 t ht).trans
  norm_num [c, Finset.sum_range_succ]

theorem reciprocal_residual_bound (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |A12 t * P12 t - 1| ≤ t^12 := by
  rw [reciprocal_residual_exact, abs_mul, abs_of_nonneg (pow_nonneg ht _)]
  have habs : |t| ≤ 1 := by rwa [abs_of_nonneg ht]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (reciprocal_tail_bound t habs) (pow_nonneg ht 12)

theorem product_residual_bound (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |-(P12 t * C12 t) - R12 t| ≤ t^12 := by
  rw [product_residual_exact, abs_mul, abs_of_nonneg (pow_nonneg ht _)]
  have habs : |t| ≤ 1 := by rwa [abs_of_nonneg ht]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (product_tail_bound t habs) (pow_nonneg ht 12)

/-- Reciprocal stability from a uniform denominator bound and the
actual finite polynomial residual. -/
theorem inverse_transfer (d a p e K M c : ℝ)
    (hc : 0 < c) (hd : c ≤ |d|) (he : 0 ≤ e) (hK : 0 ≤ K)
    (hda : |d-a| ≤ K*e) (hp : |p| ≤ M) (hr : |a*p-1| ≤ e) :
    |1/d-p| ≤ ((K*M+1)/c)*e := by
  have hdn : d ≠ 0 := by
    intro h
    rw [h, abs_zero] at hd
    linarith
  have hM : 0 ≤ M := (abs_nonneg p).trans hp
  have h1 : |(d-a)*p| ≤ K*e*M := by
    rw [abs_mul]
    exact mul_le_mul hda hp (abs_nonneg _) (by positivity)
  have hn : |1-d*p| ≤ (K*M+1)*e := by
    have hsplit : 1-d*p = -(a*p-1) - (d-a)*p := by ring
    rw [hsplit]
    calc
      _ ≤ |-(a*p-1)| + |(d-a)*p| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (-(a*p-1)) (-((d-a)*p))
      _ ≤ e + K*e*M := by rw [abs_neg]; exact add_le_add hr h1
      _ = _ := by ring
  have hs : 1/d-p = (1-d*p)/d := by field_simp [hdn] <;> ring
  rw [hs, abs_div]
  calc
    _ ≤ (K*M+1)*e/|d| := div_le_div_of_nonneg_right hn (abs_nonneg _)
    _ ≤ (K*M+1)*e/c := div_le_div_of_nonneg_left (by positivity) hc hd
    _ = _ := by ring

theorem parry_inverse_bound (t d K : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hK : 0 ≤ K) (hd : (1:ℝ)/12 ≤ |d|)
    (hda : |d-A12 t| ≤ K*t^12) :
    |1/d-P12 t| ≤ (84*K+12)*t^12 := by
  have habs : |t| ≤ 1 := by rwa [abs_of_nonneg ht]
  have h := inverse_transfer d (A12 t) (P12 t) (t^12) K 7 (1/12)
    (by norm_num) hd (pow_nonneg ht _) hK hda (p_bound t habs)
    (reciprocal_residual_bound t ht ht1)
  convert h using 1 <;> ring

/-- Product stability for the actual reciprocal times the normalized
logarithm, with the finite residual of its degree-11 polynomial. -/
theorem product_transfer (P C p c r e KP KC M N : ℝ)
    (he : 0 ≤ e) (hKP : 0 ≤ KP) (hKC : 0 ≤ KC)
    (hP : |P-p| ≤ KP*e) (hC : |C-c| ≤ KC*e)
    (hM : |P| ≤ M) (hN : |c| ≤ N)
    (hr : |-(p*c)-r| ≤ e) :
    |-(P*C)-r| ≤ (KP*N+KC*M+1)*e := by
  have h1 : |(P-p)*c| ≤ KP*e*N := by
    rw [abs_mul]
    exact mul_le_mul hP hN (abs_nonneg _) (by positivity)
  have h2 : |(C-c)*P| ≤ KC*e*M := by
    rw [abs_mul]
    exact mul_le_mul hC hM (abs_nonneg _) (by positivity)
  have hs : -(P*C)-r = (-(p*c)-r) - ((P-p)*c + (C-c)*P) := by ring
  rw [hs]
  calc
    _ ≤ |-(p*c)-r| + |(P-p)*c+(C-c)*P| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (-(p*c)-r) (-((P-p)*c+(C-c)*P))
    _ ≤ e + (|(P-p)*c|+|(C-c)*P|) := add_le_add hr (abs_add_le _ _)
    _ ≤ e + (KP*e*N+KC*e*M) := add_le_add_left (add_le_add h1 h2) _
    _ = _ := by ring

#print axioms reciprocal_residual_exact
#print axioms product_residual_exact
#print axioms eval_abs_bound
#print axioms reciprocal_tail_bound
#print axioms product_tail_bound
#print axioms p_bound
#print axioms c_bound
#print axioms reciprocal_residual_bound
#print axioms product_residual_bound
#print axioms inverse_transfer
#print axioms parry_inverse_bound
#print axioms product_transfer
end Manuscript14.ParryResidual
