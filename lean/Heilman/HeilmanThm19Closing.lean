/-
  Closing step of the certification of Heilman's 2D graph-threshold improvement
  K_G ≤ K_Kr − 10⁻⁵ of Heilman's Theorem 1.9 (numerics/heilman_thm19).

  Core Lean 4 only: no Mathlib, no `native_decide`. Every theorem is an inequality between
  nonnegative rationals, encoded as (numerator, denominator) pairs and checked by the kernel
  with `decide +kernel`. numerics/heilman_thm19/closing.py generates this file and re-evaluates
  every statement with Python Fractions.

  Inputs (rigorous, from Arb ball arithmetic; see numerics/heilman_thm19/README.md):
    bU n, bL n : upper and lower bounds of |b_n| (odd n ≤ 199), b_n = [wⁿ] H⁻¹(w), × 10⁻⁴⁰
    Psup       : upper bound of sup_{|ζ|=51/50} |Σ_{j≤200} φ_j ζ^j|, × 10⁻¹⁵   (certify.c)
    M'         : sup_{|ζ|=11/10} |E(sin ζ)| ≤ 230769761746·10⁻¹⁰                    (mbound.c)
    π ∈ (3.14159265358979323846, 3.14159265358979323847)   (Mathlib Real.pi_gt_d20, Real.pi_lt_d20)
  Proved here from these: asinh 1 = log(1 + √2) ∈ (L_lo, L_hi) by exp-series bounds,
  sinh(51/50) ≤ sh_up by its series, and the closing inequalities.
-/
namespace HeilmanThm19

/-- A nonnegative rational as a (numerator, denominator) pair. -/
structure Q where
  num : Nat
  den : Nat

def Q.Lt (a b : Q) : Prop := a.num * b.den < b.num * a.den
def Q.Le (a b : Q) : Prop := a.num * b.den ≤ b.num * a.den
def Q.Eq (a b : Q) : Prop := a.num * b.den = b.num * a.den

instance (a b : Q) : Decidable (Q.Lt a b) := Nat.decLt _ _
instance (a b : Q) : Decidable (Q.Le a b) := Nat.decLe _ _
instance (a b : Q) : Decidable (Q.Eq a b) := Nat.decEq _ _

instance : Add Q := ⟨fun a b => ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩⟩
instance : Mul Q := ⟨fun a b => ⟨a.num * b.num, a.den * b.den⟩⟩
instance : Div Q := ⟨fun a b => ⟨a.num * b.den, a.den * b.num⟩⟩
instance : HPow Q Nat Q := ⟨fun a k => ⟨a.num ^ k, a.den ^ k⟩⟩
instance {n : Nat} : OfNat Q n := ⟨⟨n, 1⟩⟩

def fr (a b : Nat) : Q := ⟨a, b⟩
/-- `dec m e` is m · 10^(−e). -/
def dec (m e : Nat) : Q := ⟨m, 10 ^ e⟩

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Σ_{k=1}^{K} x^k / k!  (so exp x − 1 ≥ this for x ≥ 0). -/
def expm1Lo (x : Q) : Nat → Q
  | 0 => 0
  | k + 1 => expm1Lo x k + x ^ (k + 1) / fr (fact (k + 1)) 1

/-- Σ_{k=0}^{K} x^(2k+1) / (2k+1)!. -/
def sinhPart (x : Q) : Nat → Q
  | 0 => x
  | k + 1 => sinhPart x k + x ^ (2 * k + 3) / fr (fact (2 * k + 3)) 1

/-- Horner evaluation c₀ + y(c₁ + y(c₂ + …)) of coefficients given as m · 10⁻⁴⁰. -/
def horner (y : Q) : List Nat → Q
  | [] => 0
  | c :: cs => dec c 40 + y * horner y cs

/-! ### Inputs -/

def πlo : Q := dec 314159265358979323846 20
def πhi : Q := dec 314159265358979323847 20
def Lhi : Q := dec 88137358701954302524 20
def Llo : Q := dec 88137358701954302523 20
def ε : Q := fr 1 100000
def s : Q := fr 51 50
def ρ' : Q := fr 11 10
def Mp : Q := fr 231 10
def Mp_in : Q := dec 230769761746 10
def Psup : Q := dec 5064404904261 15
/-- Upper bounds of |b_n|, n = 1, 3, …, 199, × 10⁻⁴⁰. -/
def bU : List Nat := [10019585747212779408461474874477678319457, 1650881789287621994386486214446490952780, 72481098105396004252206702801453358877, 1336596098642156295521380, 202145145577525845641551028143171782, 26098067453106680294608209857902337, 2817266918023114582895682200497801, 3103353516715643483913149071114433, 53980787995816985526955740777389, 253789149203513217069911455015721, 16929533580243587271773324624247, 33410544262208561622929182776800, 8416058034735025355692428653078, 6248115723146382559937577932764, 2384239035183509147606627748900, 1088193791934913840823169452898, 368161462244745780412835726664, 59785317866350069094593397196, 21000136273429176667823597454, 41124053065105563783514802709, 23246577398509095696221384495, 11184660970300889204256685140, 1694626474863482584989551790, 926149404594242298917648597, 1411054578967079150785997639, 674601331333818649783926336, 171879719766017245594293006, 83352283513826511483654003, 92619832282226461015446740, 44719771195476327308356312, 1922972370549058944852608, 10175712669142046652645431, 7340856924855253438655386, 1465908227047346245500379, 1117822194916018794204641, 1103835510267468856628516, 294149466679586301395679, 147570094144721471950417, 167808875629987593963110, 44513004767656307679657, 25540249088294091446722, 26090584173693668268840, 5128397063906339419819, 5226842872093203720632, 3962749779015802107939, 223981124713809130331, 1081670484089769409909, 531086074176606318130, 104814590185481087074, 202166832613947618021, 48011214592574547110, 42924213940194176094, 30514446102832384941, 2026590259384714254, 10020846240688465527, 2793502586076149829, 2142984941593519135, 1544913094643288997, 177643025535863525, 528991251925441978, 100011143849413668, 134972818884169425, 67946849544870091, 23736774975807455, 27159891944055356, 622776383709983, 8588406903527766, 1797832775935954, 2274018396420088, 1052095957606321, 494381955087587, 430481125851364, 76604428443737, 152796267737001, 11676421105457, 55455613620469, 21514883524760, 32531291660169, 29495841346261, 31502635960169, 36722704589747, 44795833516955, 56665938033489, 71598502883339, 108652653016675, 137636428497437, 155742153383589, 193108750963770, 244310596428157, 311385274804897, 397951847743840, 604858876971356, 768872991570078, 870869511648563, 1081456758179789, 1369482765118754, 1747374437305390, 2235267850627102, 3400086040696332, 4326919939861528]
/-- Lower bounds of |b_n|, n = 1, 3, …, 199, × 10⁻⁴⁰. -/
def bL : List Nat := [10019585747212779408461474874477677742534, 1650881789287621994386486214446490308542, 72481098105396004252206702801452547705, 1336596098642156294525910, 202145145577525845641551028141973731, 26098067453106680294608209856435275, 2817266918023114582895682198696859, 3103353516715643483913149068670330, 53980787995816985526955737806676, 253789149203513217069911451625796, 16929533580243587271773320470752, 33410544262208561622929177705334, 8416058034735025355692422445185, 6248115723146382559937570287933, 2384239035183509147606616794861, 1088193791934913840823155905995, 368161462244745780412820297309, 59785317866350069094574237099, 21000136273429176667799674892, 41124053065105563783484930244, 23246577398509095696184128005, 11184660970300889204202519930, 1694626474863482584922828212, 926149404594242298843330224, 1411054578967079150695170128, 674601331333818649671091011, 171879719766017245452840978, 83352283513826511305153140, 92619832282226460748758085, 44719771195476326971799574, 1922972370549058559660859, 10175712669142046169110939, 7340856924855252823173753, 1465908227047345460499807, 1117822194916017795821257, 1103835510267467372401343, 294149466679584441618430, 147570094144719383703710, 167808875629985027484297, 44513004767653100059008, 25540249088290052803229, 26090584173688567685591, 5128397063898703416122, 5226842872083626366247, 3962749779005048497634, 223981124700555294282, 1081670484073124855812, 531086074155540864529, 104814590158743107137, 202166832573639965988, 48011214541778780837, 42924213882973389917, 30514446032109417516, 2026590170286844301, 10020846127539555446, 2793502441871819076, 2142984723016448542, 1544912817083829156, 177642709391113444, 528990855827722169, 100010636747305507, 134972163930244816, 67946001666842826, 23735484879974366, 27158239690146363, 620885696326430, 8586049027123541, 1794848952215505, 2270225217198071, 1047270355058608, 487123269377250, 421307612676323, 66262782566488, 140015053008808, 0, 35026213769460, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def gup : Q := dec 88137853243318705709 20
def shup : Q := dec 1206299911895610 15
def δr : Q := dec 5145803983 12
def Rp : Q := dec 1014854195917 12
def RmG : Q := dec 13347566348381294291 20
def A1r : Q := dec 99999964721673050645 20
def T1r : Q := dec 449758108 20
def glo : Q := dec 881378782868385 15
def ghi : Q := dec 881378782880307 15
def RmGlo : Q := dec 133475413048615 15
def A2r : Q := dec 99999999998975547571 20
def T2r : Q := dec 449784640 20
def Kb : Q := dec 1782203471795465 15
def εlo : Q := dec 10506395904 15
def εhi : Q := dec 10506420012 15

/-! ### Constants -/

/-- exp(L_hi) − 1 > √2, hence L_hi > log(1 + √2) = asinh 1. -/
theorem Lhi_gt : Q.Lt 2 (expm1Lo Lhi 40 ^ 2) := by decide +kernel
/-- exp(L_lo) − 1 ≤ T₄₀ + 2 L_lo⁴¹/41! < √2, hence L_lo < asinh 1. -/
theorem Llo_lt : Q.Lt ((expm1Lo Llo 40 + fr 2 1 * Llo ^ 41 / fr (fact 41) 1) ^ 2) 2 := by decide +kernel
/-- γ_t = πL/(π − 2εL) ≤ g_up (γ_t increases in L and decreases in π). -/
theorem gamma_le : Q.Le (πlo * Lhi + 2 * ε * Lhi * gup) (gup * πlo) := by decide +kernel
/-- sinh(51/50) ≤ sh_up: partial sum to k = 15 plus 2·s³³/33! bounds the tail. -/
theorem sinh_le : Q.Le (sinhPart s 15 + fr 2 1 * s ^ 33 / fr (fact 33) 1) shup := by decide +kernel
theorem Mp_ge : Q.Le Mp_in Mp := by decide +kernel

/-! ### Rouché radius -/

/-- δ = Psup + M'(s/ρ')²⁰¹/(1 − s/ρ') ≤ δ_r, with s/ρ' = 51/55 and 1 − s/ρ' = 4/55. -/
theorem delta_le : Q.Le (Psup + Mp * fr 51 55 ^ 201 * fr 55 4) δr := by decide +kernel
theorem Rp_le : Q.Le (Rp + δr + dec 1 10) s := by decide +kernel
theorem RmG_eq : Q.Eq (RmG + gup) Rp := by decide +kernel

/-! ### Main inequality: A(γ_t) < 1 -/

/-- A_N(g_up) = g_up · Σ |b_{2i+1}| (g_up²)^i ≤ A1r. -/
theorem A_le : Q.Le (gup * horner (gup * gup) bU) A1r := by decide +kernel
/-- Σ_{n>200} |b_n| g_upⁿ ≤ sinh(s) q²⁰¹/(1 − q) = sh_up g_up²⁰¹/(R'²⁰⁰ (R' − g_up)) ≤ T1r. -/
theorem tail_le : Q.Le (shup * gup ^ 201 / (Rp ^ 200 * RmG)) T1r := by decide +kernel
theorem main : Q.Lt (A1r + T1r) 1 := by decide +kernel

/-! ### Existence of the root c* of A(c) = 1 (not needed for the bound) -/

theorem root_exists : Q.Lt (fr 9 10) Rp ∧ Q.Lt 1 (fr 9 10 * horner (fr 81 100) bL) := by decide +kernel

/-! ### Two-sided enclosure: g_lo < c* < g_hi -/

theorem RmGlo_eq : Q.Eq (RmGlo + glo) Rp := by decide +kernel
theorem A_lo_le : Q.Le (glo * horner (glo * glo) bU) A2r := by decide +kernel
theorem tail_lo_le : Q.Le (shup * glo ^ 201 / (Rp ^ 200 * RmGlo)) T2r := by decide +kernel
theorem best : Q.Lt (A2r + T2r) 1 := by decide +kernel
theorem above : Q.Lt 1 (ghi * horner (ghi * ghi) bL) := by decide +kernel
/-- K_G ≤ π/(2 g_lo) ≤ Kb. -/
theorem Kb_ge : Q.Le πhi (2 * glo * Kb) := by decide +kernel
/-- Kb + ε_lo ≤ π/(2 L_hi) ≤ K_Kr. -/
theorem eps_lo_le : Q.Le (2 * Lhi * (Kb + εlo)) πlo := by decide +kernel
/-- K_Kr − π/(2 g_hi) ≤ π_hi/(2 L_lo) − π_lo/(2 g_hi) ≤ ε_hi. -/
theorem eps_hi_ge : Q.Le (πhi / (2 * Llo)) (εhi + πlo / (2 * ghi)) := by decide +kernel

end HeilmanThm19

#print axioms HeilmanThm19.Lhi_gt
#print axioms HeilmanThm19.Llo_lt
#print axioms HeilmanThm19.gamma_le
#print axioms HeilmanThm19.sinh_le
#print axioms HeilmanThm19.Mp_ge
#print axioms HeilmanThm19.delta_le
#print axioms HeilmanThm19.Rp_le
#print axioms HeilmanThm19.RmG_eq
#print axioms HeilmanThm19.A_le
#print axioms HeilmanThm19.tail_le
#print axioms HeilmanThm19.main
#print axioms HeilmanThm19.root_exists
#print axioms HeilmanThm19.RmGlo_eq
#print axioms HeilmanThm19.A_lo_le
#print axioms HeilmanThm19.tail_lo_le
#print axioms HeilmanThm19.best
#print axioms HeilmanThm19.above
#print axioms HeilmanThm19.Kb_ge
#print axioms HeilmanThm19.eps_lo_le
#print axioms HeilmanThm19.eps_hi_ge
