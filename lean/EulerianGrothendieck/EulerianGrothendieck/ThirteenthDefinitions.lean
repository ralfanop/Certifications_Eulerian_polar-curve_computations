import EulerianGrothendieck.TwelfthOrderAsymptotics
noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck.Order13
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/- Exact order-13 extensions. The existing order-12 objects are preserved. -/
def cumulantA (r : ℕ) : ℚ := if r = 14 then (-3392780147 / 826385373016328125 : ℚ) else EulerianGrothendieck.cumulantA r

def normB (r : ℕ) : ℚ := if r = 13 then (-4616262989193398646053131685642539702222239 / 321060846356728692762315063296000000000 : ℚ) else EulerianGrothendieck.normB r

def vacuumD (r : ℕ) : ℚ := if r = 13 then (3755578647916406093110902261201557206665981187187019 / 262930572830524260427935180170199040000000000000 : ℚ) else EulerianGrothendieck.vacuumD r

def pCoeff (r q : ℕ) : ℚ := if r = 13 then (match q with
  | 14 => (-3392780147 / 826385373016328125 : ℚ)
  | 15 => (-6173411051779 / 2369731297242684375000 : ℚ)
  | 16 => (-649843265151137 / 1011085353490212000000000 : ℚ)
  | 17 => (-54684268386353 / 649983441529422000000000 : ℚ)
  | 18 => (-4819224764768629 / 725104057459541760000000000 : ℚ)
  | 19 => (-78764634257 / 232405146621648000000000 : ℚ)
  | 20 => (-4891237960963 / 422732729854955520000000000 : ℚ)
  | 21 => (-1315661 / 4893079726080000000000 : ℚ)
  | 22 => (-792557 / 186403037184000000000000 : ℚ)
  | 23 => (-14159 / 315451293696000000000000 : ℚ)
  | 24 => (-989 / 3277416038400000000000000 : ℚ)
  | 25 => (-1 / 858370867200000000000000 : ℚ)
  | 26 => (-1 / 510117543936000000000000000 : ℚ)
  | _ => 0) else EulerianGrothendieck.pCoeff r q

def qFallingCoeff (r q : ℕ) : ℚ := if r = 13 then (match q with
  | 8 => (-816289652736 / 547969296875 : ℚ)
  | 9 => (-1960468325380947968 / 78054390554765625 : ℚ)
  | 10 => (-33079535091871560704 / 286199432034140625 : ℚ)
  | 11 => (-205219212272078769883136 / 888649236466006640625 : ℚ)
  | 12 => (-478736150376306625352224 / 1948792185232470703125 : ℚ)
  | 13 => (-202228497225066536689490176 / 1295946803179593017578125 : ℚ)
  | 14 => (-2760010296300228404882363128 / 43364373798701766357421875 : ℚ)
  | 15 => (-1020710378158667876476245952 / 58317606143081685791015625 : ℚ)
  | 16 => (-195744988465128353831331328 / 58317606143081685791015625 : ℚ)
  | 17 => (-80377711357752997456648288 / 174952818429245057373046875 : ℚ)
  | 18 => (-6301372855536914365048 / 138302623264225341796875 : ℚ)
  | 19 => (-877766062148021331968 / 265966583200433349609375 : ℚ)
  | 20 => (-22025045475754748512 / 125984170989678955078125 : ℚ)
  | 21 => (-8636662932416 / 1283261227294921875 : ℚ)
  | 22 => (-283122387784 / 1527691937255859375 : ℚ)
  | 23 => (-416195008 / 117514764404296875 : ℚ)
  | 24 => (-3730688 / 83939117431640625 : ℚ)
  | 25 => (-1312 / 3997100830078125 : ℚ)
  | 26 => (-8 / 7423187255859375 : ℚ)
  | _ => 0) else EulerianGrothendieck.qFallingCoeff r q

def gPolynomial (r : ℕ) (x : ℚ) : ℚ :=
  ∑ q ∈ range (2*r+1), pCoeff r q*2^q*fallingPoly q x
def qPolynomial (r : ℕ) (x : ℚ) : ℚ :=
  ∑ q ∈ range (2*r+1), qFallingCoeff r q*fallingPoly q x
def exactMomentPolynomial (r : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ range (2*r+1), (pCoeff r q:ℝ)*2^q*fallingReal q x
def exactSquaredPolynomial (r : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ range (2*r+1), (qFallingCoeff r q:ℝ)*fallingReal q x

theorem cumulantA_prefix (r : ℕ) (hr : r ≤ 13) : cumulantA r = EulerianGrothendieck.cumulantA r := by
  simp [cumulantA, show r ≠ 14 by omega]
theorem normB_prefix (r : ℕ) (hr : r ≤ 12) : normB r = EulerianGrothendieck.normB r := by
  simp [normB, show r ≠ 13 by omega]
theorem vacuumD_prefix (r : ℕ) (hr : r ≤ 12) : vacuumD r = EulerianGrothendieck.vacuumD r := by
  simp [vacuumD, show r ≠ 13 by omega]
theorem pCoeff_prefix (r q : ℕ) (hr : r ≤ 12) : pCoeff r q = EulerianGrothendieck.pCoeff r q := by
  simp [pCoeff, show r ≠ 13 by omega]
theorem qFallingCoeff_prefix (r q : ℕ) (hr : r ≤ 12) : qFallingCoeff r q = EulerianGrothendieck.qFallingCoeff r q := by
  simp [qFallingCoeff, show r ≠ 13 by omega]
theorem gPolynomial_prefix (r : ℕ) (hr : r ≤ 12) (x : ℚ) :
    gPolynomial r x = EulerianGrothendieck.gPolynomial r x := by
  simp only [gPolynomial, EulerianGrothendieck.gPolynomial, pCoeff_prefix r _ hr]
theorem qPolynomial_prefix (r : ℕ) (hr : r ≤ 12) (x : ℚ) :
    qPolynomial r x = EulerianGrothendieck.qPolynomial r x := by
  simp only [qPolynomial, EulerianGrothendieck.qPolynomial, qFallingCoeff_prefix r _ hr]
theorem exactMomentPolynomial_prefix (r : ℕ) (hr : r ≤ 12) (x : ℝ) :
    exactMomentPolynomial r x = EulerianGrothendieck.exactMomentPolynomial r x := by
  simp only [exactMomentPolynomial, EulerianGrothendieck.exactMomentPolynomial, pCoeff_prefix r _ hr]
theorem exactSquaredPolynomial_prefix (r : ℕ) (hr : r ≤ 12) (x : ℝ) :
    exactSquaredPolynomial r x = EulerianGrothendieck.exactSquaredPolynomial r x := by
  simp only [exactSquaredPolynomial, EulerianGrothendieck.exactSquaredPolynomial, qFallingCoeff_prefix r _ hr]
theorem exactMomentPolynomial_rat (r : ℕ) (x : ℚ) :
    exactMomentPolynomial r (x:ℝ) = (gPolynomial r x:ℝ) := by
  simp [exactMomentPolynomial, gPolynomial, fallingReal_rat]
theorem exactSquaredPolynomial_rat (r : ℕ) (x : ℚ) :
    exactSquaredPolynomial r (x:ℝ) = (qPolynomial r x:ℝ) := by
  simp [exactSquaredPolynomial, qPolynomial, fallingReal_rat]
end EulerianGrothendieck.Order13
