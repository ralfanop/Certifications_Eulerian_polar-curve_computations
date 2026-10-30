import EulerianGrothendieck.FiniteSeries
import Mathlib.Tactic.IntervalCases

open scoped BigOperators
namespace EulerianGrothendieck
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/- Tables are certificates, not assumptions. The theorems below verify the
logarithm recurrence, P recurrence, G-square polynomial identities, exact
negative-binomial factorial functional, and reciprocal recurrence. The bridge
to the analytic law and all-order remainder is not asserted here. -/

def cumulantA : ℕ → ℚ
  | 0 => 0
  | 1 => (1 / 2 : ℚ)
  | 2 => (-1 / 20 : ℚ)
  | 3 => (1 / 105 : ℚ)
  | 4 => (-3 / 1400 : ℚ)
  | 5 => (1 / 1925 : ℚ)
  | 6 => (-691 / 5255250 : ℚ)
  | 7 => (6 / 175175 : ℚ)
  | 8 => (-10851 / 1191190000 : ℚ)
  | 9 => (43867 / 17823180375 : ℚ)
  | 10 => (-523833 / 777995968750 : ℚ)
  | 11 => (466098 / 2505147019375 : ℚ)
  | 12 => (-236364091 / 4559367575262500 : ℚ)
  | 13 => (11842758 / 814172781296875 : ℚ)
  | _ => 0

def normB : ℕ → ℚ
  | 0 => 1
  | 1 => (-3 / 160 : ℚ)
  | 2 => (5359 / 358400 : ℚ)
  | 3 => (-209763 / 11468800 : ℚ)
  | 4 => (18304223653 / 565182464000 : ℚ)
  | 5 => (-1786398921783 / 23991418880000 : ℚ)
  | 6 => (79531817948593847 / 376185448038400000 : ℚ)
  | 7 => (-56280274721300027631 / 78709570666496000000 : ℚ)
  | 8 => (1076266149215630230688843827 / 383226195073558380544000000 : ℚ)
  | 9 => (-70054628088255462752258859219 / 5574199201069940080640000000 : ℚ)
  | 10 => (33671794122508440258254808579407783 / 533339379558371866915635200000000 : ℚ)
  | 11 => (-2309572333352867518505748532774538043 / 6564176979179961438961664000000000 : ℚ)
  | 12 => (696911723598817980630533279129599184493743 / 323482641533988499712030801920000000000 : ℚ)
  | _ => 0

def vacuumD : ℕ → ℚ
  | 0 => 1
  | 1 => (3 / 160 : ℚ)
  | 2 => (-5233 / 358400 : ℚ)
  | 3 => (1017039 / 57344000 : ℚ)
  | 4 => (-17799061787 / 565182464000 : ℚ)
  | 5 => (427499109559779 / 5877897625600000 : ℚ)
  | 6 => (-2730579484573927387 / 13166490681344000000 : ℚ)
  | 7 => (25207220482913705795241 / 35812854653255680000000 : ℚ)
  | 8 => (-14300092547231958496460867439 / 5158814164451747430400000000 : ℚ)
  | 9 => (410387950138926644667173211411 / 33016410652491183554560000000 : ℚ)
  | 10 => (-9172402090182778513449682135461516347 / 146668329378552263401799680000000000 : ℚ)
  | 11 => (401241974740424387700995518764021887881341 / 1149879702327849745070109491200000000000 : ℚ)
  | 12 => (-121187694084522852063530193410645082164333996727 / 56666071730716435437054995726336000000000000 : ℚ)
  | _ => 0

def pCoeff : ℕ → ℕ → ℚ
  | 0 => fun q => match q with
    | 0 => 1
    | _ => 0
  | 1 => fun q => match q with
    | 2 => (-1 / 20 : ℚ)
    | _ => 0
  | 2 => fun q => match q with
    | 3 => (1 / 105 : ℚ)
    | 4 => (1 / 800 : ℚ)
    | _ => 0
  | 3 => fun q => match q with
    | 4 => (-3 / 1400 : ℚ)
    | 5 => (-1 / 2100 : ℚ)
    | 6 => (-1 / 48000 : ℚ)
    | _ => 0
  | 4 => fun q => match q with
    | 5 => (1 / 1925 : ℚ)
    | 6 => (269 / 1764000 : ℚ)
    | 7 => (1 / 84000 : ℚ)
    | 8 => (1 / 3840000 : ℚ)
    | _ => 0
  | 5 => fun q => match q with
    | 6 => (-691 / 5255250 : ℚ)
    | 7 => (-1 / 21560 : ℚ)
    | 8 => (-349 / 70560000 : ℚ)
    | 9 => (-1 / 5040000 : ℚ)
    | 10 => (-1 / 384000000 : ℚ)
    | _ => 0
  | 6 => fun q => match q with
    | 7 => (6 / 175175 : ℚ)
    | 8 => (23237 / 1681680000 : ℚ)
    | 9 => (5543 / 3056130000 : ℚ)
    | 10 => (143 / 1411200000 : ℚ)
    | 11 => (1 / 403200000 : ℚ)
    | 12 => (1 / 46080000000 : ℚ)
    | _ => 0
  | 7 => fun q => match q with
    | 8 => (-10851 / 1191190000 : ℚ)
    | 9 => (-9001 / 2207205000 : ℚ)
    | 10 => (-146843 / 235435200000 : ℚ)
    | 11 => (-10643 / 244490400000 : ℚ)
    | 12 => (-509 / 338688000000 : ℚ)
    | 13 => (-1 / 40320000000 : ℚ)
    | 14 => (-1 / 6451200000000 : ℚ)
    | _ => 0
  | 8 => fun q => match q with
    | 9 => (43867 / 17823180375 : ℚ)
    | 10 => (62809 / 52412360000 : ℚ)
    | 11 => (17 / 82320000 : ℚ)
    | 12 => (90749797 / 5339670336000000 : ℚ)
    | 13 => (7241 / 9779616000000 : ℚ)
    | 14 => (589 / 33868800000000 : ℚ)
    | 15 => (1 / 4838400000000 : ℚ)
    | 16 => (1 / 1032192000000000 : ℚ)
    | _ => 0
  | 9 => fun q => match q with
    | 10 => (-523833 / 777995968750 : ℚ)
    | 11 => (-1621577 / 4613058450000 : ℚ)
    | 12 => (-370206979 / 5547324182400000 : ℚ)
    | 13 => (-463523 / 74162088000000 : ℚ)
    | 14 => (-6915119 / 21358681344000000 : ℚ)
    | 15 => (-56723 / 5867769600000000 : ℚ)
    | 16 => (-223 / 1354752000000000 : ℚ)
    | 17 => (-1 / 677376000000000 : ℚ)
    | 18 => (-1 / 185794560000000000 : ℚ)
    | _ => 0
  | 10 => fun q => match q with
    | 11 => (466098 / 2505147019375 : ℚ)
    | 12 => (441301082837 / 4281840853290000000 : ℚ)
    | 13 => (465818341 / 21958158222000000 : ℚ)
    | 14 => (3673793561 / 1664197254720000000 : ℚ)
    | 15 => (73480541 / 560665385280000000 : ℚ)
    | 16 => (199994803 / 42717362688000000000 : ℚ)
    | 17 => (299 / 2933884800000000 : ℚ)
    | 18 => (107 / 81285120000000000 : ℚ)
    | 19 => (1 / 108380160000000000 : ℚ)
    | 20 => (1 / 37158912000000000000 : ℚ)
    | _ => 0
  | 11 => fun q => match q with
    | 12 => (-236364091 / 4559367575262500 : ℚ)
    | 13 => (-41342265857 / 1367810272578750000 : ℚ)
    | 14 => (-570787478291 / 85636817065800000000 : ℚ)
    | 15 => (-125765325701 / 166003676158320000000 : ℚ)
    | 16 => (-11715871309 / 232987615660800000000 : ℚ)
    | 17 => (-11604877 / 5606653852800000000 : ℚ)
    | 18 => (-138828733 / 2563041761280000000000 : ℚ)
    | 19 => (-4217 / 4694215680000000000 : ℚ)
    | 20 => (-829 / 91039334400000000000 : ℚ)
    | 21 => (-1 / 19508428800000000000 : ℚ)
    | 22 => (-1 / 8174960640000000000000 : ℚ)
    | _ => 0
  | 12 => fun q => match q with
    | 13 => (11842758 / 814172781296875 : ℚ)
    | 14 => (27997256387 / 3156485244412500000 : ℚ)
    | 15 => (33740154126223 / 16249586038235550000000 : ℚ)
    | 16 => (16274865172723 / 63942156742464000000000 : ℚ)
    | 17 => (3080013323 / 166003676158320000000 : ℚ)
    | 18 => (5666314844123 / 6605198903983680000000000 : ℚ)
    | 19 => (116512007 / 4485323082240000000000 : ℚ)
    | 20 => (53302967 / 102521670451200000000000 : ℚ)
    | 21 => (1093 / 160944537600000000000 : ℚ)
    | 22 => (101 / 1820786688000000000000 : ℚ)
    | 23 => (1 / 3901685760000000000000 : ℚ)
    | 24 => (1 / 1961990553600000000000000 : ℚ)
    | _ => 0
  | _ => fun _ => 0

def qFallingCoeff : ℕ → ℕ → ℚ
  | 0 => fun q => match q with
    | 0 => 1
    | _ => 0
  | 1 => fun q => match q with
    | 2 => (-2 / 5 : ℚ)
    | _ => 0
  | 2 => fun q => match q with
    | 2 => (2 / 25 : ℚ)
    | 3 => (164 / 525 : ℚ)
    | 4 => (2 / 25 : ℚ)
    | _ => 0
  | 3 => fun q => match q with
    | 3 => (-32 / 175 : ℚ)
    | 4 => (-304 / 875 : ℚ)
    | 5 => (-328 / 2625 : ℚ)
    | 6 => (-4 / 375 : ℚ)
    | _ => 0
  | 4 => fun q => match q with
    | 3 => (128 / 3675 : ℚ)
    | 4 => (10774 / 30625 : ℚ)
    | 5 => (470168 / 1010625 : ℚ)
    | 6 => (49988 / 275625 : ℚ)
    | 7 => (328 / 13125 : ℚ)
    | 8 => (2 / 1875 : ℚ)
    | _ => 0
  | 5 => fun q => match q with
    | 4 => (-4848 / 30625 : ℚ)
    | 5 => (-672256 / 1010625 : ℚ)
    | 6 => (-825388 / 1194375 : ℚ)
    | 7 => (-272864 / 1010625 : ℚ)
    | 8 => (-62848 / 1378125 : ℚ)
    | 9 => (-656 / 196875 : ℚ)
    | 10 => (-4 / 46875 : ℚ)
    | _ => 0
  | 6 => fun q => match q with
    | 4 => (864 / 30625 : ℚ)
    | 5 => (503168 / 1010625 : ℚ)
    | 6 => (1751604964 / 1379503125 : ℚ)
    | 7 => (15273576 / 13934375 : ℚ)
    | 8 => (574706596 / 1379503125 : ℚ)
    | 9 => (371563568 / 4775203125 : ℚ)
    | 10 => (50668 / 6890625 : ℚ)
    | 11 => (328 / 984375 : ℚ)
    | 12 => (4 / 703125 : ℚ)
    | _ => 0
  | 7 => fun q => match q with
    | 5 => (-13312 / 67375 : ℚ)
    | 6 => (-48046816 / 35371875 : ℚ)
    | 7 => (-1128881536 / 459834375 : ℚ)
    | 8 => (-213400795312 / 117257765625 : ℚ)
    | 9 => (-4582606096 / 6897515625 : ℚ)
    | 10 => (-4500602632 / 34487578125 : ℚ)
    | 11 => (-341239552 / 23876015625 : ℚ)
    | 12 => (-446368 / 516796875 : ℚ)
    | 13 => (-656 / 24609375 : ℚ)
    | 14 => (-8 / 24609375 : ℚ)
    | _ => 0
  | 8 => fun q => match q with
    | 5 => (24576 / 741125 : ℚ)
    | 6 => (93108814144 / 106221740625 : ℚ)
    | 7 => (122207916928 / 35407246875 : ℚ)
    | 8 => (216818252198006 / 45144239765625 : ℚ)
    | 9 => (8044354399988656 / 2573221666640625 : ℚ)
    | 10 => (49209347375416 / 45144239765625 : ℚ)
    | 11 => (2378918763952 / 10863587109375 : ℚ)
    | 12 => (855970508356 / 32590761328125 : ℚ)
    | 13 => (225782224 / 119380078125 : ℚ)
    | 14 => (205208 / 2583984375 : ℚ)
    | 15 => (656 / 369140625 : ℚ)
    | 16 => (2 / 123046875 : ℚ)
    | _ => 0
  | 9 => fun q => match q with
    | 6 => (-11319928832 / 35407246875 : ℚ)
    | 7 => (-37334207488 / 11802415625 : ℚ)
    | 8 => (-29228533957664 / 3472633828125 : ℚ)
    | 9 => (-478908297241984 / 50455326796875 : ℚ)
    | 10 => (-23644857386576212 / 4288702777734375 : ℚ)
    | 11 => (-23572603832947712 / 12866108333203125 : ℚ)
    | 12 => (-76739512452032 / 207294978515625 : ℚ)
    | 13 => (-102181502048 / 2172717421875 : ℚ)
    | 14 => (-3098083953112 / 814769033203125 : ℚ)
    | 15 => (-1735119808 / 8953505859375 : ℚ)
    | 16 => (-77312 / 12919921875 : ℚ)
    | 17 => (-1312 / 12919921875 : ℚ)
    | 18 => (-4 / 5537109375 : ℚ)
    | _ => 0
  | 10 => fun q => match q with
    | 6 => (7823048704 / 153431403125 : ℚ)
    | 7 => (284328259584 / 153431403125 : ℚ)
    | 8 => (5954335670682304 / 586875116953125 : ℚ)
    | 9 => (133781718759306752 / 6690376333265625 : ℚ)
    | 10 => (26372944589465671636 / 1393828402763671875 : ℚ)
    | 11 => (10052709041052318712 / 1012359576744140625 : ℚ)
    | 12 => (165626399714295432884 / 52686713624466796875 : ℚ)
    | 13 => (4269949879305111968 / 6754706874931640625 : ℚ)
    | 14 => (17761990966259704 / 213306532892578125 : ℚ)
    | 15 => (623854039844624 / 85550748486328125 : ℚ)
    | 16 => (345796100744 / 814769033203125 : ℚ)
    | 17 => (144306592 / 8953505859375 : ℚ)
    | 18 => (73916 / 193798828125 : ℚ)
    | 19 => (328 / 64599609375 : ℚ)
    | 20 => (4 / 138427734375 : ℚ)
    | _ => 0
  | 11 => fun q => match q with
    | 7 => (-2780430336 / 4383754375 : ℚ)
    | 8 => (-2577396385792 / 307103671875 : ℚ)
    | 9 => (-112115356917481472 / 3716875740703125 : ℚ)
    | 10 => (-1858659089667710272 / 39823668650390625 : ℚ)
    | 11 => (-14915863873163456576 / 392547590982421875 : ℚ)
    | 12 => (-119392374205580862272 / 6561589849267578125 : ℚ)
    | 13 => (-21120897043671525904 / 3846966391627734375 : ℚ)
    | 14 => (-1437277460334357107384 / 1317167840611669921875 : ℚ)
    | 15 => (-14885777031140998144 / 101320603123974609375 : ℚ)
    | 16 => (-797605192900576 / 58600695849609375 : ℚ)
    | 17 => (-372751798223968 / 427753742431640625 : ℚ)
    | 18 => (-467558506288 / 12221535498046875 : ℚ)
    | 19 => (-251707712 / 223837646484375 : ℚ)
    | 20 => (-47584 / 2260986328125 : ℚ)
    | 21 => (-656 / 2906982421875 : ℚ)
    | 22 => (-8 / 7613525390625 : ℚ)
    | _ => 0
  | 12 => fun q => match q with
    | 7 => (84934656 / 876750875 : ℚ)
    | 8 => (42656008626688 / 9315478046875 : ℚ)
    | 9 => (23004288307386855424 / 702489514992890625 : ℚ)
    | 10 => (1826264048931862392448 / 21464957402560546875 : ℚ)
    | 11 => (159326297464411204677632 / 1481082060776677734375 : ℚ)
    | 12 => (358408187865356306117092 / 4667275401607177734375 : ℚ)
    | 13 => (1623497202126429881419312 / 47998029747392333984375 : ℚ)
    | 14 => (113569588243796819917176248 / 11663521228616337158203125 : ℚ)
    | 15 => (66620020886718079927561424 / 34990563685849011474609375 : ℚ)
    | 16 => (3986205413628608787404 / 15366958140469482421875 : ℚ)
    | 17 => (1330408454902351722208 / 53193316640086669921875 : ℚ)
    | 18 => (43293256358613384176 / 25196834197935791015625 : ℚ)
    | 19 => (179508798469408 / 2138768712158203125 : ℚ)
    | 20 => (879550180972 / 305538387451171875 : ℚ)
    | 21 => (32346992 / 479652099609375 : ℚ)
    | 22 => (173512 / 169573974609375 : ℚ)
    | 23 => (656 / 72674560546875 : ℚ)
    | 24 => (4 / 114202880859375 : ℚ)
    | _ => 0
  | _ => fun _ => 0

def uniformMGFCoeff (n : ℕ) : ℚ := 3^n / (Nat.factorial (2*n+1) : ℚ)
def fallingPoly : ℕ → ℚ → ℚ
  | 0, _ => 1
  | n+1, x => fallingPoly n x * (x-n)
def pPolynomial (r : ℕ) (y : ℚ) : ℚ :=
  ∑ q ∈ Finset.range (2*r+1), pCoeff r q*y^q
def gPolynomial (r : ℕ) (x : ℚ) : ℚ :=
  ∑ q ∈ Finset.range (2*r+1), pCoeff r q*2^q*fallingPoly q x
def qPolynomial (r : ℕ) (x : ℚ) : ℚ :=
  ∑ q ∈ Finset.range (2*r+1), qFallingCoeff r q*fallingPoly q x
def nbFactorial (q : ℕ) : ℚ := (Nat.factorial (2*q) : ℚ)/(Nat.factorial q*16^q)

theorem log_coefficient_1 :
    (1 : ℚ)*cumulantA 1 = 1*uniformMGFCoeff 1 -
    ∑ j ∈ Finset.range 1, (j : ℚ)*cumulantA j*uniformMGFCoeff (1-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_2 :
    (2 : ℚ)*cumulantA 2 = 2*uniformMGFCoeff 2 -
    ∑ j ∈ Finset.range 2, (j : ℚ)*cumulantA j*uniformMGFCoeff (2-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_3 :
    (3 : ℚ)*cumulantA 3 = 3*uniformMGFCoeff 3 -
    ∑ j ∈ Finset.range 3, (j : ℚ)*cumulantA j*uniformMGFCoeff (3-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_4 :
    (4 : ℚ)*cumulantA 4 = 4*uniformMGFCoeff 4 -
    ∑ j ∈ Finset.range 4, (j : ℚ)*cumulantA j*uniformMGFCoeff (4-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_5 :
    (5 : ℚ)*cumulantA 5 = 5*uniformMGFCoeff 5 -
    ∑ j ∈ Finset.range 5, (j : ℚ)*cumulantA j*uniformMGFCoeff (5-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_6 :
    (6 : ℚ)*cumulantA 6 = 6*uniformMGFCoeff 6 -
    ∑ j ∈ Finset.range 6, (j : ℚ)*cumulantA j*uniformMGFCoeff (6-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_7 :
    (7 : ℚ)*cumulantA 7 = 7*uniformMGFCoeff 7 -
    ∑ j ∈ Finset.range 7, (j : ℚ)*cumulantA j*uniformMGFCoeff (7-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_8 :
    (8 : ℚ)*cumulantA 8 = 8*uniformMGFCoeff 8 -
    ∑ j ∈ Finset.range 8, (j : ℚ)*cumulantA j*uniformMGFCoeff (8-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_9 :
    (9 : ℚ)*cumulantA 9 = 9*uniformMGFCoeff 9 -
    ∑ j ∈ Finset.range 9, (j : ℚ)*cumulantA j*uniformMGFCoeff (9-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_10 :
    (10 : ℚ)*cumulantA 10 = 10*uniformMGFCoeff 10 -
    ∑ j ∈ Finset.range 10, (j : ℚ)*cumulantA j*uniformMGFCoeff (10-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_11 :
    (11 : ℚ)*cumulantA 11 = 11*uniformMGFCoeff 11 -
    ∑ j ∈ Finset.range 11, (j : ℚ)*cumulantA j*uniformMGFCoeff (11-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_12 :
    (12 : ℚ)*cumulantA 12 = 12*uniformMGFCoeff 12 -
    ∑ j ∈ Finset.range 12, (j : ℚ)*cumulantA j*uniformMGFCoeff (12-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem log_coefficient_13 :
    (13 : ℚ)*cumulantA 13 = 13*uniformMGFCoeff 13 -
    ∑ j ∈ Finset.range 13, (j : ℚ)*cumulantA j*uniformMGFCoeff (13-j) := by
  norm_num [cumulantA, uniformMGFCoeff, Finset.sum_range_succ, Nat.factorial]

theorem p_recurrence_1 (y : ℚ) :
    (1 : ℚ)*pPolynomial 1 y =
    ∑ j ∈ Finset.range 1, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (1-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_1 (x : ℚ) :
    (∑ j ∈ Finset.range 2, gPolynomial j x*gPolynomial (1-j) x) = qPolynomial 1 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_1 : normB 1 =
    ∑ q ∈ Finset.range 3, qFallingCoeff 1 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_1 :
    (∑ j ∈ Finset.range 2, normB j*vacuumD (1-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_2 (y : ℚ) :
    (2 : ℚ)*pPolynomial 2 y =
    ∑ j ∈ Finset.range 2, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (2-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_2 (x : ℚ) :
    (∑ j ∈ Finset.range 3, gPolynomial j x*gPolynomial (2-j) x) = qPolynomial 2 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_2 : normB 2 =
    ∑ q ∈ Finset.range 5, qFallingCoeff 2 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_2 :
    (∑ j ∈ Finset.range 3, normB j*vacuumD (2-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_3 (y : ℚ) :
    (3 : ℚ)*pPolynomial 3 y =
    ∑ j ∈ Finset.range 3, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (3-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_3 (x : ℚ) :
    (∑ j ∈ Finset.range 4, gPolynomial j x*gPolynomial (3-j) x) = qPolynomial 3 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_3 : normB 3 =
    ∑ q ∈ Finset.range 7, qFallingCoeff 3 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_3 :
    (∑ j ∈ Finset.range 4, normB j*vacuumD (3-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_4 (y : ℚ) :
    (4 : ℚ)*pPolynomial 4 y =
    ∑ j ∈ Finset.range 4, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (4-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_4 (x : ℚ) :
    (∑ j ∈ Finset.range 5, gPolynomial j x*gPolynomial (4-j) x) = qPolynomial 4 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_4 : normB 4 =
    ∑ q ∈ Finset.range 9, qFallingCoeff 4 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_4 :
    (∑ j ∈ Finset.range 5, normB j*vacuumD (4-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_5 (y : ℚ) :
    (5 : ℚ)*pPolynomial 5 y =
    ∑ j ∈ Finset.range 5, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (5-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_5 (x : ℚ) :
    (∑ j ∈ Finset.range 6, gPolynomial j x*gPolynomial (5-j) x) = qPolynomial 5 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_5 : normB 5 =
    ∑ q ∈ Finset.range 11, qFallingCoeff 5 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_5 :
    (∑ j ∈ Finset.range 6, normB j*vacuumD (5-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_6 (y : ℚ) :
    (6 : ℚ)*pPolynomial 6 y =
    ∑ j ∈ Finset.range 6, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (6-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_6 (x : ℚ) :
    (∑ j ∈ Finset.range 7, gPolynomial j x*gPolynomial (6-j) x) = qPolynomial 6 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_6 : normB 6 =
    ∑ q ∈ Finset.range 13, qFallingCoeff 6 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_6 :
    (∑ j ∈ Finset.range 7, normB j*vacuumD (6-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_7 (y : ℚ) :
    (7 : ℚ)*pPolynomial 7 y =
    ∑ j ∈ Finset.range 7, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (7-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_7 (x : ℚ) :
    (∑ j ∈ Finset.range 8, gPolynomial j x*gPolynomial (7-j) x) = qPolynomial 7 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_7 : normB 7 =
    ∑ q ∈ Finset.range 15, qFallingCoeff 7 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_7 :
    (∑ j ∈ Finset.range 8, normB j*vacuumD (7-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_8 (y : ℚ) :
    (8 : ℚ)*pPolynomial 8 y =
    ∑ j ∈ Finset.range 8, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (8-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_8 (x : ℚ) :
    (∑ j ∈ Finset.range 9, gPolynomial j x*gPolynomial (8-j) x) = qPolynomial 8 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_8 : normB 8 =
    ∑ q ∈ Finset.range 17, qFallingCoeff 8 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_8 :
    (∑ j ∈ Finset.range 9, normB j*vacuumD (8-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_9 (y : ℚ) :
    (9 : ℚ)*pPolynomial 9 y =
    ∑ j ∈ Finset.range 9, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (9-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_9 (x : ℚ) :
    (∑ j ∈ Finset.range 10, gPolynomial j x*gPolynomial (9-j) x) = qPolynomial 9 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_9 : normB 9 =
    ∑ q ∈ Finset.range 19, qFallingCoeff 9 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_9 :
    (∑ j ∈ Finset.range 10, normB j*vacuumD (9-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_10 (y : ℚ) :
    (10 : ℚ)*pPolynomial 10 y =
    ∑ j ∈ Finset.range 10, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (10-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_10 (x : ℚ) :
    (∑ j ∈ Finset.range 11, gPolynomial j x*gPolynomial (10-j) x) = qPolynomial 10 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_10 : normB 10 =
    ∑ q ∈ Finset.range 21, qFallingCoeff 10 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_10 :
    (∑ j ∈ Finset.range 11, normB j*vacuumD (10-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_11 (y : ℚ) :
    (11 : ℚ)*pPolynomial 11 y =
    ∑ j ∈ Finset.range 11, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (11-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_11 (x : ℚ) :
    (∑ j ∈ Finset.range 12, gPolynomial j x*gPolynomial (11-j) x) = qPolynomial 11 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_11 : normB 11 =
    ∑ q ∈ Finset.range 23, qFallingCoeff 11 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_11 :
    (∑ j ∈ Finset.range 12, normB j*vacuumD (11-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

theorem p_recurrence_12 (y : ℚ) :
    (12 : ℚ)*pPolynomial 12 y =
    ∑ j ∈ Finset.range 12, (j+1 : ℚ)*cumulantA (j+2)*y^(j+2)*pPolynomial (12-1-j) y := by
  norm_num [pPolynomial, pCoeff, cumulantA, Finset.sum_range_succ]
  <;> ring

theorem squared_moment_polynomial_12 (x : ℚ) :
    (∑ j ∈ Finset.range 13, gPolynomial j x*gPolynomial (12-j) x) = qPolynomial 12 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

theorem norm_coefficient_12 : normB 12 =
    ∑ q ∈ Finset.range 25, qFallingCoeff 12 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_12 :
    (∑ j ∈ Finset.range 13, normB j*vacuumD (12-j)) = 0 := by
  norm_num [normB, vacuumD, Finset.sum_range_succ]

end EulerianGrothendieck
