import Mathlib

/-! Manuscript 14.119, 17 November 2026, Proposition 10.2 (201).
Finite rational Taylor coefficient identities in t = x². Analytic remainder
estimates for the actual functions are separate proof obligations. -/

namespace Manuscript14.ParryX20

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def b : ℕ → ℚ
  | 0 => (1 : ℚ)
  | 1 => (1 / 6 : ℚ)
  | 2 => (1 / 120 : ℚ)
  | 3 => (1 / 5040 : ℚ)
  | 4 => (1 / 362880 : ℚ)
  | 5 => (1 / 39916800 : ℚ)
  | 6 => (1 / 6227020800 : ℚ)
  | 7 => (1 / 1307674368000 : ℚ)
  | 8 => (1 / 355687428096000 : ℚ)
  | 9 => (1 / 121645100408832000 : ℚ)
  | 10 => (1 / 51090942171709440000 : ℚ)
  | 11 => (1 / 25852016738884976640000 : ℚ)
  | 12 => (1 / 15511210043330985984000000 : ℚ)
  | _ => 0

def a : ℕ → ℚ
  | 0 => (0 : ℚ)
  | 1 => (1 / 6 : ℚ)
  | 2 => (-1 / 180 : ℚ)
  | 3 => (1 / 2835 : ℚ)
  | 4 => (-1 / 37800 : ℚ)
  | 5 => (1 / 467775 : ℚ)
  | 6 => (-691 / 3831077250 : ℚ)
  | 7 => (2 / 127702575 : ℚ)
  | 8 => (-3617 / 2605132530000 : ℚ)
  | 9 => (43867 / 350813659321125 : ℚ)
  | 10 => (-174611 / 15313294652906250 : ℚ)
  | 11 => (155366 / 147926426347074375 : ℚ)
  | 12 => (-236364091 / 2423034863565078262500 : ℚ)
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

theorem sinh_basis_0 :
    b 0 = 1 / (Nat.factorial 1 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_1 :
    b 1 = 1 / (Nat.factorial 3 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_2 :
    b 2 = 1 / (Nat.factorial 5 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_3 :
    b 3 = 1 / (Nat.factorial 7 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_4 :
    b 4 = 1 / (Nat.factorial 9 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_5 :
    b 5 = 1 / (Nat.factorial 11 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_6 :
    b 6 = 1 / (Nat.factorial 13 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_7 :
    b 7 = 1 / (Nat.factorial 15 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_8 :
    b 8 = 1 / (Nat.factorial 17 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_9 :
    b 9 = 1 / (Nat.factorial 19 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_10 :
    b 10 = 1 / (Nat.factorial 21 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_11 :
    b 11 = 1 / (Nat.factorial 23 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem sinh_basis_12 :
    b 12 = 1 / (Nat.factorial 25 : ℚ) := by
  norm_num [b, Nat.factorial]

theorem log_b_1 :
    a 1 = b 1 - ((0 : ℚ)) / 1 := by
  norm_num [a, b, c, p, r]

theorem log_b_2 :
    a 2 = b 2 - ((1 : ℚ) * a 1 * b 1) / 2 := by
  norm_num [a, b, c, p, r]

theorem log_b_3 :
    a 3 = b 3 - ((1 : ℚ) * a 1 * b 2 + (2 : ℚ) * a 2 * b 1) / 3 := by
  norm_num [a, b, c, p, r]

theorem log_b_4 :
    a 4 = b 4 - ((1 : ℚ) * a 1 * b 3 + (2 : ℚ) * a 2 * b 2 + (3 : ℚ) * a 3 * b 1) / 4 := by
  norm_num [a, b, c, p, r]

theorem log_b_5 :
    a 5 = b 5 - ((1 : ℚ) * a 1 * b 4 + (2 : ℚ) * a 2 * b 3 + (3 : ℚ) * a 3 * b 2 + (4 : ℚ) * a 4 * b 1) / 5 := by
  norm_num [a, b, c, p, r]

theorem log_b_6 :
    a 6 = b 6 - ((1 : ℚ) * a 1 * b 5 + (2 : ℚ) * a 2 * b 4 + (3 : ℚ) * a 3 * b 3 + (4 : ℚ) * a 4 * b 2 + (5 : ℚ) * a 5 * b 1) / 6 := by
  norm_num [a, b, c, p, r]

theorem log_b_7 :
    a 7 = b 7 - ((1 : ℚ) * a 1 * b 6 + (2 : ℚ) * a 2 * b 5 + (3 : ℚ) * a 3 * b 4 + (4 : ℚ) * a 4 * b 3 + (5 : ℚ) * a 5 * b 2 + (6 : ℚ) * a 6 * b 1) / 7 := by
  norm_num [a, b, c, p, r]

theorem log_b_8 :
    a 8 = b 8 - ((1 : ℚ) * a 1 * b 7 + (2 : ℚ) * a 2 * b 6 + (3 : ℚ) * a 3 * b 5 + (4 : ℚ) * a 4 * b 4 + (5 : ℚ) * a 5 * b 3 + (6 : ℚ) * a 6 * b 2 + (7 : ℚ) * a 7 * b 1) / 8 := by
  norm_num [a, b, c, p, r]

theorem log_b_9 :
    a 9 = b 9 - ((1 : ℚ) * a 1 * b 8 + (2 : ℚ) * a 2 * b 7 + (3 : ℚ) * a 3 * b 6 + (4 : ℚ) * a 4 * b 5 + (5 : ℚ) * a 5 * b 4 + (6 : ℚ) * a 6 * b 3 + (7 : ℚ) * a 7 * b 2 + (8 : ℚ) * a 8 * b 1) / 9 := by
  norm_num [a, b, c, p, r]

theorem log_b_10 :
    a 10 = b 10 - ((1 : ℚ) * a 1 * b 9 + (2 : ℚ) * a 2 * b 8 + (3 : ℚ) * a 3 * b 7 + (4 : ℚ) * a 4 * b 6 + (5 : ℚ) * a 5 * b 5 + (6 : ℚ) * a 6 * b 4 + (7 : ℚ) * a 7 * b 3 + (8 : ℚ) * a 8 * b 2 + (9 : ℚ) * a 9 * b 1) / 10 := by
  norm_num [a, b, c, p, r]

theorem log_b_11 :
    a 11 = b 11 - ((1 : ℚ) * a 1 * b 10 + (2 : ℚ) * a 2 * b 9 + (3 : ℚ) * a 3 * b 8 + (4 : ℚ) * a 4 * b 7 + (5 : ℚ) * a 5 * b 6 + (6 : ℚ) * a 6 * b 5 + (7 : ℚ) * a 7 * b 4 + (8 : ℚ) * a 8 * b 3 + (9 : ℚ) * a 9 * b 2 + (10 : ℚ) * a 10 * b 1) / 11 := by
  norm_num [a, b, c, p, r]

theorem log_b_12 :
    a 12 = b 12 - ((1 : ℚ) * a 1 * b 11 + (2 : ℚ) * a 2 * b 10 + (3 : ℚ) * a 3 * b 9 + (4 : ℚ) * a 4 * b 8 + (5 : ℚ) * a 5 * b 7 + (6 : ℚ) * a 6 * b 6 + (7 : ℚ) * a 7 * b 5 + (8 : ℚ) * a 8 * b 4 + (9 : ℚ) * a 9 * b 3 + (10 : ℚ) * a 10 * b 2 + (11 : ℚ) * a 11 * b 1) / 12 := by
  norm_num [a, b, c, p, r]

theorem log_c_1 :
    c 1 = 6 * b 2 - ((0 : ℚ)) / 1 := by
  norm_num [a, b, c, p, r]

theorem log_c_2 :
    c 2 = 6 * b 3 - ((1 : ℚ) * c 1 * (6 * b 2)) / 2 := by
  norm_num [a, b, c, p, r]

theorem log_c_3 :
    c 3 = 6 * b 4 - ((1 : ℚ) * c 1 * (6 * b 3) + (2 : ℚ) * c 2 * (6 * b 2)) / 3 := by
  norm_num [a, b, c, p, r]

theorem log_c_4 :
    c 4 = 6 * b 5 - ((1 : ℚ) * c 1 * (6 * b 4) + (2 : ℚ) * c 2 * (6 * b 3) + (3 : ℚ) * c 3 * (6 * b 2)) / 4 := by
  norm_num [a, b, c, p, r]

theorem log_c_5 :
    c 5 = 6 * b 6 - ((1 : ℚ) * c 1 * (6 * b 5) + (2 : ℚ) * c 2 * (6 * b 4) + (3 : ℚ) * c 3 * (6 * b 3) + (4 : ℚ) * c 4 * (6 * b 2)) / 5 := by
  norm_num [a, b, c, p, r]

theorem log_c_6 :
    c 6 = 6 * b 7 - ((1 : ℚ) * c 1 * (6 * b 6) + (2 : ℚ) * c 2 * (6 * b 5) + (3 : ℚ) * c 3 * (6 * b 4) + (4 : ℚ) * c 4 * (6 * b 3) + (5 : ℚ) * c 5 * (6 * b 2)) / 6 := by
  norm_num [a, b, c, p, r]

theorem log_c_7 :
    c 7 = 6 * b 8 - ((1 : ℚ) * c 1 * (6 * b 7) + (2 : ℚ) * c 2 * (6 * b 6) + (3 : ℚ) * c 3 * (6 * b 5) + (4 : ℚ) * c 4 * (6 * b 4) + (5 : ℚ) * c 5 * (6 * b 3) + (6 : ℚ) * c 6 * (6 * b 2)) / 7 := by
  norm_num [a, b, c, p, r]

theorem log_c_8 :
    c 8 = 6 * b 9 - ((1 : ℚ) * c 1 * (6 * b 8) + (2 : ℚ) * c 2 * (6 * b 7) + (3 : ℚ) * c 3 * (6 * b 6) + (4 : ℚ) * c 4 * (6 * b 5) + (5 : ℚ) * c 5 * (6 * b 4) + (6 : ℚ) * c 6 * (6 * b 3) + (7 : ℚ) * c 7 * (6 * b 2)) / 8 := by
  norm_num [a, b, c, p, r]

theorem log_c_9 :
    c 9 = 6 * b 10 - ((1 : ℚ) * c 1 * (6 * b 9) + (2 : ℚ) * c 2 * (6 * b 8) + (3 : ℚ) * c 3 * (6 * b 7) + (4 : ℚ) * c 4 * (6 * b 6) + (5 : ℚ) * c 5 * (6 * b 5) + (6 : ℚ) * c 6 * (6 * b 4) + (7 : ℚ) * c 7 * (6 * b 3) + (8 : ℚ) * c 8 * (6 * b 2)) / 9 := by
  norm_num [a, b, c, p, r]

theorem log_c_10 :
    c 10 = 6 * b 11 - ((1 : ℚ) * c 1 * (6 * b 10) + (2 : ℚ) * c 2 * (6 * b 9) + (3 : ℚ) * c 3 * (6 * b 8) + (4 : ℚ) * c 4 * (6 * b 7) + (5 : ℚ) * c 5 * (6 * b 6) + (6 : ℚ) * c 6 * (6 * b 5) + (7 : ℚ) * c 7 * (6 * b 4) + (8 : ℚ) * c 8 * (6 * b 3) + (9 : ℚ) * c 9 * (6 * b 2)) / 10 := by
  norm_num [a, b, c, p, r]

theorem log_c_11 :
    c 11 = 6 * b 12 - ((1 : ℚ) * c 1 * (6 * b 11) + (2 : ℚ) * c 2 * (6 * b 10) + (3 : ℚ) * c 3 * (6 * b 9) + (4 : ℚ) * c 4 * (6 * b 8) + (5 : ℚ) * c 5 * (6 * b 7) + (6 : ℚ) * c 6 * (6 * b 6) + (7 : ℚ) * c 7 * (6 * b 5) + (8 : ℚ) * c 8 * (6 * b 4) + (9 : ℚ) * c 9 * (6 * b 3) + (10 : ℚ) * c 10 * (6 * b 2)) / 11 := by
  norm_num [a, b, c, p, r]

theorem reciprocal_0 :
    a 1 * p 0 = 1 := by
  norm_num [a, b, c, p, r]

theorem product_0 :
    r 0 = -(p 0 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_1 :
    a 1 * p 1 + a 2 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_1 :
    r 1 = -(p 0 * c 1 + p 1 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_2 :
    a 1 * p 2 + a 2 * p 1 + a 3 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_2 :
    r 2 = -(p 0 * c 2 + p 1 * c 1 + p 2 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_3 :
    a 1 * p 3 + a 2 * p 2 + a 3 * p 1 + a 4 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_3 :
    r 3 = -(p 0 * c 3 + p 1 * c 2 + p 2 * c 1 + p 3 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_4 :
    a 1 * p 4 + a 2 * p 3 + a 3 * p 2 + a 4 * p 1 + a 5 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_4 :
    r 4 = -(p 0 * c 4 + p 1 * c 3 + p 2 * c 2 + p 3 * c 1 + p 4 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_5 :
    a 1 * p 5 + a 2 * p 4 + a 3 * p 3 + a 4 * p 2 + a 5 * p 1 + a 6 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_5 :
    r 5 = -(p 0 * c 5 + p 1 * c 4 + p 2 * c 3 + p 3 * c 2 + p 4 * c 1 + p 5 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_6 :
    a 1 * p 6 + a 2 * p 5 + a 3 * p 4 + a 4 * p 3 + a 5 * p 2 + a 6 * p 1 + a 7 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_6 :
    r 6 = -(p 0 * c 6 + p 1 * c 5 + p 2 * c 4 + p 3 * c 3 + p 4 * c 2 + p 5 * c 1 + p 6 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_7 :
    a 1 * p 7 + a 2 * p 6 + a 3 * p 5 + a 4 * p 4 + a 5 * p 3 + a 6 * p 2 + a 7 * p 1 + a 8 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_7 :
    r 7 = -(p 0 * c 7 + p 1 * c 6 + p 2 * c 5 + p 3 * c 4 + p 4 * c 3 + p 5 * c 2 + p 6 * c 1 + p 7 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_8 :
    a 1 * p 8 + a 2 * p 7 + a 3 * p 6 + a 4 * p 5 + a 5 * p 4 + a 6 * p 3 + a 7 * p 2 + a 8 * p 1 + a 9 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_8 :
    r 8 = -(p 0 * c 8 + p 1 * c 7 + p 2 * c 6 + p 3 * c 5 + p 4 * c 4 + p 5 * c 3 + p 6 * c 2 + p 7 * c 1 + p 8 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_9 :
    a 1 * p 9 + a 2 * p 8 + a 3 * p 7 + a 4 * p 6 + a 5 * p 5 + a 6 * p 4 + a 7 * p 3 + a 8 * p 2 + a 9 * p 1 + a 10 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_9 :
    r 9 = -(p 0 * c 9 + p 1 * c 8 + p 2 * c 7 + p 3 * c 6 + p 4 * c 5 + p 5 * c 4 + p 6 * c 3 + p 7 * c 2 + p 8 * c 1 + p 9 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_10 :
    a 1 * p 10 + a 2 * p 9 + a 3 * p 8 + a 4 * p 7 + a 5 * p 6 + a 6 * p 5 + a 7 * p 4 + a 8 * p 3 + a 9 * p 2 + a 10 * p 1 + a 11 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_10 :
    r 10 = -(p 0 * c 10 + p 1 * c 9 + p 2 * c 8 + p 3 * c 7 + p 4 * c 6 + p 5 * c 5 + p 6 * c 4 + p 7 * c 3 + p 8 * c 2 + p 9 * c 1 + p 10 * c 0) := by
  norm_num [a, b, c, p, r]

theorem reciprocal_11 :
    a 1 * p 11 + a 2 * p 10 + a 3 * p 9 + a 4 * p 8 + a 5 * p 7 + a 6 * p 6 + a 7 * p 5 + a 8 * p 4 + a 9 * p 3 + a 10 * p 2 + a 11 * p 1 + a 12 * p 0 = 0 := by
  norm_num [a, b, c, p, r]

theorem product_11 :
    r 11 = -(p 0 * c 11 + p 1 * c 10 + p 2 * c 9 + p 3 * c 8 + p 4 * c 7 + p 5 * c 6 + p 6 * c 5 + p 7 * c 4 + p 8 * c 3 + p 9 * c 2 + p 10 * c 1 + p 11 * c 0) := by
  norm_num [a, b, c, p, r]

theorem zeta_term_9 :
    a 9 / 8 ^ 9 = (43867 / 47085412305447419904000 : ℚ) ∧ (43867 / 798 : ℚ) / (2 ^ 10 * 9 * (Nat.factorial 18 : ℚ)) = (43867 / 47085412305447419904000 : ℚ) := by
  norm_num [a, Nat.factorial]

theorem zeta_term_10 :
    a 10 / 8 ^ 10 = (-174611 / 16442524932061003776000000 : ℚ) ∧ (-174611 / 330 : ℚ) / (2 ^ 11 * 10 * (Nat.factorial 20 : ℚ)) = (-174611 / 16442524932061003776000000 : ℚ) := by
  norm_num [a, Nat.factorial]

theorem zeta_term_11 :
    a 11 / 8 ^ 11 = (77683 / 635339163374837185904640000 : ℚ) ∧ (854513 / 138 : ℚ) / (2 ^ 12 * 11 * (Nat.factorial 22 : ℚ)) = (77683 / 635339163374837185904640000 : ℚ) := by
  norm_num [a, Nat.factorial]

/-! The displayed x^20 coefficients are the degree-11 coefficients prior to dividing by t. -/
theorem terminal_coefficients :
    p 11 = (326577481196239877 / 610604785618399722150000000000 : ℚ) ∧ r 11 = (1238782192338196421 / 4062763485856018944000000000000 : ℚ) := by
  norm_num [a, b, c, p, r]

end Manuscript14.ParryX20

#print axioms Manuscript14.ParryX20.sinh_basis_0
#print axioms Manuscript14.ParryX20.sinh_basis_1
#print axioms Manuscript14.ParryX20.sinh_basis_2
#print axioms Manuscript14.ParryX20.sinh_basis_3
#print axioms Manuscript14.ParryX20.sinh_basis_4
#print axioms Manuscript14.ParryX20.sinh_basis_5
#print axioms Manuscript14.ParryX20.sinh_basis_6
#print axioms Manuscript14.ParryX20.sinh_basis_7
#print axioms Manuscript14.ParryX20.sinh_basis_8
#print axioms Manuscript14.ParryX20.sinh_basis_9
#print axioms Manuscript14.ParryX20.sinh_basis_10
#print axioms Manuscript14.ParryX20.sinh_basis_11
#print axioms Manuscript14.ParryX20.sinh_basis_12
#print axioms Manuscript14.ParryX20.log_b_1
#print axioms Manuscript14.ParryX20.log_b_2
#print axioms Manuscript14.ParryX20.log_b_3
#print axioms Manuscript14.ParryX20.log_b_4
#print axioms Manuscript14.ParryX20.log_b_5
#print axioms Manuscript14.ParryX20.log_b_6
#print axioms Manuscript14.ParryX20.log_b_7
#print axioms Manuscript14.ParryX20.log_b_8
#print axioms Manuscript14.ParryX20.log_b_9
#print axioms Manuscript14.ParryX20.log_b_10
#print axioms Manuscript14.ParryX20.log_b_11
#print axioms Manuscript14.ParryX20.log_b_12
#print axioms Manuscript14.ParryX20.log_c_1
#print axioms Manuscript14.ParryX20.log_c_2
#print axioms Manuscript14.ParryX20.log_c_3
#print axioms Manuscript14.ParryX20.log_c_4
#print axioms Manuscript14.ParryX20.log_c_5
#print axioms Manuscript14.ParryX20.log_c_6
#print axioms Manuscript14.ParryX20.log_c_7
#print axioms Manuscript14.ParryX20.log_c_8
#print axioms Manuscript14.ParryX20.log_c_9
#print axioms Manuscript14.ParryX20.log_c_10
#print axioms Manuscript14.ParryX20.log_c_11
#print axioms Manuscript14.ParryX20.reciprocal_0
#print axioms Manuscript14.ParryX20.product_0
#print axioms Manuscript14.ParryX20.reciprocal_1
#print axioms Manuscript14.ParryX20.product_1
#print axioms Manuscript14.ParryX20.reciprocal_2
#print axioms Manuscript14.ParryX20.product_2
#print axioms Manuscript14.ParryX20.reciprocal_3
#print axioms Manuscript14.ParryX20.product_3
#print axioms Manuscript14.ParryX20.reciprocal_4
#print axioms Manuscript14.ParryX20.product_4
#print axioms Manuscript14.ParryX20.reciprocal_5
#print axioms Manuscript14.ParryX20.product_5
#print axioms Manuscript14.ParryX20.reciprocal_6
#print axioms Manuscript14.ParryX20.product_6
#print axioms Manuscript14.ParryX20.reciprocal_7
#print axioms Manuscript14.ParryX20.product_7
#print axioms Manuscript14.ParryX20.reciprocal_8
#print axioms Manuscript14.ParryX20.product_8
#print axioms Manuscript14.ParryX20.reciprocal_9
#print axioms Manuscript14.ParryX20.product_9
#print axioms Manuscript14.ParryX20.reciprocal_10
#print axioms Manuscript14.ParryX20.product_10
#print axioms Manuscript14.ParryX20.reciprocal_11
#print axioms Manuscript14.ParryX20.product_11
#print axioms Manuscript14.ParryX20.zeta_term_9
#print axioms Manuscript14.ParryX20.zeta_term_10
#print axioms Manuscript14.ParryX20.zeta_term_11
#print axioms Manuscript14.ParryX20.terminal_coefficients

