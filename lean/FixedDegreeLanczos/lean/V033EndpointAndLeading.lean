import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def ieval : List ℤ → ℤ → ℤ
 | [], _ => 0
 | a::p, x => a + x*ieval p x
theorem legendre_cert_5 :
  4*(4*5^2-1)*ieval betaNum5 1 = 5^2*ieval betaDen5 1 := by decide
theorem leading_cert_5 :
  12*(betaNum5.getLast!) = 5*(betaDen5.getLast!) := by decide
theorem subleading_cert_5 :
  20*((betaNum5.reverse[1]!) * betaDen5.getLast! - betaNum5.getLast! * (betaDen5.reverse[1]!))
  = -5*4*(betaDen5.getLast!)^2 := by decide
theorem denominator_positive_5_1 : 0 < ieval betaDen5 1 := by decide
theorem denominator_positive_5_2 : 0 < ieval betaDen5 2 := by decide
theorem denominator_positive_5_3 : 0 < ieval betaDen5 3 := by decide
theorem denominator_positive_5_4 : 0 < ieval betaDen5 4 := by decide
theorem denominator_positive_5_5 : 0 < ieval betaDen5 5 := by decide
theorem denominator_positive_5_10 : 0 < ieval betaDen5 10 := by decide
theorem denominator_positive_5_335 : 0 < ieval betaDen5 335 := by decide
theorem legendre_cert_6 :
  4*(4*6^2-1)*ieval betaNum6 1 = 6^2*ieval betaDen6 1 := by decide
theorem leading_cert_6 :
  12*(betaNum6.getLast!) = 6*(betaDen6.getLast!) := by decide
theorem subleading_cert_6 :
  20*((betaNum6.reverse[1]!) * betaDen6.getLast! - betaNum6.getLast! * (betaDen6.reverse[1]!))
  = -6*5*(betaDen6.getLast!)^2 := by decide
theorem denominator_positive_6_1 : 0 < ieval betaDen6 1 := by decide
theorem denominator_positive_6_2 : 0 < ieval betaDen6 2 := by decide
theorem denominator_positive_6_3 : 0 < ieval betaDen6 3 := by decide
theorem denominator_positive_6_4 : 0 < ieval betaDen6 4 := by decide
theorem denominator_positive_6_5 : 0 < ieval betaDen6 5 := by decide
theorem denominator_positive_6_10 : 0 < ieval betaDen6 10 := by decide
theorem denominator_positive_6_335 : 0 < ieval betaDen6 335 := by decide
theorem legendre_cert_7 :
  4*(4*7^2-1)*ieval betaNum7 1 = 7^2*ieval betaDen7 1 := by decide
theorem leading_cert_7 :
  12*(betaNum7.getLast!) = 7*(betaDen7.getLast!) := by decide
theorem subleading_cert_7 :
  20*((betaNum7.reverse[1]!) * betaDen7.getLast! - betaNum7.getLast! * (betaDen7.reverse[1]!))
  = -7*6*(betaDen7.getLast!)^2 := by decide
theorem denominator_positive_7_1 : 0 < ieval betaDen7 1 := by decide
theorem denominator_positive_7_2 : 0 < ieval betaDen7 2 := by decide
theorem denominator_positive_7_3 : 0 < ieval betaDen7 3 := by decide
theorem denominator_positive_7_4 : 0 < ieval betaDen7 4 := by decide
theorem denominator_positive_7_5 : 0 < ieval betaDen7 5 := by decide
theorem denominator_positive_7_10 : 0 < ieval betaDen7 10 := by decide
theorem denominator_positive_7_335 : 0 < ieval betaDen7 335 := by decide
theorem legendre_cert_8 :
  4*(4*8^2-1)*ieval betaNum8 1 = 8^2*ieval betaDen8 1 := by decide
theorem leading_cert_8 :
  12*(betaNum8.getLast!) = 8*(betaDen8.getLast!) := by decide
theorem subleading_cert_8 :
  20*((betaNum8.reverse[1]!) * betaDen8.getLast! - betaNum8.getLast! * (betaDen8.reverse[1]!))
  = -8*7*(betaDen8.getLast!)^2 := by decide
theorem denominator_positive_8_1 : 0 < ieval betaDen8 1 := by decide
theorem denominator_positive_8_2 : 0 < ieval betaDen8 2 := by decide
theorem denominator_positive_8_3 : 0 < ieval betaDen8 3 := by decide
theorem denominator_positive_8_4 : 0 < ieval betaDen8 4 := by decide
theorem denominator_positive_8_5 : 0 < ieval betaDen8 5 := by decide
theorem denominator_positive_8_10 : 0 < ieval betaDen8 10 := by decide
theorem denominator_positive_8_335 : 0 < ieval betaDen8 335 := by decide
theorem legendre_cert_9 :
  4*(4*9^2-1)*ieval betaNum9 1 = 9^2*ieval betaDen9 1 := by decide
theorem leading_cert_9 :
  12*(betaNum9.getLast!) = 9*(betaDen9.getLast!) := by decide
theorem subleading_cert_9 :
  20*((betaNum9.reverse[1]!) * betaDen9.getLast! - betaNum9.getLast! * (betaDen9.reverse[1]!))
  = -9*8*(betaDen9.getLast!)^2 := by decide
theorem denominator_positive_9_1 : 0 < ieval betaDen9 1 := by decide
theorem denominator_positive_9_2 : 0 < ieval betaDen9 2 := by decide
theorem denominator_positive_9_3 : 0 < ieval betaDen9 3 := by decide
theorem denominator_positive_9_4 : 0 < ieval betaDen9 4 := by decide
theorem denominator_positive_9_5 : 0 < ieval betaDen9 5 := by decide
theorem denominator_positive_9_10 : 0 < ieval betaDen9 10 := by decide
theorem denominator_positive_9_335 : 0 < ieval betaDen9 335 := by decide
theorem legendre_cert_10 :
  4*(4*10^2-1)*ieval betaNum10 1 = 10^2*ieval betaDen10 1 := by decide
theorem leading_cert_10 :
  12*(betaNum10.getLast!) = 10*(betaDen10.getLast!) := by decide
theorem subleading_cert_10 :
  20*((betaNum10.reverse[1]!) * betaDen10.getLast! - betaNum10.getLast! * (betaDen10.reverse[1]!))
  = -10*9*(betaDen10.getLast!)^2 := by decide
theorem denominator_positive_10_1 : 0 < ieval betaDen10 1 := by decide
theorem denominator_positive_10_2 : 0 < ieval betaDen10 2 := by decide
theorem denominator_positive_10_3 : 0 < ieval betaDen10 3 := by decide
theorem denominator_positive_10_4 : 0 < ieval betaDen10 4 := by decide
theorem denominator_positive_10_5 : 0 < ieval betaDen10 5 := by decide
theorem denominator_positive_10_10 : 0 < ieval betaDen10 10 := by decide
theorem denominator_positive_10_335 : 0 < ieval betaDen10 335 := by decide
theorem legendre_cert_11 :
  4*(4*11^2-1)*ieval betaNum11 1 = 11^2*ieval betaDen11 1 := by decide
theorem leading_cert_11 :
  12*(betaNum11.getLast!) = 11*(betaDen11.getLast!) := by decide
theorem subleading_cert_11 :
  20*((betaNum11.reverse[1]!) * betaDen11.getLast! - betaNum11.getLast! * (betaDen11.reverse[1]!))
  = -11*10*(betaDen11.getLast!)^2 := by decide
theorem denominator_positive_11_1 : 0 < ieval betaDen11 1 := by decide
theorem denominator_positive_11_2 : 0 < ieval betaDen11 2 := by decide
theorem denominator_positive_11_3 : 0 < ieval betaDen11 3 := by decide
theorem denominator_positive_11_4 : 0 < ieval betaDen11 4 := by decide
theorem denominator_positive_11_5 : 0 < ieval betaDen11 5 := by decide
theorem denominator_positive_11_10 : 0 < ieval betaDen11 10 := by decide
theorem denominator_positive_11_335 : 0 < ieval betaDen11 335 := by decide
theorem legendre_cert_12 :
  4*(4*12^2-1)*ieval betaNum12 1 = 12^2*ieval betaDen12 1 := by decide
theorem leading_cert_12 :
  12*(betaNum12.getLast!) = 12*(betaDen12.getLast!) := by decide
theorem subleading_cert_12 :
  20*((betaNum12.reverse[1]!) * betaDen12.getLast! - betaNum12.getLast! * (betaDen12.reverse[1]!))
  = -12*11*(betaDen12.getLast!)^2 := by decide
theorem denominator_positive_12_1 : 0 < ieval betaDen12 1 := by decide
theorem denominator_positive_12_2 : 0 < ieval betaDen12 2 := by decide
theorem denominator_positive_12_3 : 0 < ieval betaDen12 3 := by decide
theorem denominator_positive_12_4 : 0 < ieval betaDen12 4 := by decide
theorem denominator_positive_12_5 : 0 < ieval betaDen12 5 := by decide
theorem denominator_positive_12_10 : 0 < ieval betaDen12 10 := by decide
theorem denominator_positive_12_335 : 0 < ieval betaDen12 335 := by decide
theorem legendre_cert_13 :
  4*(4*13^2-1)*ieval betaNum13 1 = 13^2*ieval betaDen13 1 := by decide
theorem leading_cert_13 :
  12*(betaNum13.getLast!) = 13*(betaDen13.getLast!) := by decide
theorem subleading_cert_13 :
  20*((betaNum13.reverse[1]!) * betaDen13.getLast! - betaNum13.getLast! * (betaDen13.reverse[1]!))
  = -13*12*(betaDen13.getLast!)^2 := by decide
theorem denominator_positive_13_1 : 0 < ieval betaDen13 1 := by decide
theorem denominator_positive_13_2 : 0 < ieval betaDen13 2 := by decide
theorem denominator_positive_13_3 : 0 < ieval betaDen13 3 := by decide
theorem denominator_positive_13_4 : 0 < ieval betaDen13 4 := by decide
theorem denominator_positive_13_5 : 0 < ieval betaDen13 5 := by decide
theorem denominator_positive_13_10 : 0 < ieval betaDen13 10 := by decide
theorem denominator_positive_13_335 : 0 < ieval betaDen13 335 := by decide
theorem legendre_cert_14 :
  4*(4*14^2-1)*ieval betaNum14 1 = 14^2*ieval betaDen14 1 := by decide
theorem leading_cert_14 :
  12*(betaNum14.getLast!) = 14*(betaDen14.getLast!) := by decide
theorem subleading_cert_14 :
  20*((betaNum14.reverse[1]!) * betaDen14.getLast! - betaNum14.getLast! * (betaDen14.reverse[1]!))
  = -14*13*(betaDen14.getLast!)^2 := by decide
theorem denominator_positive_14_1 : 0 < ieval betaDen14 1 := by decide
theorem denominator_positive_14_2 : 0 < ieval betaDen14 2 := by decide
theorem denominator_positive_14_3 : 0 < ieval betaDen14 3 := by decide
theorem denominator_positive_14_4 : 0 < ieval betaDen14 4 := by decide
theorem denominator_positive_14_5 : 0 < ieval betaDen14 5 := by decide
theorem denominator_positive_14_10 : 0 < ieval betaDen14 10 := by decide
theorem denominator_positive_14_335 : 0 < ieval betaDen14 335 := by decide
theorem legendre_cert_15 :
  4*(4*15^2-1)*ieval betaNum15 1 = 15^2*ieval betaDen15 1 := by decide
theorem leading_cert_15 :
  12*(betaNum15.getLast!) = 15*(betaDen15.getLast!) := by decide
theorem subleading_cert_15 :
  20*((betaNum15.reverse[1]!) * betaDen15.getLast! - betaNum15.getLast! * (betaDen15.reverse[1]!))
  = -15*14*(betaDen15.getLast!)^2 := by decide
theorem denominator_positive_15_1 : 0 < ieval betaDen15 1 := by decide
theorem denominator_positive_15_2 : 0 < ieval betaDen15 2 := by decide
theorem denominator_positive_15_3 : 0 < ieval betaDen15 3 := by decide
theorem denominator_positive_15_4 : 0 < ieval betaDen15 4 := by decide
theorem denominator_positive_15_5 : 0 < ieval betaDen15 5 := by decide
theorem denominator_positive_15_10 : 0 < ieval betaDen15 10 := by decide
theorem denominator_positive_15_335 : 0 < ieval betaDen15 335 := by decide
theorem legendre_cert_16 :
  4*(4*16^2-1)*ieval betaNum16 1 = 16^2*ieval betaDen16 1 := by decide
theorem leading_cert_16 :
  12*(betaNum16.getLast!) = 16*(betaDen16.getLast!) := by decide
theorem subleading_cert_16 :
  20*((betaNum16.reverse[1]!) * betaDen16.getLast! - betaNum16.getLast! * (betaDen16.reverse[1]!))
  = -16*15*(betaDen16.getLast!)^2 := by decide
theorem denominator_positive_16_1 : 0 < ieval betaDen16 1 := by decide
theorem denominator_positive_16_2 : 0 < ieval betaDen16 2 := by decide
theorem denominator_positive_16_3 : 0 < ieval betaDen16 3 := by decide
theorem denominator_positive_16_4 : 0 < ieval betaDen16 4 := by decide
theorem denominator_positive_16_5 : 0 < ieval betaDen16 5 := by decide
theorem denominator_positive_16_10 : 0 < ieval betaDen16 10 := by decide
theorem denominator_positive_16_335 : 0 < ieval betaDen16 335 := by decide
end V033
