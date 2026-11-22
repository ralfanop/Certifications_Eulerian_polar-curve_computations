#!/bin/bash
# Rebuild every module, print the axioms of every theorem and run leanchecker.
# Run from this folder with the toolchain of lean-toolchain (elan) on the PATH.
set -u
mkdir -p ../LOGS_LOCAL
EC="Bracket CubeSlabs FourierModes EulerianFourier CentralSlope LocalLimit Combinatorics"
PA="SincGaussian TailConstants IntegralBound FiniteComparisons ConsecutiveSlopes OddSlopeTail GlobalApex EvenAsymptotics SincExpBounds OddSecondOrder ApexDefinitions ExpansionCalculus LogSincSeries LaplaceAllOrders SlopeAllOrders EvenDirect AngleAllOrders ConsecutiveRatios DeficitRatioCoefficients QuantCalculus QuantSinc QuantLaplace QuantSlopes CardioidIdentities CardioidProbability CardioidRigidity CardioidModular"
lake exe cache get || true
for m in $(for x in $EC; do echo EulerianCert.$x; done) $(for x in $PA; do echo PrivateApex.$x; done); do
  lake build $m > ../LOGS_LOCAL/$m.log 2>&1; echo "$m exit=$?"
done
A=../LOGS_LOCAL/axioms.lean
{ echo "import PrivateApex.QuantSlopes"; echo "import PrivateApex.DeficitRatioCoefficients"
  echo "import PrivateApex.CardioidRigidity"; echo "import PrivateApex.CardioidModular"; echo "import PrivateApex.ApexDefinitions"
  echo "open PrivateApex PrivateApex.Cardioid"
  for x in $PA; do grep -h "^theorem " PrivateApex/$x.lean | sed -E 's/^theorem ([^ :({]+).*/#print axioms \1/'; done; } > $A
lake env lean $A > ../LOGS_LOCAL/AXIOMS.txt 2>&1
for m in $PA; do lake env leanchecker PrivateApex.$m > /dev/null 2>&1; echo "leanchecker PrivateApex.$m exit=$?"; done
