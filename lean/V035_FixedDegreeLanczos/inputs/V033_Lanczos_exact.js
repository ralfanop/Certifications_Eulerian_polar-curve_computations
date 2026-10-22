
"use strict";

// V033 — Exact Lanczos coefficients beta_5 through beta_16.
// No floating-point arithmetic. No external libraries.
// Polynomial arrays are in ascending powers of M.

const fs = require("node:fs");
const K = 16;

const abs = a => a < 0n ? -a : a;

function gcd(a, b) {
  a = abs(a);
  b = abs(b);
  while (b !== 0n) {
    const t = a % b;
    a = b;
    b = t;
  }
  return a;
}

function rational(a, b = 1n) {
  if (b === 0n) throw Error("Zero denominator");
  if (b < 0n) {
    a = -a;
    b = -b;
  }
  const g = gcd(a, b);
  return [a / g, b / g];
}

function rAdd(a, b) {
  return rational(
    a[0] * b[1] + b[0] * a[1],
    a[1] * b[1]
  );
}

function rMul(a, b) {
  return rational(a[0] * b[0], a[1] * b[1]);
}

function factorial(n) {
  let v = 1n;
  for (let k = 2; k <= n; k++) v *= BigInt(k);
  return v;
}

const ZERO = [0n, 1n];
const ONE = [1n, 1n];

// Exact coefficient polynomials of
// (sinh(z/2)/(z/2))^M = sum c_k(M) z^(2k).
//
// c_0 = 1;
// c_n = (1/n) sum_{k=1}^n
//       [((M+1)k-n)/(4^k (2k+1)!)] c_{n-k}.

const coefficients = [[ONE]];

for (let n = 1; n <= K; n++) {
  const p = Array.from({ length: n + 1 }, () => ZERO);

  for (let k = 1; k <= n; k++) {
    const factor = rational(
      1n,
      BigInt(n) * 4n ** BigInt(k) * factorial(2 * k + 1)
    );

    coefficients[n - k].forEach((v, j) => {
      const w = rMul(v, factor);

      p[j] = rAdd(
        p[j],
        rMul(w, [BigInt(k - n), 1n])
      );

      p[j + 1] = rAdd(
        p[j + 1],
        rMul(w, [BigInt(k), 1n])
      );
    });
  }

  coefficients.push(p);
}

// Exact even moments, as rational polynomials in M.
const moments = coefficients.map((p, k) =>
  p.map(v => rMul(v, [factorial(2 * k), 1n]))
);

// One common denominator makes all moment polynomials
// integral without changing determinant ratios.
let common = 1n;

for (const p of moments) {
  for (const v of p) {
    common = (common / gcd(common, v[1])) * v[1];
  }
}

const momentInt = moments.map(p =>
  p.map(v => v[0] * (common / v[1]))
);

// Integer-polynomial arithmetic.
function trim(p) {
  while (p.length > 1 && p[p.length - 1] === 0n) {
    p.pop();
  }
  return p;
}

function multiply(p, q) {
  const out = Array(p.length + q.length - 1).fill(0n);

  for (let i = 0; i < p.length; i++) {
    for (let j = 0; j < q.length; j++) {
      out[i + j] += p[i] * q[j];
    }
  }
  return trim(out);
}

function subtract(p, q) {
  return trim(
    Array.from(
      { length: Math.max(p.length, q.length) },
      (_, i) => (p[i] ?? 0n) - (q[i] ?? 0n)
    )
  );
}

function divideExact(p, q) {
  let rem = p.slice();
  const out = Array(
    Math.max(1, p.length - q.length + 1)
  ).fill(0n);

  while (
    rem.length >= q.length &&
    rem[rem.length - 1] !== 0n
  ) {
    const a = rem[rem.length - 1];
    const b = q[q.length - 1];
    const v = a / b;

    if (v * b !== a) {
      throw Error("Non-exact polynomial division");
    }

    const shift = rem.length - q.length;
    out[shift] = v;

    for (let i = 0; i < q.length; i++) {
      rem[i + shift] -= v * q[i];
    }

    trim(rem);
  }

  if (rem.some(v => v !== 0n)) {
    throw Error("Nonzero polynomial remainder");
  }

  return trim(out);
}

// Fraction-free Bareiss determinant.
function parityDeterminant(odd, n) {
  if (n === 0) return [1n];

  const a = Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) =>
      momentInt[i + j + (odd ? 1 : 0)].slice()
    )
  );

  let previousPivot = [1n];

  for (let k = 0; k < n - 1; k++) {
    const pivot = a[k][k];

    for (let i = k + 1; i < n; i++) {
      for (let j = k + 1; j < n; j++) {
        a[i][j] = divideExact(
          subtract(
            multiply(pivot, a[i][j]),
            multiply(a[i][k], a[k][j])
          ),
          previousPivot
        );
      }
    }

    for (let i = k + 1; i < n; i++) {
      a[i][k] = [0n];
    }

    previousPivot = pivot;
  }

  return a[n - 1][n - 1];
}

// Strip the lowest powers of M; divide integer content;
// choose positive leading coefficient.
function primitive(p) {
  p = p.slice();

  while (p.length > 1 && p[0] === 0n) {
    p.shift();
  }

  const content = p.reduce((a, b) => gcd(a, b), 0n);
  const sign = p[p.length - 1] < 0n ? -1n : 1n;

  return p.map(x => sign * x / content);
}

// Primitive parity-Hankel polynomials.
const A = Array.from(
  { length: 10 },
  (_, r) => primitive(parityDeterminant(false, r))
);

const B = Array.from(
  { length: 9 },
  (_, r) => primitive(parityDeterminant(true, r))
);

// Exact normalizing constants, independently checked.
const scalars = {
  5: [25n, 132n],
  6: [1n, 1430n],
  7: [49n, 780n],
  8: [10n, 51n],
  9: [3n, 9044n],
  10: [1n, 3990n],
  11: [121n, 1380n],
  12: [7n, 23n],
  13: [169n, 12n],
  14: [1n, 870n],
  15: [1n, 197780n],
  16: [4n, 1023n]
};

function evaluate(p, x) {
  return p.reduceRight((v, a) => v * x + a, 0n);
}

function strings(p) {
  return p.map(String);
}

const beta = {};

for (let j = 5; j <= 16; j++) {
  const r = Math.floor(j / 2);
  const odd = j % 2 === 1;
  const [cn, cd] = scalars[j];

  const numFactors = odd
    ? [A[r], B[r + 1]]
    : [A[r + 1], B[r - 1]];

  const denFactors = odd
    ? [A[r + 1], B[r]]
    : [A[r], B[r]];

  const N = multiply(
    numFactors[0],
    numFactors[1]
  ).map(x => cn * x);

  const D = multiply(
    denFactors[0],
    denFactors[1]
  ).map(x => cd * x);

  const jj = BigInt(j);

  // Exact M=1 Legendre identity.
  if (
    4n * (4n * jj * jj - 1n) * evaluate(N, 1n)
    !== jj * jj * evaluate(D, 1n)
  ) {
    throw Error(`Legendre check failed at j=${j}`);
  }

  // Exact leading term j*M/12.
  if (12n * N[N.length - 1] !== jj * D[D.length - 1]) {
    throw Error(`Leading term failed at j=${j}`);
  }

  // Exact constant term -j*(j-1)/20.
  const nl = N[N.length - 1];
  const np = N[N.length - 2];
  const dl = D[D.length - 1];
  const dp = D[D.length - 2];

  if (
    20n * (np * dl - nl * dp)
    !== -jj * (jj - 1n) * dl * dl
  ) {
    throw Error(`Second term failed at j=${j}`);
  }

  beta[j] = {
    prefactor: `${cn}/${cd}`,
    numerator_factors: odd
      ? [`A${r}`, `B${r + 1}`]
      : [`A${r + 1}`, `B${r - 1}`],
    denominator_factors: odd
      ? [`A${r + 1}`, `B${r}`]
      : [`A${r}`, `B${r}`],
    numerator: strings(N),
    denominator: strings(D),
    degree_numerator: N.length - 1,
    degree_denominator: D.length - 1,
    exact_checks: "passed"
  };
}

const result = {
  manuscript: "V033",
  mathematical_status: "exact rational functions",
  domain: "M is a positive integer",
  representation: "ascending powers of M",
  coefficients: beta,
  primitive_polynomials: {
    A: Object.fromEntries(
      A.map((p, i) => [`A${i}`, strings(p)])
    ),
    B: Object.fromEntries(
      B.map((p, i) => [`B${i}`, strings(p)])
    )
  },
  common_moment_denominator: String(common),
  asymptotic_theorem:
    "beta_j(M) = j*M/12 - j*(j-1)/20 + O_j(1/M)",
  arithmetic: "BigInt integers and reduced exact rationals"
};

const filename = "V033_Lanczos_beta5_beta16_exact.json";

// 'wx' prevents accidentally overwriting an existing file.
fs.writeFileSync(
  filename,
  JSON.stringify(result, null, 2),
  { encoding: "utf8", flag: "wx" }
);

console.log(`Created ${filename}`);
console.log("12 exact rational functions.");
console.log("Legendre and two-term checks: passed.");
