# Uniform Lanczos note (V035 candidate): numerical consistency checks

Independent checks for the referee report of 22 October 2026 on the note
"Uniform two-parameter asymptotics for Lanczos coefficients of centered uniform convolutions".
They are evidence only; none of them is used as a proof.

| File | Content |
| --- | --- |
| `beta_bspline.py` | beta_N^{[M]} by exact Gauss–Legendre discretisation of the cardinal B-spline on each knot interval + Stieltjes, long double |
| `exact_check.py` | exact rational beta_N^{[M]} (moments + Chebyshev algorithm); `exact_check_M40_N12.log` vs `stieltjes_M40_N12.log` agree to ~17 digits |
| `Fprofile.py` / `.log` | the limit profile F(alpha) = a_alpha^2/4 (mpmath, 30 digits) |
| `grid.py` / `grid.log` | beta_N^{[M]}/M^2 − F(N/M) for M = 25…400, N = tM, t = 1/4…4 (N up to 1600): error ≈ c(t)/M |
| `saddle_check.py` / `.log` | Lemma 1: M·R, M·R′, M·R″ converge for R = log g_M + M I − ½ log(M/(2πv)) |
| `q_check.py` / `.log` | second-order correction q = κ4/(8v²) − 5κ3²/(24v³); equals lim M·R |
| `Fseries.py` / `.log` | exact Taylor coefficients of F; the first five equal the top-degree coefficients of Milovanović's Conjecture 2 |
| `conj2_check.py` / `.log` | error of Conjecture 2 (five terms) behaves like m^{-4} for k = 3, 6, 10 |

Run: `python3 beta_bspline.py M N`, `python3 grid.py 100 200 400`,
`PYTHONPATH=<mpmath> python3 Fprofile.py` (likewise `saddle_check.py`, `q_check.py`), `python3 Fseries.py`.
