# Figures of manuscript 13 (Gegenbauer–Fock)

Vector PDF figures (TikZ/PGFPlots, Type 1 fonts, no raster images), their data, the scripts that produce
the data, and the certificates for the figures whose captions state numerical facts.

| Figure | Statement of 13 | Source | Data | Certificate |
| --- | --- | --- | --- | --- |
| 1 | Corollary 4.2 | `fig1_eulerian_resolvent.tex` | `fig1_im.dat`, `fig1_re.dat` (closed forms) | not needed |
| 2 | Proposition 4.4 and the sphere average | `fig2_sphere.tex` | `fig2_density_d*.dat` (closed forms) | not needed |
| 3 | Theorems 7.2, 7.3, Proposition 7.5, Corollary 7.4 | `fig3_intertwining.tex` | `fig3_gram.dat` | `fig3_gram_certificate.txt` |
| 4 | Theorem 8.1 | `fig4_tail.tex` | `fig4_tail_*.dat`, `fig4_bound_*.dat` | `fig4_tail_certificate.txt` |

Certificates:

* `fig3_gram_certificate.txt` (from `cert_fig3_gram.py`): the normalized Gram matrix
  ⟨F_m, F_n⟩/(‖F_m‖‖F_n‖), 0 ≤ m, n ≤ 11, of F_n = C_{1/2,α} P_n with α = 1/16 (c = 4). Exact rational partial
  sums of ⟨F_m, F_n⟩ = Σ_k (c^k/k!) M_k(P_m) M_k(P_n) up to K = 90, tail ≤ 55 c^K/K! < 6·10⁻⁸³ (|M_k| ≤ 1, e⁴ < 55);
  rational square-root bounds. Certified: the entries with m + n odd are exactly 0 (parity), the entries with
  m + n even are positive and decrease away from the diagonal, and the largest off-diagonal entry is the one at
  (m, n) = (0, 2), in [0.753174039953, 0.753174039953] to twelve digits (printed 0.7531… in the caption).
* `fig4_tail_certificate.txt` (from `make_fig1_fig4_data.py`): for λ = 1/2, α ∈ {1/4, 1, 4} and 0 ≤ N ≤ 20, the tail
  ‖C − C_N‖²_HS = Σ_{n≥N} cⁿ/[(2n+1) n!] is enclosed by exact rational partial sums and a rigorous remainder,
  and the inequality of Theorem 8.1, tail ≤ e^c c^N/N!, is checked exactly at all 63 points.

Reproduce: `python3 make_fig1_fig4_data.py; python3 make_fig2_fig3_data.py; python3 cert_fig3_gram.py`, then
`pdflatex` each `fig*.tex` (requires `style.tex`). Python 3 with NumPy and SciPy (closed-form curves only);
all certified quantities use `fractions.Fraction`.
