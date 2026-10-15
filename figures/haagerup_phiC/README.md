# Haagerup's function and the line π(k+1)/8

`fig_haagerup.py` draws φ_ℂ(k) = (π/4) k ₂F₁(½, ½; 2; k²) for 0 ≤ k ≤ 1, where the defining integral exists, and the line π(k+1)/8 for 0 ≤ k ≤ 1.6. The point k₀ = 0.81255… where they meet is taken from the certified enclosure in `numerics/hermite_catalan/haagerup_k0.log`. The figure uses the standard style: full box frame, inward ticks on all four sides, and a framed legend.

```
python3 fig_haagerup.py
```
