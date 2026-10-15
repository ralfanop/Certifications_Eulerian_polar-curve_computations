# Figure 1: Haagerup's function phi_C(k) and the line pi(k+1)/8, meeting at k0.
# Style as in the author's TJM figures: full box, inward ticks on all four sides,
# matplotlib default sans-serif (DejaVu) and mathtext, framed legend.
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.special import hyp2f1
plt.rcParams.update({'pdf.fonttype': 42, 'font.size': 10,
                     'xtick.direction': 'in', 'ytick.direction': 'in',
                     'xtick.top': True, 'ytick.right': True})
k = np.linspace(0, 1.0, 800)            # the integral (26) is defined only for |k| <= 1
phi = np.pi/4*k*hyp2f1(.5, .5, 2, k*k)  # phi_C(1) = 1
kl = np.linspace(0, 1.6, 800)
line = np.pi/8*(kl+1)
k0 = 0.8125578588214724
y0 = np.pi/8*(k0+1)
fig, ax = plt.subplots(figsize=(6.69, 3.0))
ax.plot(k, phi, color='tab:blue', lw=1.5, label=r'Haagerup $\varphi_{\mathbb{C}}(k)$')
ax.plot(kl, line, color='red', lw=1.5, label=r'$\pi(k+1)/8$')
ax.plot([k0, k0], [0, y0], color='0.4', lw=0.8, ls=':')
ax.plot(k0, y0, 'o', ms=5, mfc='white', mec='black', mew=1.0, zorder=5)
ax.annotate(r'$k_0=0.81255\ldots$', xy=(k0, y0), xytext=(k0+0.08, y0-0.32),
            arrowprops=dict(arrowstyle='-', color='0.4', lw=0.6))
ax.set_xlim(0, 1.6); ax.set_ylim(0, 1.6)
ax.set_xticks(np.arange(0, 1.61, 0.2)); ax.set_yticks(np.arange(0, 1.61, 0.2))
ax.set_xlabel(r'$k$')
ax.legend(loc='upper center')
fig.tight_layout(pad=0.3)
fig.savefig('fig_haagerup.pdf'); fig.savefig('fig_haagerup.png', dpi=160)
