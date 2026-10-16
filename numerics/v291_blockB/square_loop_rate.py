# Numerical test of the leading term of log F_{Sq LxL} (square lattice, last-erased-loop fraction)
# F_p = 4^{-l(p)} det(I - A/4)_{B\p} / det(I - A/4)_{B\v},  B = M x M box with Dirichlet outer boundary,
# p = boundary of the L x L lattice square (l(p) = 4L vertices), v = one vertex of p.
import numpy as np, scipy.sparse as sps
from scipy.sparse.linalg import splu
def logdet_IminusA4(M, removed):
    idx = -np.ones((M,M), dtype=np.int64); keep = np.ones((M,M),bool)
    for (i,j) in removed: keep[i,j] = False
    n = keep.sum(); idx[keep] = np.arange(n)
    rows=[]; cols=[]; vals=[]
    I,J = np.nonzero(keep)
    rows.append(idx[I,J]); cols.append(idx[I,J]); vals.append(np.ones(n))
    for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
        I2,J2 = I+di, J+dj
        ok = (I2>=0)&(I2<M)&(J2>=0)&(J2<M)
        I1,J1,I2,J2 = I[ok],J[ok],I2[ok],J2[ok]
        ok2 = keep[I2,J2]
        rows.append(idx[I1[ok2],J1[ok2]]); cols.append(idx[I2[ok2],J2[ok2]]); vals.append(-0.25*np.ones(ok2.sum()))
    A = sps.csc_matrix((np.concatenate(vals),(np.concatenate(rows),np.concatenate(cols))),shape=(n,n))
    lu = splu(A, permc_spec='MMD_AT_PLUS_A')
    d = lu.U.diagonal()
    return np.sum(np.log(np.abs(d)))
c = np.log(np.sqrt(2)-1)
prev=None
print(" L    M    log F_L        log F_L/(4L)   slope d(logF)/dL")
for L in [8,12,16,24,32,48,64]:
    M = 4*L+1; o = (M-L)//2
    p = [(o+i,o) for i in range(L)] + [(o+L,o+i) for i in range(L)] + [(o+L-i,o+L) for i in range(L)] + [(o,o+L-i) for i in range(L)]
    assert len(set(p)) == 4*L
    lF = -4*L*np.log(4) + logdet_IminusA4(M,p) - logdet_IminusA4(M,[p[0]])
    s = '' if prev is None else '%.5f' % ((lF-prev[1])/(L-prev[0]))
    print('%3d %4d  %12.5f   %.5f   %s' % (L, M, lF, lF/(4*L), s)); prev=(L,lF)
print('target per unit L: 4 log(sqrt2-1) = %.5f ; per perimeter vertex: log(sqrt2-1) = %.5f' % (4*c, c))
