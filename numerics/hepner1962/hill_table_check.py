#!/usr/bin/env python3
"""Hepner (1962), pp. 355-356, against Hill (1945), Phys. Rev. 67, 358, Table II (p. 362).
Spatial sub-algebra (no time index, so the x4 = it convention plays no role): translations
X1..X3, rotations X5..X7, accelerations X11..X13, dilatation X15, with c = 1.
Hill's table lists [X_a, X_b] in row a, column b (checked on [X15, X1] = -X1 with the
vector fields X1 = -d_x, X15 = x d_x + ...).  Hepner's matrices:
  X_k = t * (1/2)(1 + g5) g_k,  X_{10+k} = a * (1/2)(1 - g5) g_k  (k = 1,2,3),
  X5 = -g2 g3 / 2, X6 = -g3 g1 / 2, X7 = -g1 g2 / 2, X15 = -g5 / 2,
with Hepner's choice t = a = i/sqrt2.  We test which factors (t, a) reproduce Table II.
"""
import numpy as np
s1 = np.array([[0, 1], [1, 0]]); s2 = np.array([[0, -1j], [1j, 0]]); s3 = np.array([[1, 0], [0, -1]])
I2 = np.eye(2); Z = np.zeros((2, 2)); I4 = np.eye(4)
g = [None] + [np.block([[Z, -1j*s], [1j*s, Z]]) for s in (s1, s2, s3)] + [np.block([[I2, Z], [Z, -I2]])]
g5 = g[1] @ g[2] @ g[3] @ g[4]
C = lambda A, B: A @ B - B @ A
def gens(t, a):
    X = {}
    for k in (1, 2, 3):
        X[k] = t * 0.5 * (I4 + g5) @ g[k]
        X[10 + k] = a * 0.5 * (I4 - g5) @ g[k]
    X[5] = -0.5 * g[2] @ g[3]; X[6] = -0.5 * g[3] @ g[1]; X[7] = -0.5 * g[1] @ g[2]; X[15] = -0.5 * g5
    return X
# Hill, Table II (c = 1): (row, column) -> list of (coefficient, generator)
H = {
 (2,1):[],(3,1):[],(3,2):[],
 (5,1):[],(5,2):[(1,3)],(5,3):[(-1,2)],
 (6,1):[(-1,3)],(6,2):[],(6,3):[(1,1)],(6,5):[(-1,7)],
 (7,1):[(1,2)],(7,2):[(-1,1)],(7,3):[],(7,5):[(1,6)],(7,6):[(-1,5)],
 (11,1):[(-1,15)],(11,2):[(1,7)],(11,3):[(-1,6)],(11,5):[],(11,6):[(1,13)],(11,7):[(-1,12)],
 (12,1):[(-1,7)],(12,2):[(-1,15)],(12,3):[(1,5)],(12,5):[(-1,13)],(12,6):[],(12,7):[(1,11)],(12,11):[],
 (13,1):[(1,6)],(13,2):[(-1,5)],(13,3):[(-1,15)],(13,5):[(1,12)],(13,6):[(-1,11)],(13,7):[],(13,11):[],(13,12):[],
 (15,1):[(-1,1)],(15,2):[(-1,2)],(15,3):[(-1,3)],(15,5):[],(15,6):[],(15,7):[],(15,11):[(1,11)],(15,12):[(1,12)],(15,13):[(1,13)],
}
def check(t, a):
    X = gens(t, a); bad = []
    for (r, c), rhs in H.items():
        R = sum((co * X[k] for co, k in rhs), np.zeros((4, 4), complex))
        if not np.allclose(C(X[r], X[c]), R): bad.append((r, c))
    return bad
z0 = 1j / np.sqrt(2)
print("Hepner's choice t = a = z0 = i/sqrt2: mismatches", check(z0, z0))
for al in (2, -3, 1j, 0.5 + 0.7j):
    print(f"t = z0*{al}, a = z0/{al}: mismatches", check(z0 * al, z0 / al))
print("t = a = 1:  mismatches", len(check(1, 1)), "entries")
print("t*a must equal z0^2 = -1/2; t = a = 1/sqrt2 (product +1/2): mismatches", len(check(1/np.sqrt(2), 1/np.sqrt(2))), "entries")
