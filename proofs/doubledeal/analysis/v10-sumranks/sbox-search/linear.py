"""Quick linear-style check: correlation between simple card-count features of the input grid and of
SumRanks(input) over N random decks. Features: per row, count of each suit (16); per row, sum of ranks (4);
per column, count of each suit (52); per column, number of red cards (13). Reports the largest |corr| between
any input feature and any output feature, and the largest among 'same feature' pairs, vs the noise level."""
import sys, numpy as np, sb
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
rng = np.random.default_rng(3)
X = np.ascontiguousarray(np.argsort(rng.random((N, 52)), axis=1).astype(np.uint8))
Y = np.zeros_like(X); sb.L.sr_batch(N, X, Y)
def feats(G):
    G = G.reshape(-1, 4, 13).astype(np.int64); s = G // 13; r = G % 13 + 1
    F, names = [], []
    for i in range(4):
        for k in range(4): F.append((s[:, i, :] == k).sum(1)); names.append(f"row{i} #{'CHSD'[k]}")
    for i in range(4): F.append(r[:, i, :].sum(1)); names.append(f"row{i} ranksum")
    for i in range(4): F.append((r[:, i, :] * (13 - np.arange(13))).sum(1) % 13); names.append(f"row{i} weighted-ranksum mod 13")
    for j in range(13):
        for k in range(4): F.append((s[:, :, j] == k).sum(1)); names.append(f"col{j} #{'CHSD'[k]}")
    for j in range(13): F.append(((s[:, :, j] == 1) | (s[:, :, j] == 3)).sum(1)); names.append(f"col{j} #red")
    return np.array(F, dtype=np.float64), names
FX, names = feats(X); FY, _ = feats(Y)
def z(A): A = A - A.mean(1, keepdims=True); return A / A.std(1, keepdims=True)
Cm = z(FX) @ z(FY).T / N
noise = 1 / np.sqrt(N)
print(f"N = {N}; noise sd of a correlation ~ {noise:.2g} (so |corr| < ~{5*noise:.2g} is noise)")
diag = np.abs(np.diag(Cm)); o = np.argsort(-diag)
print("largest same-feature correlations (feature in vs same feature out):")
for i in o[:12]: print(f"  {names[i]:30s} corr {Cm[i, i]:+.4f}")
A = np.abs(Cm); np.fill_diagonal(A, 0); idx = np.dstack(np.unravel_index(np.argsort(-A.ravel()), A.shape))[0][:8]
print("largest cross-feature correlations (in feature -> different out feature):")
for i, j in idx: print(f"  {names[i]:30s} -> {names[j]:30s} corr {Cm[i, j]:+.4f}")
# single-card position bias: how often does a card stay in the same cell / same row / same column
same_cell = (X == Y).mean(); 
pos = lambda G: np.argsort(G, axis=1)
PX, PY = pos(X), pos(Y)
print(f"a given card ends in the same cell: {same_cell:.4f} (uniform 1/52 = {1/52:.4f}); same row: {((PX//13)==(PY//13)).mean():.4f} (uniform 0.25); same column: {((PX%13)==(PY%13)).mean():.4f} (uniform {1/13:.4f})")
