"""Power of the two-sided 5% tests used in the report (normal approximation to the exact null
laws: P(fix>=2) Bernoulli, mean fixed count and mean moved with their exact null variances)."""
import math
from statistics import NormalDist
import mdfix_lib as L

N = NormalDist()
z = N.inv_cdf(0.975)
z90 = N.inv_cdf(0.90)
le = L.fix_law(30)
p0 = float(1 - le[0] - le[1])
mf = sum(j * float(q) for j, q in enumerate(le))
vf = sum(j * j * float(q) for j, q in enumerate(le)) - mf ** 2
ml = L.moved_law()
mm = sum(k * float(q) for k, q in enumerate(ml))
vm = sum(k * k * float(q) for k, q in enumerate(ml)) - mm ** 2
print(f'null: P(fixE>=2) = {p0:.6f}; fixE mean {mf:.6f} var {vf:.6f}; moved mean {mm:.6f} var {vm:.6f} (exact laws)')
for n in (400_000, 1_000_000):
    print(f'n = {n}:')
    for name, sd in (('P(fix>=2)', math.sqrt(p0 * (1 - p0))), ('mean fixE/fixC', math.sqrt(vf)), ('mean moved', math.sqrt(vm))):
        se = sd / math.sqrt(n)
        hw = z * se

        def power(d):
            return N.cdf(d / se - z) + N.cdf(-d / se - z)
        d90 = (z + z90) * se
        print(f'  {name:15s}: 95% CI half-width {hw:.5f}; power at true advantage = half-width: {power(hw):.3f}; '
              f'at 0.0009: {power(0.0009):.3f}; smallest advantage detected with 90% power: {d90:.5f}')
    print(f'  exact prediction, 0 hits: one-sided 95% upper bound {1 - 0.05 ** (1 / n):.2e}')
