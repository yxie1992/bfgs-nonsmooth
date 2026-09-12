#!/usr/bin/env python3
"""Independent exact-rational audit of the displayed planar example.

This is a review aid, not an external computation invoked by the paper's
proof or a substitute for its Lean correspondence. Uses only Python stdlib.
"""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json


class P:
    """Sparse rational polynomials in u, v, e."""

    def __init__(self, x=0):
        self.c = x if isinstance(x, dict) else {(0, 0, 0): Q(x)}
        self.c = {m: Q(c) for m, c in self.c.items() if c}

    def __add__(self, other):
        other = other if isinstance(other, P) else P(other)
        out = dict(self.c)
        for m, c in other.c.items():
            out[m] = out.get(m, Q(0)) + c
        return P(out)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.c.items()})

    def __sub__(self, other):
        return self + -(other if isinstance(other, P) else P(other))

    def __rsub__(self, other):
        return P(other) + -self

    def __mul__(self, other):
        other = other if isinstance(other, P) else P(other)
        out = {}
        for m, c in self.c.items():
            for n, d in other.c.items():
                k = tuple(a + b for a, b in zip(m, n))
                out[k] = out.get(k, Q(0)) + c * d
        return P(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        out = P(1)
        for _ in range(n):
            out = out * self
        return out

    def diff(self, i):
        out = {}
        for m, c in self.c.items():
            if m[i]:
                n = list(m)
                n[i] -= 1
                out[tuple(n)] = c * m[i]
        return P(out)

    def substitute(self, values):
        out = P()
        for m, c in self.c.items():
            term = P(c)
            for value, power in zip(values, m):
                term = term * value**power
            out = out + term
        return out

    def centered_box_bound(self, radius):
        """Triangle bounds on |u|,|v| <= radius; no e dependence."""
        lo = hi = self.c.get((0, 0, 0), Q(0))
        for m, c in self.c.items():
            if m == (0, 0, 0):
                continue
            if m[2]:
                raise ValueError('Unexpected e dependence')
            a = abs(c) * radius**sum(m)
            lo -= a
            hi += a
        return lo, hi


checks = {}


def equal(name, lhs, rhs):
    difference = lhs - rhs
    if difference.c:
        raise AssertionError((name, difference.c))
    checks[name] = True


u, v, e = (P({tuple(int(i == j) for i in range(3)): 1}) for j in range(3))
f = [u + u**2 + Q(1, 2)*v**2,
     v + Q(1, 2)*u**2 + Q(3, 2)*v**2,
     -u-v + Q(3, 2)*u**2 + v**2]
g = [[p.diff(j) for j in range(2)] for p in f]
equal('average_of_branches', sum(f, P()) * Q(1, 3), u**2+v**2)
for i, diagonal in enumerate([(2, 1), (1, 3), (3, 2)]):
    for j in range(2):
        for k in range(2):
            equal(f'Hessian_{i}_{j}_{k}', g[i][j].diff(k),
                  P(diagonal[j] if j == k else 0))
D = 3*(1+v-u*v)
N = [1-4*u+3*v-7*u*v, 1+2*u-3*v-u*v, 1+2*u+3*v+5*u*v]
det = (g[0][0]-g[2][0])*(g[1][1]-g[2][1]) \
    - (g[0][1]-g[2][1])*(g[1][0]-g[2][0])
equal('augmented_gradient_determinant', det, D)
equal('coefficient_sum', sum(N, P()), D)
for j in range(2):
    equal(f'weighted_gradient_{j}', sum((N[i]*g[i][j] for i in range(3)), P()), P())

radius = Q(1, 10)
bounds = {name: p.centered_box_bound(radius) for name, p in zip(['D', 'N0', 'N1', 'N2'], [D]+N)}
expected = [Q(267, 100), Q(23, 100), Q(49, 100), Q(45, 100)]
if [b[0] for b in bounds.values()] != expected:
    raise AssertionError(bounds)
checks['displayed_exact_lower_bounds'] = True

tie = v**2+v-u-Q(1, 2)*u**2
J = (g[0][0]-g[1][0])*u+(g[0][1]-g[1][1])*v
equal('radial_jump_modulo_tie', J-(Q(1, 2)*u**2-v**2), -tie)
x, z = [u, v+e, e], [u, v-e, e]
old = [p.substitute(x) for p in g[1]]
new = [p.substitute(z) for p in g[0]]
equal('predicted_decrease', 2*e*old[1], 2*e*(1+3*v+3*e))
equal('secant_curvature', -2*e*(new[1]-old[1]), 2*e*(1+2*v+4*e))
equal('value_decrease_modulo_tie', f[1].substitute(x)-f[0].substitute(z)-tie,
      e*(1+4*v)+e**2)

root = Path(__file__).resolve().parents[2]
source = root / 'paper/sections/local.tex'
print(json.dumps({
    'purpose': 'Independent author-side exact algebra review; not a proof dependency',
    'arithmetic': 'Python standard-library Fraction; sparse polynomial identities',
    'checker_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    'reviewed_source': str(source.relative_to(root)),
    'reviewed_source_sha256': sha256(source.read_bytes()).hexdigest(),
    'checks': checks,
    'box_bounds': {k: [str(x) for x in pair] for k, pair in bounds.items()},
    'result': 'PASS',
}, indent=2))
