#!/usr/bin/env python3
"""Quick exact checks. This does not rerun the analytic monodromy certificate."""
import hashlib
import json
from pathlib import Path
import flint
from sympy.combinatorics import Permutation, PermutationGroup

ROOT = Path(__file__).resolve().parents[1]


def read(relative):
    return json.loads((ROOT / relative).read_text())


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def main():
    manifest = read('certificate/manifest.json')
    for item in manifest['files']:
        digest = hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest()
        require(digest == item['sha256'], 'File changed: ' + item['path'])
    for short, original in [('f', 'f_poly'), ('g', 'g_poly')]:
        require((ROOT / f'data/{short}.json').read_bytes() ==
                (ROOT / f'certificate/results/{original}.json').read_bytes(),
                f'Public and certificate copies of {short} differ')
    f = read('data/f.json')
    coeff = {tuple(map(int, k.split(','))): flint.fmpq(v) for k, v in f['coefficients'].items()}
    require(coeff[(65, 0)] == 1 and all(v == 0 for (i, j), v in coeff.items() if i == 64), 'Monic/trace normalization')
    g = read('data/g.json')
    Q = flint.fmpq_poly
    num, den = Q(g['T_numerator_ascending']), Q(g['T_denominator_ascending'])
    expected = {}
    for (i, j), v in coeff.items():
        expected[i] = expected.get(i, Q([])) + v * num**j * den**(7-j)
    actual = {int(i): Q([flint.fmpq(v) for v in c]) for i, c in g['coefficients'].items()}
    require(expected == actual, 'Exact pullback identity')
    require(actual[65] == den**7 and actual[65] != 1, 'Cleared leading coefficient')
    t0 = flint.fmpq(-7, 5)
    h = [sum((v * t0**j for (m, j), v in coeff.items() if m == i), flint.fmpq(0)) for i in range(66)]
    witnessed = {}
    for p, expected_degrees in [(11, [1, 1] + [7]*9), (31, [13]*5)]:
        hp = flint.nmod_poly([int(v.p) % p * pow(int(v.q) % p, -1, p) % p for v in h], p)
        require(hp.gcd(hp.derivative()).degree() == 0, f'Separability at {p}')
        degrees = sorted(int(a.degree()) for a, e in hp.factor()[1] for _ in range(e))
        require(degrees == expected_degrees, f'Frobenius degrees at {p}')
        witnessed[p] = degrees
    mon = read('data/monodromy.json')['permutations']
    group = PermutationGroup([Permutation(s) for s in mon.values()])
    require(group.order() == 87360 and group.is_transitive() and group.is_primitive(), 'Stored monodromy group')
    require(group.derived_subgroup().order() == 29120, 'Derived group order')
    print('PASS: manifest hashes, exact pullback, specialization at 11 and 31, stored permutation group.')
    print('These checks do not repeat node certification or the two monodromy loops.')


if __name__ == '__main__':
    main()
