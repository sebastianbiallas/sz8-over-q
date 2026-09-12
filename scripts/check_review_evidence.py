#!/usr/bin/env python3
"""Check the printed specialization and the root-conjugation consistency relation.

This verifies new evidence cited in the revised exposition. It does not repeat
the generic monodromy continuation or the two-variable resultant bridge.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import time

import flint
from sympy.combinatorics import Permutation, PermutationGroup
from run_reduced_presentations import compose_mod, height_digits, irreducible65, load, primitive, specialise

ROOT = Path(__file__).resolve().parents[1]


def conjugation(poly):
    """Identify conjugate roots by unique overlaps of certified root enclosures."""
    flint.ctx.prec = 1200
    roots = flint.acb_poly([flint.acb(c) for c in poly.coeffs()]).roots(
        tol=flint.arb(2)**-800, maxprec=4800)
    if len(roots) != poly.degree() or any(roots[i].overlaps(roots[j])
                                         for i in range(len(roots)) for j in range(i)):
        raise AssertionError('Root enclosures do not isolate every root separately')
    c = []
    for r in roots:
        hits = [j for j, other in enumerate(roots) if r.conjugate().overlaps(other)]
        if len(hits) != 1:
            raise AssertionError('Conjugate-root matching is ambiguous')
        c.append(hits[0])
    if any(c[c[i]] != i for i in range(len(c))):
        raise AssertionError('Conjugation is not an involution')
    return c


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='optional JSON report')
    args = parser.parse_args()
    start = time.monotonic()
    f, _ = load('f.json')
    F3, _ = load('F3_L3P0P4.json')
    doc = json.loads((ROOT / 'data/P_s1_number_field.json').read_text())
    cs = [int(c) for c in doc['P_coefficients_ascending']]
    P1 = flint.fmpq_poly(cs)
    A = flint.fmpq_poly([flint.fmpq(c) for c in doc['A_coefficients_ascending']])
    F4 = specialise(F3, flint.fmpq(4))
    gates = {
        'P1_monic_integral_degree65': len(cs) == 66 and cs[-1] == 1,
        'P1_height43': len(str(max(abs(c) for c in cs))) == 43,
        'F4_height48': len(str(max(abs(c) for c in primitive(F4.coeffs())))) == 48,
        'P1_irreducible': irreducible65(P1),
        'F4_irreducible': irreducible65(F4),
        'F4_of_A_zero_mod_P1': compose_mod(F4, A, P1).is_zero(),
        'f_height249': height_digits(f) == 249,
        'F3_height47': height_digits(F3) == 47,
        'term_counts': len(f) == 472 and len(F3) == 318,
    }
    leading = {(65, 0): 1, (64, 0): 78, (63, 0): 2652, (62, 0): 48880,
               (61, 0): 457290, (60, 0): 296636, (60, 1): -13312}
    gates['F3_printed_leading_terms'] = {k: v for k, v in F3.items() if k[0] >= 60} == leading
    # The resultant verifier uses the affine-reduced candidate in the original t coordinate.
    sys.path.insert(0, str(ROOT / 'certificate/tools'))
    from affine_search import apply_transform
    candidate, bridge_doc = load('F3_bridge_psi.json')
    affine = bridge_doc['psi']['y_affine']
    Q = flint.fmpq
    bridge_poly = apply_transform(candidate, Q(affine['a']), Q(affine['b']), Q(1), Q(0), 65)
    public_poly = apply_transform(F3, Q(1), Q(0), Q(3), Q(3), 65)
    gates['public_F3_matches_bridge_candidate'] = bridge_poly == public_poly
    C7 = flint.fmpq_poly([f.get((i, 7), Q(0)) for i in range(66)])
    C6 = flint.fmpq_poly([f.get((i, 6), Q(0)) for i in range(66)])
    factors7 = C7.factor()[1]
    gates['infinity_quartic_power13'] = len(factors7) == 1 and factors7[0][0].degree() == 4 and factors7[0][1] == 13
    if gates['infinity_quartic_power13']:
        quartic = factors7[0][0]
        gates['infinity_four_smooth_points'] = quartic.gcd(quartic.derivative()).degree() == 0 and quartic.gcd(C6).degree() == 0
    else:
        gates['infinity_four_smooth_points'] = False
    gates['infinity_cusp_newton_edge'] = all(7*i + 13*j <= 455 for i, j in f) and {
        (i, j) for i, j in f if 7*i + 13*j == 455} == {(65, 0), (52, 7)}
    patterns = {}
    for p, expected in [(11, [13]*5), (17, [1, 1]+[7]*9)]:
        reduced = flint.nmod_poly([int(c.p) % p * pow(int(c.q), -1, p) % p for c in F4.coeffs()], p)
        factors = sorted(g.degree() for g, e in reduced.factor()[1] for _ in range(e))
        gates[f'F4_separable_mod_{p}'] = reduced.gcd(reduced.derivative()).degree() == 0
        gates[f'F4_factors_mod_{p}'] = factors == expected
        patterns[str(p)] = factors
    # The source table prints paired rows (i, a_i, j, a_j).
    table = (ROOT / 'sections/09-polynomial.tex').read_text()
    printed = {}
    for row in re.findall(r'^\s*(\d+) & \$(-?\d+)\$ & (\d+) & \$(-?\d+)\$', table, re.M):
        i, ai, j, aj = map(int, row)
        if i in printed or j in printed:
            raise AssertionError('Repeated exponent in printed table')
        printed.update({i: ai, j: aj})
    gates['printed_coefficients_match'] = printed == dict(enumerate(cs))
    c = conjugation(specialise(f, flint.fmpq(0)))
    mon = json.loads((ROOT / 'data/monodromy.json').read_text())['permutations']
    s1, s2 = mon['gamma_1'], mon['gamma_2']
    inv = [0]*65
    for i, v in enumerate(s1):
        inv[v] = i
    gates['sigma2_conjugation_identity'] = s2 == [c[inv[c[i]]] for i in range(65)]
    group = PermutationGroup([Permutation(s1), Permutation(s2)])
    gates['conjugation_in_G'] = group.contains(Permutation(c))
    gates['conjugation_one_fixed_point'] = sum(i == v for i, v in enumerate(c)) == 1
    for name, poly in [('h', specialise(f, flint.fmpq(-7, 5))), ('P1', P1)]:
        involution = conjugation(poly)
        gates[name + '_signature_1_32'] = sum(i == v for i, v in enumerate(involution)) == 1
    report = {'gates': gates, 'all_gates_pass': all(gates.values()), 'F4_frobenius_patterns': patterns,
              'root_conjugation_at_t0': c, 'runtime_seconds': round(time.monotonic() - start, 2),
              'input_sha256': {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                               for p in ['data/f.json', 'data/F3_L3P0P4.json', 'data/P_s1_number_field.json',
                                         'data/monodromy.json', 'sections/09-polynomial.tex']}}
    if args.out:
        args.out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    if not report['all_gates_pass']:
        raise SystemExit(1)
    print('PASS: printed polynomial, field isomorphism, Frobenius patterns, heights, signatures, conjugation.')


if __name__ == '__main__':
    main()
