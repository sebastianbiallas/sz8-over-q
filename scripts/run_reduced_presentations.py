#!/usr/bin/env python3
"""Verify the reduced presentations of the Sz(8) paper from the data files alone (no PARI/GP, no GAP).

Checks (all exact, in flint):
  1. P (data/P_number_field.json) is monic, irreducible of degree 65, and T(A) = 0 mod P with T the
     primitive integer form of f(X, -7/5): so Q[x]/(P) is the specialisation field K.
  2. S = F3(Y, -6/5) (from data/F3_L3P0P4.json) is irreducible of degree 65 with the stated 52-digit height
     and has the recorded root in K (data/F3_spec_field_check.json): so S also defines K.
  3. G3 (data/G3_L3P0P4_pullback.json) equals den(s+1)^7 F3(Y, 3 (T(s+1) + 1)) exactly, T the cubic of the
     paper, so G3 is the denominator-free cubic pullback of F3 shifted by s -> s + 1.
  4. The primitive integer heights of F3 and G3 recomputed from the files match the stated digits.
  5. The bridge from F3 to f (certificate/tools/bridge_check.py) reruns in full; it writes its report
     under certificate/results and must pass all gates (about 15 min on 6 workers; --skip-bridges runs
     1-4 only).

    python3 scripts/run_reduced_presentations.py --workers 6
"""
import argparse, json, math, subprocess, sys, time
from pathlib import Path
import flint

sys.set_int_max_str_digits(0)
Q, P_, Z_ = flint.fmpq, flint.fmpq_poly, flint.fmpz_poly
ROOT = Path(__file__).resolve().parents[1]
DATA, CERT = ROOT / 'data', ROOT / 'certificate'
START = time.monotonic()


def log(*a):
    print('[%7.1fs]' % (time.monotonic() - START), *a, flush=True)


def load(name):
    doc = json.loads((DATA / name).read_text())
    return {tuple(map(int, k.split(','))): Q(v) for k, v in doc['coefficients'].items() if Q(v)}, doc


def primitive(cs):
    den = 1
    for c in cs:
        den = math.lcm(den, int(c.q))
    ints = [int(c.p) * (den // int(c.q)) for c in cs]
    g = 0
    for v in ints:
        g = math.gcd(g, v)
    return [v // g for v in ints]


def height_digits(f):
    return len(str(max(abs(v) for v in primitive(list(f.values())))))


def specialise(f, u0, first=True):
    """f(., u0) as fmpq_poly in the first variable (first=True) or f(u0, .) in the second."""
    if first:
        ni = max(i for i, j in f)
        return P_([sum((v * u0**j for (i, j), v in f.items() if i == ii), Q(0)) for ii in range(ni + 1)])
    nj = max(j for i, j in f)
    return P_([sum((v * u0**i for (i, j), v in f.items() if j == jj), Q(0)) for jj in range(nj + 1)])


def irreducible65(poly):
    z = Z_(primitive(poly.coeffs()))
    fac = z.factor()[1]
    return len(fac) == 1 and fac[0][1] == 1 and fac[0][0].degree() == 65


def compose_mod(poly, A, Pq):
    acc = P_([Q(0)])
    for c in reversed(poly.coeffs()):
        acc = (acc * A + P_([c])) % Pq
    return acc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=6)
    ap.add_argument('--skip-bridges', action='store_true')
    a = ap.parse_args()
    gates = {}
    f, _ = load('f.json')
    F3, F3doc = load('F3_L3P0P4.json')
    # 1. P defines K
    Pdoc = json.loads((DATA / 'P_number_field.json').read_text())
    Pz = [int(c) for c in Pdoc['P_coefficients_ascending']]
    Pq = P_([Q(c) for c in Pz])
    A = P_([Q(c) for c in Pdoc['A_coefficients_ascending']])
    T = P_([Q(c) for c in primitive(specialise(f, Q(-7, 5)).coeffs())])
    gates['P_monic_degree_65'] = len(Pz) == 66 and Pz[-1] == 1
    gates['P_irreducible'] = irreducible65(Pq)
    gates['T_of_A_zero_mod_P'] = compose_mod(T, A, Pq).is_zero()
    gates['P_height_68_digits'] = len(str(max(abs(v) for v in Pz))) == 68
    log('1. P:', {k: gates[k] for k in gates})
    # 2. S = F3(Y, -6/5) defines K
    U0 = Q(-6, 5)
    S = specialise(F3, U0)
    spec = json.loads((DATA / 'F3_spec_field_check.json').read_text())
    root = P_([Q(c) for c in spec['root_in_K_coefficients_ascending']])
    gates['S_irreducible'] = irreducible65(S)
    gates['S_height_52_digits'] = len(str(max(abs(v) for v in primitive(S.coeffs())))) == 52
    gates['S_of_root_zero_mod_P'] = compose_mod(S, root, Pq).is_zero()
    gates['spec_file_U0_matches'] = Q(spec['U0']) == U0
    log('2. S = F3(Y, -6/5):', {k: gates[k] for k in ('S_irreducible', 'S_height_52_digits', 'S_of_root_zero_mod_P', 'spec_file_U0_matches')})
    # 3. G3 = den(s+1)^7 F3(Y, 3 (T(s+1) + 1))
    G3, G3doc = load('G3_L3P0P4_pullback.json')
    num = P_([Q(21), Q(-27), Q(6), Q(1)])          # T(s) = (s^3 + 6 s^2 - 27 s + 21) / (3 (s^3 - 7 s^2 + 12 s - 5))
    den = P_([Q(-15), Q(36), Q(-21), Q(3)])
    shift = P_([Q(1), Q(1)])                        # s -> s + 1
    num1, den1 = num(shift), den(shift)
    U = (num1 + den1) * 3                           # 3 (T + 1) = 3 (num + den) / den  -> numerator; denominator den1
    # F3(Y, U) with U = U/den1: multiply by den1^7: sum_j c_ij Y^i U^j den1^(7-j)
    dpow = [P_([Q(1)])]
    upow = [P_([Q(1)])]
    for _ in range(7):
        dpow.append(dpow[-1] * den1)
        upow.append(upow[-1] * U)
    lhs = {}
    for (i, j), v in F3.items():
        poly = upow[j] * dpow[7 - j] * v
        for k, c in enumerate(poly.coeffs()):
            if c:
                lhs[(i, k)] = lhs.get((i, k), Q(0)) + c
    lhs = {k: v for k, v in lhs.items() if v}
    gates['G3_equals_den7_F3_pullback_shifted'] = lhs == G3
    log('3. G3 pullback identity:', gates['G3_equals_den7_F3_pullback_shifted'])
    # 4. heights
    heights = {}
    for name, digits in (('F3_L3P0P4.json', 47), ('G3_L3P0P4_pullback.json', 52)):
        h = height_digits(load(name)[0])
        heights[name] = h
        gates['height_' + name] = h == digits
    log('4. heights:', heights)
    # 5. bridges
    if not a.skip_bridges:
        runs = [(['python3', '-u', 'tools/bridge_check.py', '--f', 'results/f_poly.json', '--cand', '../data/F3_bridge_psi.json', '--workers', str(a.workers), '--out', 'results/bridge_check_F3.json'], 'bridge_check_F3.json')]
        for cmd, rep in runs:
            log('+', ' '.join(cmd))
            r = subprocess.run(cmd, cwd=CERT, capture_output=True, text=True)
            ok = r.returncode == 0 and (CERT / 'results' / rep).exists() and json.loads((CERT / 'results' / rep).read_text())['all_gates_pass']
            gates['bridge_' + rep] = ok
            log('  ->', ok, (r.stdout.strip().splitlines() or [''])[-1][:120])
    allok = all(gates.values())
    out = {'gates': gates, 'all_gates_pass': allok, 'heights_recomputed': heights, 'runtime_seconds': round(time.monotonic() - START, 1)}
    (CERT / 'results' / 'reduced_presentations_check.json').write_text(json.dumps(out, indent=1) + '\n')
    print('PASS: reduced presentations' if allok else 'FAIL: ' + str([k for k, v in gates.items() if not v]), flush=True)
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main())
