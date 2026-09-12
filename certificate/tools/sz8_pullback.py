#!/usr/bin/env python3
"""The Sz(8) polynomial over Q(s) from the Sz(8):3 polynomial f(X, t).

M = L^{Sz(8)} is a regular cyclic cubic cover of P^1_t branched at zeta3, zeta3^2, with the
conductor-13 cubic field as its fibre over t = inf: one of the two twists of the Shanks cover
by that field (Section 5 of the paper), constructed by Hilbert 90:

    T1(x) = (-4x^3 + 6x^2 + 36x - 6) / (3 (x^3 + 5x^2 - 9x - 5))      fibre over 0: x^3 - 39x - 26
    T2(x) = (x^3 + 6x^2 - 27x + 21)  / (3 (x^3 - 7x^2 + 12x - 5))     fibre over 0: x^3 - 39x - 91

(both with fibre x^3 - x^2 - 4x - 1 over inf, discriminant in t equal to (t^2 + t + 1)^2).
Which twist is M is decided by Frobenius at t = 0: for a prime p outside {2, 3, 5, 7, 13} not
dividing a denominator of f and with f(X, 0) separable modulo p, Frob_p fixes the fibre of M over
t = 0 iff Frob_p lies in Sz(8) iff no irreducible factor of f(X, 0) mod p has degree divisible by 3
(every element of Sz(8):3 outside Sz(8) has order divisible by 3, no element of Sz(8) has).  Frob_p
fixes the fibre of the twist T_i over 0 iff its cubic splits completely modulo p.  The twist whose
splitting pattern agrees with the Sz(8) test at every prime is M; the other must disagree at some
prime (a must-fire control).

Output: results/sz8_pullback.json (the decision, per-prime data, cycle types of Frob_p on the 65
roots) and results/g_poly.json: g(X, s) = den(s)^7 f(X, T(s)) in Z[1/S][s][X], the Sz(8)
polynomial over Q(s): degree 65 in X with leading coefficient den(s)^7 (monic only after dividing by it),
degree <= 21 in s.

    python3 -u tools/sz8_pullback.py --primes 40
"""
import argparse, hashlib, json, sys, time
from fractions import Fraction as F
from pathlib import Path
import flint

POLY = Path('results/f_poly.json')
OUT = Path('results/sz8_pullback.json')
GPOLY = Path('results/g_poly.json')
S = (2, 3, 5, 7, 13)
TW = {1: ([-6, 36, 6, -4], [-15, -27, 15, 3], [-26, -39, 0, 1]),
      2: ([21, -27, 6, 1], [-15, 36, -21, 3], [-91, -39, 0, 1])}   # numerator, denominator (ascending), fibre cubic over 0


def sha256(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def load_f():
    d = json.load(open(POLY))
    shape = [tuple(s) for s in d['shape']]
    coef = {tuple(int(v) for v in k.split(',')): F(v) for k, v in d['coefficients'].items()}
    return d, shape, coef


def f_at_t0_modp(coef, p):
    """f(X, 0) mod p as nmod_poly, or None if a denominator vanishes mod p."""
    c = [0]*66
    for (i, j), v in coef.items():
        if j == 0:
            if v.denominator % p == 0:
                return None
            c[i] = int(v.numerator % p) * pow(int(v.denominator % p), -1, p) % p
    return flint.nmod_poly(c, p)


def cubic_splits(cub, p):
    q = flint.nmod_poly([c % p for c in cub], p)
    return len(q.roots()) == 3


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--primes', type=int, default=40)
    a = ap.parse_args()
    t0 = time.monotonic()
    d, shape, coef = load_f()
    rows, p, n = [], 16, 0
    agree = {1: True, 2: True}
    while n < a.primes:
        p += 1
        if not flint.fmpz(p).is_prime() or p in S:
            continue
        fp = f_at_t0_modp(coef, p)
        if fp is None:
            continue
        if fp.gcd(fp.derivative()).degree() != 0:
            rows.append({'p': p, 'skipped': 'f(X,0) inseparable mod p'})
            continue
        degs = sorted(int(g.degree()) for g, e in fp.factor()[1] for _ in range(e))
        in_sz8 = not any(dg % 3 == 0 for dg in degs)
        sp = {i: cubic_splits(TW[i][2], p) for i in (1, 2)}
        for i in (1, 2):
            agree[i] = agree[i] and (sp[i] == in_sz8)
        rows.append({'p': p, 'cycle_type': degs, 'frob_in_Sz8': in_sz8, 'twist1_cubic_splits': sp[1], 'twist2_cubic_splits': sp[2]})
        n += 1
    chosen = [i for i in (1, 2) if agree[i]]
    rep = {'polynomial': str(POLY), 'f_poly_sha256': sha256(POLY), 'primes_tested': n, 'rows': rows,
           'twist_agrees_everywhere': {str(i): agree[i] for i in (1, 2)}, 'chosen_twist': chosen[0] if len(chosen) == 1 else None,
           'verdict': 'M_IDENTIFIED' if len(chosen) == 1 else ('AMBIGUOUS' if chosen else 'NO_TWIST_AGREES')}
    if rep['chosen_twist']:
        i = rep['chosen_twist']
        num, den = TW[i][0], TW[i][1]
        # g(X, s) = den(s)^7 * sum_i c_i(T(s)) X^i, c_i(t) = sum_j c_ij t^j:  c_ij num^j den^(7-j)
        Q = flint.fmpq_poly
        numq, denq = Q(num), Q(den)
        g = {}
        for (i_, j), v in coef.items():
            term = Q([flint.fmpq(v.numerator, v.denominator)]) * numq**j * denq**(7-j)
            g[i_] = g.get(i_, Q([])) + term
        gd = {str(k): [str(c) for c in v.coeffs()] for k, v in sorted(g.items())}
        maxdeg = max(v.degree() for v in g.values())
        json.dump({'group': 'Sz(8) over Q(s)', 'twist': i, 'T_numerator_ascending': num, 'T_denominator_ascending': den,
                   'definition': 'g(X, s) = den(s)^7 f(X, num(s)/den(s)); coefficients of X^i as polynomials in s (ascending, rationals)',
                   'degree_X': 65, 'max_degree_s': maxdeg, 'coefficients': gd,
                   'monic_in_X': False, 'leading_coefficient_X65': 'den(s)^7',
                   'leading_coefficient_X65_equals_den_s_7': str(g[65]) == str(denq**7),
                   'f_poly_sha256': sha256(POLY)}, open(GPOLY, 'w'), indent=1)
        rep['sz8_polynomial'] = str(GPOLY)
        rep['g_poly_sha256'] = sha256(GPOLY)
        rep['g_leading_coefficient_X65_equals_den_s_7'] = str(g[65]) == str(denq**7)
        rep['max_degree_s'] = maxdeg
    rep['runtime_seconds'] = round(time.monotonic() - t0, 1)
    json.dump(rep, open(OUT, 'w'), indent=1)
    print(json.dumps({k: v for k, v in rep.items() if k != 'rows'}, indent=1))
    for r in rows[:12]:
        print(r)


if __name__ == '__main__':
    main()
