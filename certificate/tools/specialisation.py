#!/usr/bin/env python3
"""A rational specialisation of the Sz(8) polynomial with Galois group Sz(8) over Q.

g(X, 0) = den(0)^7 f(X, T2(0)) with T2(0) = -7/5.  For a prime p outside {2, 3, 5, 7, 13} (the denominators
of f(X, -7/5) are 5^a 13^b; the primes dividing the group order are skipped although Dedekind's theorem
only needs separability) at which f(X, -7/5) is separable modulo p, the factorisation pattern
modulo p is the cycle type of a Frobenius element of Gal(f(X, -7/5) / Q) on the 65 roots.  Since
f(X, -7/5) is separable (its reduction at such a p is), s = 0 is unramified in the Galois closure of
g over Q(s), and Gal(f(X, -7/5) / Q) is the decomposition group there: a subgroup H of Gal(g / Q(s)) =
Sz(8) (the certified generic group, KB C44) acting on the 65 roots.  A Frobenius of cycle type 1^2 7^9
has order 7 and one of type 13^5 has order 13, so 91 divides |H|; no maximal subgroup of Sz(8) has
order divisible by 91 (orders 448, 52, 20, 14; results/primitive65.json), hence H = Sz(8).
Control: every observed cycle type must be one of Sz(8)'s (1^65, 1 2^32, 1 4^16, 5^13, 1^2 7^9, 13^5);
a type with a length divisible by 3 would contradict the generic group.

Output: results/specialisation.json.

    python3 tools/specialisation.py --pmax 400
"""
import argparse, hashlib, json, sys, time
from fractions import Fraction as F
from pathlib import Path
import flint

POLY = Path('results/f_poly.json')
GPOLY = Path('results/g_poly.json')
PRIM = Path('results/primitive65.json')
OUT = Path('results/specialisation.json')
T0 = F(-7, 5)
SKIP = (2, 3, 5, 7, 13)          # the denominators 5, 13, and the other primes dividing |Sz(8):3| (not needed by Dedekind, avoided for the record)
SZ8_TYPES = {(1,)*65, (2,)*32 + (1,), (4,)*16 + (1,), (5,)*13, (7,)*9 + (1, 1), (13,)*5}


def sha256(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pmax', type=int, default=400)
    a = ap.parse_args()
    sys.set_int_max_str_digits(0)
    t0 = time.monotonic()
    d = json.load(open(POLY))
    coef = {tuple(map(int, k.split(','))): F(v) for k, v in d['coefficients'].items()}
    c = [F(0)]*66
    for (i, j), v in coef.items():
        c[i] += v * T0**j
    assert c[65] == 1 and c[64] == 0
    # tie to g(X, s) at s = 0
    gd = json.load(open(GPOLY))
    den0 = sum(F(x) * F(0)**k for k, x in enumerate(gd['T_denominator_ascending']))
    num0 = sum(F(x) * F(0)**k for k, x in enumerate(gd['T_numerator_ascending']))
    assert num0 / den0 == T0
    g0 = [sum(F(x) * F(0)**k for k, x in enumerate(gd['coefficients'].get(str(i), ['0']))) for i in range(66)]
    g_matches = all(g0[i] == den0**7 * c[i] for i in range(66))
    denoms = set()
    for v in c:
        q = v.denominator
        for p in (5, 13):
            while q % p == 0:
                q //= p
        denoms.add(q)
    denominators_5_13_only = denoms == {1}
    rows, witness7, witness13, sep_prime, all_in_sz8 = [], None, None, None, True
    for p in range(2, a.pmax + 1):
        if not flint.fmpz(p).is_prime() or p in SKIP:
            continue
        cp = [int(v.numerator % p) * pow(int(v.denominator % p), -1, p) % p for v in c]
        fp = flint.nmod_poly(cp, p)
        if fp.gcd(fp.derivative()).degree() != 0:
            rows.append({'p': p, 'skipped': 'inseparable mod p'})
            continue
        sep_prime = sep_prime or p
        degs = tuple(sorted((int(g.degree()) for g, e in fp.factor()[1] for _ in range(e)), reverse=True))
        in_sz8 = degs in SZ8_TYPES
        all_in_sz8 = all_in_sz8 and in_sz8
        order = 1
        for dg in set(degs):
            order = order * dg // __import__('math').gcd(order, dg)
        rows.append({'p': p, 'cycle_type': list(degs), 'frobenius_order': order, 'is_Sz8_cycle_type': in_sz8})
        if order == 7 and witness7 is None:
            witness7 = p
        if order == 13 and witness13 is None:
            witness13 = p
    prim = json.load(open(PRIM))
    maxorders = prim['facts']['Sz8_maximal_subgroup_orders']
    gates = {'g_at_s0_equals_den0_7_times_f_at_t0': g_matches, 'f_spec_denominators_only_5_13': denominators_5_13_only,
             'f_spec_separable_over_Q': sep_prime is not None, 'order_7_frobenius_witness': witness7 is not None,
             'order_13_frobenius_witness': witness13 is not None,
             'no_maximal_subgroup_of_Sz8_has_order_divisible_by_91': all(o % 91 for o in maxorders),
             'all_frobenius_cycle_types_are_Sz8_types': all_in_sz8}
    rep = {'f_poly_sha256': sha256(POLY), 'g_poly_sha256': sha256(GPOLY), 'specialisation': {'s': 0, 't': str(T0)},
           'first_separable_prime': sep_prime, 'order_7_witness_prime': witness7, 'order_13_witness_prime': witness13,
           'Sz8_maximal_subgroup_orders': maxorders, 'gates': gates, 'all_gates_pass': all(gates.values()),
           'conclusion': ('Gal(f(X, -7/5) / Q) = Gal(g(X, 0) / Q) = Sz(8), given Gal(g / Q(s)) = Sz(8) (KB C44): the decomposition group '
                          'at s = 0 contains elements of orders 7 and 13, and no proper subgroup of Sz(8) does.') if all(gates.values())
           else 'SOME GATES FAIL',
           'rows': rows, 'runtime_seconds': round(time.monotonic() - t0, 1)}
    json.dump(rep, open(OUT, 'w'), indent=1)
    print(json.dumps({k: v for k, v in rep.items() if k != 'rows'}, indent=1))
    print([r for r in rows if r.get('p') in (witness7, witness13)])


if __name__ == '__main__':
    main()
