#!/usr/bin/env python3
"""Exact bridge between the certified f(X, t) and a candidate P(Y, t) through a plane relation
Psi(X, Y) = 0 (for example ../data/F3_bridge_psi.json).

Proposition.  Let f, P in Q[t][.] be monic of degree 65 and irreducible over Q(t), Psi in Q[X, Y].  Put
  Q_a(X, t) = Res_Y(P(Y, t), Psi(X, Y)),   Q_b(Y, t) = Res_X(f(X, t), Psi(X, Y)).
If f | Q_a, f^2 does not divide Q_a, P | Q_b and P^2 does not divide Q_b (in Q(t)[X] resp. Q(t)[Y]), then
for the roots X_k of f and y_i of P over an algebraic closure of Q(t) the relation Psi(X_k, y_i) = 0 is a
bijection {X_k} <-> {y_i} (each X_k is a simple root of Q_a = prod_i Psi(X, y_i), so it pairs with exactly
one y_i, and symmetrically), it is Galois-equivariant, hence the partner y of X_1 is fixed by
Gal(/Q(t)(X_1)) and lies in E = Q(t)(X_1) = Q(C).  As P is irreducible of degree 65 = [E : Q(t)],
E = Q(t)(y) and P is the minimal polynomial of the generator y of Q(C)/Q(t) with Psi(X, y) = 0.

Exactness.  The divisibility f | Q_a in Q[t][X] is the vanishing of the remainder R = Q_a mod f (f monic in
X), a polynomial of t-degree at most deg_X(Q_a)*theta_f + deg_t(Q_a), theta_f = max b/(65-a) over the terms
X^a t^b of f (every term of f has weight a*theta_f + b <= 65*theta_f, and division by f does not raise the
weight; for f, theta_f = 7/13 from the pole-order shape).  It is verified at more rational
points t0 than that bound, each time exactly in Q[X]: Q_a(X, t0) = Res_Y(P(Y, t0), Psi(X, Y)) (flint
fmpq_mpoly resultant) reduced modulo f(X, t0).  Specialisation commutes with division by a monic
polynomial.  Non-divisibility by f^2 and irreducibility of P are checked at a single t0 (they can only
improve under specialisation).  Symmetrically for Q_b.  Report: results/bridge_check_<m>_<n>.json.

    python3 -u tools/bridge_check.py --cand ../data/F3_bridge_psi.json --workers 8
"""
import argparse, hashlib, json, multiprocessing as mp, sys, time
from pathlib import Path
import flint

sys.set_int_max_str_digits(0)
Q, P_ = flint.fmpq, flint.fmpq_poly
START = time.monotonic()
_G = {}


def log(*a):
    print('[%7.1fs]' % (time.monotonic() - START), *a, flush=True)


def load_bivar(path, key='coefficients'):
    doc = json.loads(Path(path).read_text())
    src = doc[key] if key == 'coefficients' else doc['psi']['coefficients']
    return {tuple(map(int, k.split(','))): Q(v) for k, v in src.items() if Q(v)}, doc


def degs(f):
    return max(i for i, j in f), max(j for i, j in f)


def specialise(f, t0):
    """f(., t0) as fmpq_poly (ascending in the first index)."""
    ni = degs(f)[0]
    return P_([sum((v * t0**j for (i, j), v in f.items() if i == ii), Q(0)) for ii in range(ni + 1)])


def _init(f, P, psi):
    _G['f'], _G['P'], _G['psi'] = f, P, psi
    ctx = flint.fmpq_mpoly_ctx.get(('X', 'Y'), 'lex')
    _G['ctx'] = ctx
    _G['Psi'] = ctx.from_dict({(a, b): v for (a, b), v in psi.items()})


def _check_point(args):
    """(direction, t0) -> (t0, remainder_zero, extra) where extra = (Q nonzero, multiplicity-one) for the probe."""
    direction, t0, probe = args
    t0 = Q(t0)
    ctx, Psi = _G['ctx'], _G['Psi']
    if direction == 'a':
        Pt = specialise(_G['P'], t0)                     # in Y
        ft = specialise(_G['f'], t0)                     # in X
        Pm = ctx.from_dict({(0, k): c for k, c in enumerate(Pt.coeffs()) if c})
        R = Pm.resultant(Psi, 'Y')                       # polynomial in X
        d = R.to_dict()
        assert all(b == 0 for (a, b) in d), 'resultant not univariate'
        Rx = P_([d.get((k, 0), Q(0)) for k in range(max((a for a, b in d), default=0) + 1)]) if d else P_([])
        rem = Rx % ft
        extra = None
        if probe:
            quo = Rx // ft
            g = quo.gcd(ft)
            extra = {'Q_nonzero': not Rx.is_zero(), 'multiplicity_one': (not quo.is_zero()) and g.degree() == 0,
                     'deg_Q': Rx.degree()}
        return int(t0.p), rem.is_zero(), extra
    else:
        ft = specialise(_G['f'], t0)                     # in X
        Pt = specialise(_G['P'], t0)                     # in Y
        fm = ctx.from_dict({(k, 0): c for k, c in enumerate(ft.coeffs()) if c})
        R = fm.resultant(Psi, 'X')                       # polynomial in Y
        d = R.to_dict()
        assert all(a == 0 for (a, b) in d), 'resultant not univariate'
        Ry = P_([d.get((0, k), Q(0)) for k in range(max((b for a, b in d), default=0) + 1)]) if d else P_([])
        rem = Ry % Pt
        extra = None
        if probe:
            quo = Ry // Pt
            g = quo.gcd(Pt)
            extra = {'Q_nonzero': not Ry.is_zero(), 'multiplicity_one': (not quo.is_zero()) and g.degree() == 0,
                     'deg_Q': Ry.degree()}
        return int(t0.p), rem.is_zero(), extra


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--f', default='results/f_poly.json')
    ap.add_argument('--cand', required=True)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--points', type=int, default=None, help='override the number of evaluation points (smoke tests only)')
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    f, fdoc = load_bivar(a.f)
    P, cdoc = load_bivar(a.cand)
    psi, _ = load_bivar(a.cand, key='psi')
    assert cdoc['psi']['all_reconstructed'] and cdoc['all_reconstructed'], 'candidate/psi not fully reconstructed'
    yaff = cdoc['psi'].get('y_affine')
    if yaff:
        # Psi is stated for y_red = (y - b)/a: P := a^-65 P_can(aY + b, t) exactly (parameter unchanged)
        sys.path.insert(0, 'tools')
        from affine_search import apply_transform
        aa, bb = Q(yaff['a']), Q(yaff['b'])
        P = apply_transform(P, aa, bb, Q(1), Q(0), 65)
        log('candidate transformed to the affine-reduced generator: a=%s b=%s' % (aa, bb))
    m, n = cdoc['divisor']['m'], cdoc['divisor']['n']
    out = Path(a.out or f'results/bridge_check_{m}_{n}.json')
    nX, dtf = degs(f)
    nY, dtP = degs(P)
    dXpsi, dYpsi = max(x for x, y in psi), max(y for x, y in psi)
    assert nX == 65 and nY == 65 and f[(65, 0)] == 1 and P[(65, 0)] == 1
    # degree bounds for the remainders.  Weight argument: with theta = max_{a<65} b/(65-a) over the terms X^a t^b of
    # the monic divisor D, every term of D has weight a*theta + b <= 65*theta, so one division step replaces a term by
    # terms of no larger weight; the remainder's weight is at most the dividend's, and a term X^a t^b of the remainder
    # has b <= its weight.  Dividend weight <= deg_X(Q)*theta + deg_t(Q).
    from fractions import Fraction as Fr
    def theta(D, n):
        return max((Fr(j, n - i) for (i, j) in D if i < n), default=Fr(0))
    th_f, th_P = theta(f, 65), theta(P, 65)
    degX_Qa, degt_Qa = dXpsi * nY, dtP * dYpsi
    bound_a = int(degX_Qa * th_f + degt_Qa)
    degY_Qb, degt_Qb = dYpsi * nX, dtf * dXpsi
    bound_b = int(degY_Qb * th_P + degt_Qb)
    log('weights: theta_f = %s, theta_P = %s' % (th_f, th_P))
    npts_a = (a.points or bound_a + 1)
    npts_b = (a.points or bound_b + 1)
    log('degrees: f (%d,%d) P (%d,%d) Psi (X %d, Y %d); remainder t-degree bounds a=%d b=%d; points %d / %d' %
        (nX, dtf, nY, dtP, dXpsi, dYpsi, bound_a, bound_b, npts_a, npts_b))
    # irreducibility of P over Q(t): at t0 = 0 (then 1, 2 if reducible there)
    irr = None
    for t0 in range(0, 5):
        Pt = specialise(P, Q(t0))
        den = 1
        for c in Pt.coeffs():
            den = den * int(c.q) // __import__('math').gcd(den, int(c.q))
        Pz = flint.fmpz_poly([int(c.p) * (den // int(c.q)) for c in Pt.coeffs()])
        fac = Pz.factor()
        if len(fac[1]) == 1 and fac[1][0][1] == 1 and fac[1][0][0].degree() == 65:
            irr = t0
            break
    log('P(Y, t0) irreducible over Q at t0 =', irr)
    report = {'candidate': a.cand, 'sha256': {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in [a.f, a.cand]},
              'divisor': cdoc['divisor'], 'degrees': {'f': [nX, dtf], 'P': [nY, dtP], 'Psi_X': dXpsi, 'Psi_Y': dYpsi},
              'remainder_t_degree_bounds': {'a': bound_a, 'b': bound_b, 'theta_f': str(th_f), 'theta_P': str(th_P),
                                            'argument': 'weight a*theta+b is not raised by division by the monic divisor; bound = deg_X(Q)*theta + deg_t(Q)'},
              'points': {'a': npts_a, 'b': npts_b},
              'P_irreducible_at_t0': irr, 'workers': a.workers,
              'P_used': ('a^-65 P_can(aY + b, t) with (a, b) = (%s, %s) from %s' % (yaff['a'], yaff['b'], yaff.get('source'))) if yaff else 'coefficients of the candidate file'}
    gates = {'P_irreducible_over_Q_t': irr is not None,
             'points_exceed_remainder_degree_bounds': (npts_a > bound_a and npts_b > bound_b)}
    if not gates['points_exceed_remainder_degree_bounds']:
        log('WARNING: fewer points than the degree bounds (smoke mode); the verdict cannot be a proof')
    with mp.get_context('fork').Pool(a.workers, initializer=_init, initargs=(f, P, psi)) as pool:
        for direction, npts in (('a', npts_a), ('b', npts_b)):
            t0 = time.monotonic()
            tasks = [(direction, k, k == 0) for k in range(npts)]
            zero = 0
            fails = []
            probe = None
            done = 0
            for (tk, ok, extra) in pool.imap_unordered(_check_point, tasks, chunksize=4):
                done += 1
                zero += ok
                if not ok:
                    fails.append(tk)
                if extra is not None:
                    probe = extra
                if done % 200 == 0 or done == npts:
                    el = time.monotonic() - t0
                    log('direction %s: %d/%d points, remainder zero at %d, failures %d, rate %.1f/s, ETA %.0f s' %
                        (direction, done, npts, zero, len(fails), done / el, (npts - done) / (done / el)))
            gates[f'{direction}_remainder_zero_at_all_points'] = (zero == npts)
            gates[f'{direction}_Q_nonzero'] = bool(probe and probe['Q_nonzero'])
            gates[f'{direction}_multiplicity_one'] = bool(probe and probe['multiplicity_one'])
            report[direction] = {'points': npts, 'remainder_zero': zero, 'failures': fails[:20], 'probe_t0_0': probe,
                                 'seconds': round(time.monotonic() - t0, 1)}
    report['gates'] = gates
    report['all_gates_pass'] = all(gates.values())
    report['conclusion'] = ('P is the minimal polynomial over Q(t) of a generator y of Q(C) with Psi(X, y) = 0 (proposition in the docstring)'
                            if report['all_gates_pass'] else 'bridge NOT established')
    report['runtime_seconds'] = round(time.monotonic() - START, 1)
    out.write_text(json.dumps(report, indent=1) + '\n')
    log('wrote', out, 'all_gates_pass', report['all_gates_pass'])
    print('BRIDGE_DONE all_gates_pass=%s' % report['all_gates_pass'], flush=True)
    return 0 if report['all_gates_pass'] else 1


if __name__ == '__main__':
    sys.exit(main())
