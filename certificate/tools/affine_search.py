#!/usr/bin/env python3
"""Reproducible bounded affine search on the certified polynomials f and g.

Objective.  For a polynomial with rational coefficients c_ij (X^i t^j), the primitive integer
height H_prim (clear one common denominator, divide out the content) equals the projective Weil
height of the coefficient vector:  log H_prim = sum over places v of max_ij log|c_ij|_v.  It is
invariant under multiplying the equation by a scalar, so it is the quantity compared here.

Transformations.  X = a Y + b, t = c U + d with a, c in Q*, b, d in Q; the result is divided by
a^65 so it stays monic (for g the leading coefficient den(s)^7 is kept and the height is projective
anyway).  With a = prod p^alpha_p, c = prod p^gamma_p the new coefficient is c_ij a^(i-65) c^j and

  log H(alpha, gamma) = max_ij (log|c_ij| + (i-65) A + j C)
                      + sum_p log p * max_ij (-v_p(c_ij) - (i-65) alpha_p - j gamma_p),
  A = sum_p alpha_p log p,  C = sum_p gamma_p log p,

a convex piecewise-linear function of the integer vector (alpha, gamma).  For fixed (b, d) its
minimum is an exact mixed-integer linear program (scipy.optimize.milp, HiGHS); the returned optimum
is re-scored exactly and compared with its +-1 neighbours.  A prime outside the support of the
coefficients can only increase the height, so the prime set is the support plus {2,3,5,7,11,13}.

Translations b, d are searched greedily on p-adic digits: for each prime p of the set and each level
k in [KMIN, KMAX], the candidates b + delta p^k (delta = 0..p-1) are scored by the exact torus optimum
and the best strict improvement is kept; passes repeat until no digit improves.  The trace-centred
and zero translations are included as starting points.  Optionally (--mobius) the X- and
t-reversals (X -> x0 + 1/X', t -> t0 + 1/U) at the current centres are tried as well; these lose
monicity and are reported separately.

Everything accepted is recomputed exactly: the transformation is inverted and the inverse
substitution must return the source polynomial.  Bounds, candidate counts and timings are recorded.

    python3 -u tools/affine_search.py --target f --out results/affine_f.json
    python3 -u tools/affine_search.py --target g --out results/affine_g.json
"""
import argparse, hashlib, json, math, sys, time
from pathlib import Path
import numpy as np
import flint
from scipy.optimize import milp, LinearConstraint, Bounds

sys.set_int_max_str_digits(0)
Q, P_ = flint.fmpq, flint.fmpq_poly
START = time.monotonic()
NX = 65
BASE_PRIMES = [2, 3, 5, 7, 11, 13]


def log(*a):
    print('[%7.1fs]' % (time.monotonic() - START), *a, flush=True)


# ------------------------------------------------------------------ polynomials as dicts
def load_target(target, file=None):
    if file is not None:
        p = Path(file)
        doc = json.loads(p.read_text())
        f = {tuple(map(int, k.split(','))): Q(v) for k, v in doc['coefficients'].items() if Q(v)}
        return f, p, None
    if target in ('f', 'h'):
        p = Path('results/f_poly.json')
        doc = json.loads(p.read_text())
        f = {tuple(map(int, k.split(','))): Q(v) for k, v in doc['coefficients'].items() if Q(v)}
        if target == 'h':
            t0 = Q(-7, 5)
            f = {(i, 0): sum((v * t0**j for (m, j), v in f.items() if m == i), Q(0)) for i in range(NX + 1)}
            f = {k: v for k, v in f.items() if v}
        return f, p, None
    p = Path('results/g_poly.json')
    doc = json.loads(p.read_text())
    g = {(int(i), j): Q(v) for i, vv in doc['coefficients'].items() for j, v in enumerate(vv) if Q(v)}
    return g, p, doc


def degs(f):
    return max(i for i, j in f), max(j for i, j in f)


def shift(f, b, d):
    """f(Y + b, U + d) exactly."""
    ni, nj = degs(f)
    out = f
    if b != 0:
        tmp = {}
        for j in range(nj + 1):
            col = P_([out.get((i, j), 0) for i in range(ni + 1)])
            if col.is_zero():
                continue
            col = col(P_([b, 1]))
            tmp.update({(i, j): v for i, v in enumerate(col.coeffs()) if v})
        out = tmp
    if d != 0:
        tmp = {}
        for i in range(ni + 1):
            row = P_([out.get((i, j), 0) for j in range(nj + 1)])
            if row.is_zero():
                continue
            row = row(P_([d, 1]))
            tmp.update({(i, j): v for j, v in enumerate(row.coeffs()) if v})
        out = tmp
    return out


def scale(f, a, c, ni):
    """a^-ni f(aY, cU)."""
    return {(i, j): v * a**(i - ni) * c**j for (i, j), v in f.items()}


def reverse_x(f, ni):
    """X = 1/X': X'^ni f(1/X', t)  (coefficient of X^i goes to X'^(ni-i))."""
    return {(ni - i, j): v for (i, j), v in f.items()}


def reverse_t(f, nj):
    return {(i, nj - j): v for (i, j), v in f.items()}


def exact_height(f):
    den = 1
    for v in f.values():
        den = math.lcm(den, int(v.q))
    ints = [int(v.p) * (den // int(v.q)) for v in f.values()]
    g = 0
    for v in ints:
        g = math.gcd(g, v)
    H = max(abs(v) for v in ints) // g
    return {'primitive_integer_height_digits': len(str(H)), 'primitive_integer_height_bits': H.bit_length(),
            'log10_height': round(math.log10(H), 3), 'nonzero_terms': len(f),
            'rational_height_digits': max(max(len(str(abs(int(v.p)))), len(str(int(v.q)))) for v in f.values()),
            'denominator_lcm_digits': len(str(den)), 'degree_X': degs(f)[0], 'degree_parameter': degs(f)[1]}


# ------------------------------------------------------------------ torus optimum (MILP)
def vp(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def support_primes(f, extra=BASE_PRIMES, bound=200):
    """Small primes of the denominators plus BASE_PRIMES, and the remaining denominator cofactors refined
    into a pairwise coprime base (a composite base element is exact for the height only when its prime
    factors always occur together; the accepted polynomial is re-scored exactly in any case)."""
    ps = set(extra)
    bigs = []
    for v in f.values():
        q = int(v.q)
        for p in range(2, bound):
            if q % p == 0:
                ps.add(p)
                while q % p == 0:
                    q //= p
        if q > 1 and q not in bigs:
            bigs.append(q)
    base = []
    for q in bigs:                      # coprime refinement
        stack = [q]
        while stack:
            x = stack.pop()
            if x == 1:
                continue
            for i, b in enumerate(base):
                g = math.gcd(x, b)
                if g > 1 and g != b:
                    base[i] = g
                    stack.append(b // g)
                    x //= g
                    break
                if g == b:
                    x //= b
                    stack.append(x)
                    x = 1
                    break
            else:
                base.append(x)
    base = sorted({b for b in base if b > 1})
    return sorted(ps) + base


def torus_optimum(f, primes, ni, abound, gbound):
    """Exact minimiser of log10 H over alpha_p in [-abound, abound], gamma_p in [-gbound, gbound]."""
    keys = list(f.keys())
    I = np.array([i - ni for i, j in keys], dtype=float)
    J = np.array([j for i, j in keys], dtype=float)
    L = np.array([math.log10(abs(int(v.p))) - math.log10(int(v.q)) for v in (f[k] for k in keys)])
    V = {p: np.array([vp(int(f[k].p), p) - vp(int(f[k].q), p) for k in keys], dtype=float) for p in primes}
    lp = {p: math.log10(p) for p in primes}
    n = len(keys)
    m = len(primes)
    # variables: alpha_1..alpha_m, gamma_1..gamma_m (integer), z_1..z_m, z_inf (continuous)
    nv = 2 * m + m + 1
    cobj = np.zeros(nv)
    for k, p in enumerate(primes):
        cobj[2 * m + k] = lp[p]
    cobj[-1] = 1.0
    rows, lo, hi = [], [], []
    # z_p >= -V_p - I alpha_p - J gamma_p   <=>  I alpha_p + J gamma_p + z_p >= -V_p
    for k, p in enumerate(primes):
        Ablk = np.zeros((n, nv))
        Ablk[:, k] = I
        Ablk[:, m + k] = J
        Ablk[:, 2 * m + k] = 1.0
        rows.append(Ablk)
        lo.append(-V[p])
        hi.append(np.full(n, np.inf))
    # z_inf >= L + I A + J C, A = sum alpha_p log p:  -I sum(lp alpha) - J sum(lp gamma) + z_inf >= L
    Ablk = np.zeros((n, nv))
    for k, p in enumerate(primes):
        Ablk[:, k] = -I * lp[p]
        Ablk[:, m + k] = -J * lp[p]
    Ablk[:, -1] = 1.0
    rows.append(Ablk)
    lo.append(L)
    hi.append(np.full(n, np.inf))
    A = np.vstack(rows)
    cons = LinearConstraint(A, np.concatenate(lo), np.concatenate(hi))
    lb = np.concatenate([np.full(m, -abound), np.full(m, -gbound), np.full(m + 1, -np.inf)])
    ub = np.concatenate([np.full(m, abound), np.full(m, gbound), np.full(m + 1, np.inf)])
    integrality = np.concatenate([np.ones(2 * m), np.zeros(m + 1)])
    res = milp(cobj, constraints=cons, bounds=Bounds(lb, ub), integrality=integrality,
               options={'disp': False, 'mip_rel_gap': 0.0})
    if not res.success or res.x is None:
        res = milp(cobj, constraints=cons, bounds=Bounds(lb, ub), integrality=integrality,
                   options={'disp': False, 'mip_rel_gap': 1e-6, 'time_limit': 60.0})
    if not res.success or res.x is None:
        log('MILP failed (%s); candidate skipped' % getattr(res, 'message', '?'))
        return float('inf'), [0]*m, [0]*m
    alpha = [int(round(x)) for x in res.x[:m]]
    gamma = [int(round(x)) for x in res.x[m:2 * m]]

    def score(al, ga):
        Aa = sum(a * lp[p] for a, p in zip(al, primes))
        Cc = sum(g * lp[p] for g, p in zip(ga, primes))
        s = float(np.max(L + I * Aa + J * Cc))
        for k, p in enumerate(primes):
            s += lp[p] * float(np.max(-V[p] - I * al[k] - J * ga[k]))
        return s
    best = (score(alpha, gamma), alpha, gamma)
    # +-1 neighbourhood re-scoring (guards the float tolerance of the LP)
    for k in range(m):
        for da in (-1, 1):
            al = alpha[:]; al[k] += da
            if abs(al[k]) <= abound:
                s = score(al, gamma)
                if s < best[0] - 1e-9:
                    best = (s, al, gamma)
        for dg in (-1, 1):
            ga = gamma[:]; ga[k] += dg
            if abs(ga[k]) <= gbound:
                s = score(alpha, ga)
                if s < best[0] - 1e-9:
                    best = (s, alpha, ga)
    return best


def scale_from(alpha, gamma, primes):
    a, c = Q(1), Q(1)
    for al, ga, p in zip(alpha, gamma, primes):
        a *= Q(p)**al
        c *= Q(p)**ga
    return a, c


# ------------------------------------------------------------------ greedy translation search
def evaluate(f0, b, d, primes, ni, abound, gbound):
    f1 = shift(f0, b, d)
    s, al, ga = torus_optimum(f1, primes, ni, abound, gbound)
    return s, al, ga


def greedy(f0, primes, ni, abound, gbound, kmin, kmax, b0, d0, do_t, log_prefix):
    b, d = b0, d0
    best, al, ga = evaluate(f0, b, d, primes, ni, abound, gbound)
    log(log_prefix, 'start b=%s d=%s log10H=%.3f' % (b, d, best))
    ncand = 1
    improved = True
    npass = 0
    while improved:
        improved = False
        npass += 1
        for which in (['b', 'd'] if do_t else ['b']):
            for p in primes:
                if p > 200:
                    continue            # large base elements enter the scaling MILP only
                levels = range(kmin, kmax + 1) if p <= 13 else range(max(kmin, -4), min(kmax, 2) + 1)
                for k in levels:
                    step = Q(p)**k
                    for delta in range(1, p):
                        for sgn in (1, -1):
                            nb, nd = b, d
                            if which == 'b':
                                nb = b + sgn * delta * step
                            else:
                                nd = d + sgn * delta * step
                            s, a2, g2 = evaluate(f0, nb, nd, primes, ni, abound, gbound)
                            ncand += 1
                            if s < best - 1e-6:
                                best, al, ga, b, d = s, a2, g2, nb, nd
                                improved = True
                                log(log_prefix, 'pass %d improve: %s=%s (p=%d k=%d) log10H=%.3f' % (npass, which, nb if which == 'b' else nd, p, k, best))
        log(log_prefix, 'pass %d done: candidates so far %d, best %.3f' % (npass, ncand, best))
    return best, al, ga, b, d, ncand, npass


def apply_transform(f0, a, b, c, d, ni):
    """a^-ni f0(aY + b, cU + d)."""
    return scale(shift(f0, b, d), a, c, ni)


def inverse_check(f0, f1, a, b, c, d, ni):
    """f0(X, t) == a^ni f1((X - b)/a, (t - d)/c)."""
    back = apply_transform(f1, 1 / a, -b / a, 1 / c, -d / c, ni)
    return back == f0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--target', choices=['f', 'g', 'h'], default='f')
    ap.add_argument('--out', default=None)
    ap.add_argument('--abound', type=int, default=16)
    ap.add_argument('--gbound', type=int, default=8)
    ap.add_argument('--kmin', type=int, default=-6)
    ap.add_argument('--kmax', type=int, default=12)
    ap.add_argument('--mobius', action='store_true')
    ap.add_argument('--no-t', action='store_true', help='do not translate the parameter')
    ap.add_argument('--file', default=None, help='any JSON with a coefficients dict "i,j" -> rational (overrides --target source)')
    args = ap.parse_args()
    out = Path(args.out or f'results/affine_{args.target}.json')
    f0, src, gdoc = load_target(args.target, args.file)
    ni, nj = degs(f0)
    assert ni == NX
    primes = support_primes(f0)
    base = exact_height(f0)
    log('target', args.target, 'from', src, 'degrees', (ni, nj), 'terms', len(f0), 'primes', primes)
    log('source primitive height digits', base['primitive_integer_height_digits'])
    do_t = (nj > 0) and not args.no_t
    if nj == 0:
        args.gbound = 0   # no parameter: the parameter scale is meaningless
    # starting points: zero and trace-centred translation
    c64 = f0.get((64, 0), Q(0))
    starts = [(Q(0), Q(0))]
    if c64 != 0 and f0.get((ni, 0), Q(0)) == 1 and all(j == 0 for (i, j) in f0 if i == ni):
        starts.append((-c64 / 65, Q(0)))          # trace-centred start: only meaningful for a monic polynomial
    results = []
    for b0, d0 in starts:
        r = greedy(f0, primes, ni, args.abound, args.gbound, args.kmin, args.kmax, b0, d0, do_t, 'affine')
        results.append(('affine', r))
    results.sort(key=lambda x: x[1][0])
    kind, (best, al, ga, b, d, ncand, npass) = results[0]
    a, c = scale_from(al, ga, primes)
    f1 = apply_transform(f0, a, b, c, d, ni)
    assert inverse_check(f0, f1, a, b, c, d, ni)
    m1 = exact_height(f1)
    log('best affine: a=%s b=%s c=%s d=%s -> digits %d (score %.3f)' % (a, b, c, d, m1['primitive_integer_height_digits'], best))
    mobius = None
    if args.mobius:
        # X-reversal at the accepted centre: X = b + 1/X' ; polynomial X'^65 f(b + 1/X', t), then re-optimise
        fr = reverse_x(shift(f0, b, Q(0)), ni)
        r = greedy(fr, primes, ni, args.abound, args.gbound, args.kmin, args.kmax, Q(0), Q(0), do_t, 'mobius-X')
        sr, alr, gar, br, dr, ncr, npr = r
        ar, cr = scale_from(alr, gar, primes)
        f2 = apply_transform(fr, ar, br, cr, dr, ni)
        m2 = exact_height(f2)
        mobius = {'X_reversal_centre': str(b), 'then': {'a': str(ar), 'b': str(br), 'c': str(cr), 'd': str(dr)},
                  'metrics': m2, 'candidates': ncr, 'monic': f2.get((ni, 0)) is not None and all(j == 0 for (i, j) in f2 if i == ni),
                  'note': 'X = b + 1/(a X" + b"), non-monic in general; reported for comparison only'}
        log('mobius-X: digits %d' % m2['primitive_integer_height_digits'])
        if do_t:
            ft = reverse_t(shift(f0, Q(0), d), nj)
            r = greedy(ft, primes, ni, args.abound, args.gbound, args.kmin, args.kmax, Q(0), Q(0), do_t, 'mobius-t')
            st, alt, gat, bt, dt, nct, npt = r
            at, ct = scale_from(alt, gat, primes)
            f3 = apply_transform(ft, at, bt, ct, dt, ni)
            m3 = exact_height(f3)
            mobius['t_reversal'] = {'t_reversal_centre': str(d), 'then': {'a': str(at), 'b': str(bt), 'c': str(ct), 'd': str(dt)},
                                    'metrics': m3, 'candidates': nct,
                                    'note': 't = d + 1/U, multiplied by U^deg_t; leading X-coefficient becomes U^deg_t'}
            log('mobius-t: digits %d' % m3['primitive_integer_height_digits'])
    ident = {'f': 'F(Y,U) = a^-65 f(aY+b, cU+d)', 'g': 'G(Y,s\') = a^-65 g(aY+b, c s\'+d)', 'h': 'H(Y) = a^-65 h(aY+b)'}[args.target]
    report = {
        'target': args.target,
        'source': {str(src): hashlib.sha256(src.read_bytes()).hexdigest()},
        'objective': 'primitive integer height = projective Weil height of the coefficient vector (exact)',
        'search': {'primes': [str(p) for p in primes], 'alpha_bound': args.abound, 'gamma_bound': args.gbound,
                   'digit_levels': [args.kmin, args.kmax], 'starts': [[str(x), str(y)] for x, y in starts],
                   'translate_parameter': do_t, 'candidates_evaluated': sum(r[1][5] for r in results),
                   'passes': [r[1][6] for r in results], 'runtime_seconds': round(time.monotonic() - START, 1)},
        'accepted': {'a': str(a), 'b': str(b), 'c': str(c), 'd': str(d), 'identity': ident,
                     'inverse_substitution_verified': True,
                     'alpha': dict(zip(map(str, primes), al)), 'gamma': dict(zip(map(str, primes), ga))},
        'metrics': {'source': base, 'accepted': m1},
        'mobius': mobius,
        'coefficients': {f'{i},{j}': str(v) for (i, j), v in sorted(f1.items()) if v},
    }
    if gdoc is not None:
        num, den = P_(gdoc['T_numerator_ascending']), P_(gdoc['T_denominator_ascending'])
        num2, den2 = num(P_([d, c])), den(P_([d, c]))
        report['accepted']['T_after_s_change'] = {'numerator_ascending': [str(x) for x in num2.coeffs()],
                                                  'denominator_ascending': [str(x) for x in den2.coeffs()],
                                                  'meaning': "t = T(s) = T(c s' + d) = num'(s')/den'(s')"}
    out.write_text(json.dumps(report, indent=1) + '\n')
    doc = json.loads(out.read_text())
    f_back = {tuple(map(int, k.split(','))): Q(v) for k, v in doc['coefficients'].items()}
    assert f_back == f1 and exact_height(f_back) == m1
    log('wrote', out, 'digits source=%d accepted=%d' % (base['primitive_integer_height_digits'], m1['primitive_integer_height_digits']))
    print('AFFINE_DONE target=%s digits=%d' % (args.target, m1['primitive_integer_height_digits']), flush=True)


if __name__ == '__main__':
    main()
