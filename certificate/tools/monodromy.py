#!/usr/bin/env python3
"""Certified monodromy of the plane model f(X, t) = 0.

At t0, isolate all roots in acb rectangles with centres c_i and Euclidean
radii r_i. For each root, max_step tries R_i = alpha*d_i, where d_i is the
nearest-centre distance and alpha ranges over FACTORS. Retain R_i > 4*r_i.
On |X-c_i| = R_i, the monic factorization gives the lower bound
    (R_i-r_i) prod_{l != i} (|c_i-c_l|-R_i-r_l).
The exact degree-seven Taylor expansion in t bounds the increment by
    sum_{j=1}^7 h^j/j! * |d_t^j f(X,t0)|.
Each derivative is bounded using its leading coefficient and isolated
roots, retaining exact multiplicities for the seventh derivative. If a
lower derivative cannot be isolated, use a termwise bound in t based on
precomputed factorizations of its coefficient polynomials in X. Bisection
finds an admissible h for each candidate radius; choose the largest per
root, then take the minimum over roots. Strict ball inequalities certify
Rouche on every disc for every |t-t0| <= h.

Accepted endpoints are checked in ball arithmetic against this parameter
bound, and root rectangles are matched by containment in the previous
discs. Radii use the Euclidean half-diagonal (acb.rad). Proposed waypoints
are binary64; the actual displacements are certified in ball arithmetic.

The two main loops start at t=0, follow straight tails to circles about
zeta3 and its conjugate, traverse inscribed 24-sided polygons counter-
clockwise, and return. Their homotopy classes are standard meridians of
the thrice-punctured sphere. The local node proof establishes that the
other discriminant roots are unramified. Optional node loops are retained
for diagnostics; the proof driver passes --skip-nodes. The geometric group
is identified by its order, transitivity and primitivity using the
supplied degree-65 primitive-group census. Permutations compose left to
right: prod[i] = sigma2[sigma1[i]].

    python3 -u tools/monodromy.py --prec 1200 --skip-nodes
"""
import argparse, hashlib, json, math, multiprocessing as mp, pickle, sys, time
from fractions import Fraction as F
from pathlib import Path
import flint

POLY = Path('results/f_poly.json')
DISC = Path('results/discriminant.pkl')
OUT = Path('results/monodromy.json')
START = time.monotonic()
_G = {}


def log(*a):
    print('[%8.1fs]' % (time.monotonic()-START), *a, flush=True)


def sha256(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def load_f():
    d = json.load(open(POLY))
    coef = {}
    for k, v in d['coefficients'].items():
        i, j = map(int, k.split(','))
        x = F(v)
        coef.setdefault(i, [flint.fmpq(0)]*8)[j] = flint.fmpq(x.numerator, x.denominator)
    return [coef.get(i, [flint.fmpq(0)]*8) for i in range(66)]   # c_i(t) ascending in t


class Tracker:
    def __init__(self, ct, prec, verbose=False):
        self.prec = prec
        self.verbose = verbose
        flint.ctx.prec = prec
        self.ct_exact = ct
        self.ct = [[flint.arb(x) for x in row] for row in ct]      # exact rationals as arb
        self.absc = [[abs(flint.arb(x)) for x in row] for row in ct]
        self.two = flint.arb(2)

    def poly_at(self, t):
        cs = []
        for row in self.ct:
            v = flint.acb(0)
            tp = flint.acb(1)
            for j in range(8):
                if not row[j].is_zero():
                    v += flint.acb(row[j]) * tp
                tp = tp * t
            cs.append(v)
        return flint.acb_poly(cs)

    def roots(self, t):
        P = self.poly_at(t)
        rts = P.roots(tol=flint.arb(2)**(-(self.prec*2)//3), maxprec=self.prec*4)
        if len(rts) != 65:
            raise RuntimeError('root isolation returned %d roots' % len(rts))
        return rts

    def factored_increments(self):
        """C_k(x) = sum_m c_mk x^m for k = 1..7 (the coefficient of t^k in f), each factored: roots isolated
        in balls once, so that |C_k(x)| <= |lc_k| prod_j (|x - gamma_kj| + rad_kj) is a tight upper bound."""
        self.Ck = []
        for k in range(1, 8):
            cs = [self.ct_exact[m][k] for m in range(66)]
            while len(cs) > 1 and cs[-1] == 0:
                cs.pop()
            P = flint.fmpq_poly(cs)
            lc, fac = P.factor()                        # exact factorisation over Q (C_7 is a 13th power of a quartic)
            cent, rad, mult = [], [], []
            for g, e in fac:
                A = flint.acb_poly([flint.acb(x) for x in g.coeffs()])
                rts = A.roots(tol=flint.arb(2)**(-(self.prec*2)//3), maxprec=self.prec*4)
                if len(rts) != g.degree():
                    raise RuntimeError('C_%d factor: %d of %d roots isolated' % (k, len(rts), g.degree()))
                for r in rts:
                    cent.append(flint.acb(r.real.mid(), r.imag.mid()))
                    rad.append(r.rad())                      # Euclidean radius of the rectangle (upper bound)
                    mult.append(int(e))
                lc = lc * g.coeffs()[-1]**int(e)
            self.Ck.append((abs(flint.arb(lc)), cent, rad, mult, k))

    FACTORS = (0.1, 0.03, 0.01, 0.003, 0.001)

    def t_derivative_factors(self, t0):
        """For j = 1..7 the polynomial d^j F / dt^j (x, t0) = sum_k k!/(k-j)! t0^(k-j) C_k(x), factored:
        (|lc|, root centres, root radii, multiplicities).  j = 7 is 7! C_7 with C_7's exact factorisation;
        for j < 7 the roots are isolated at t0 (fallback to the termwise C_k bound if isolation fails)."""
        out = []
        for jd in range(1, 7):
            cs = []
            for m in range(66):
                v = flint.acb(0)
                for k in range(jd, 8):
                    if not self.ct[m][k].is_zero():
                        v += flint.acb(self.ct[m][k]) * (math.factorial(k) // math.factorial(k - jd)) * t0**(k - jd)
                cs.append(v)
            while len(cs) > 1 and cs[-1].is_zero():          # only exactly-zero leading coefficients are dropped
                cs.pop()
            P = flint.acb_poly(cs)
            deg = len(cs) - 1
            try:
                rts = P.roots(tol=flint.arb(2)**(-(self.prec*2)//3), maxprec=self.prec*4)
                ok = len(rts) == deg
            except Exception:                # noqa
                ok = False
            if ok:
                out.append((abs(cs[-1]), [flint.acb(r.real.mid(), r.imag.mid()) for r in rts],
                            [r.rad() for r in rts], [1]*deg, jd))
            else:
                out.append(None)
        lc7, gc7, gr7, gm7, _ = self.Ck[6]
        out.append((lc7 * math.factorial(7), gc7, gr7, gm7, 7))
        return out

    def max_step(self, t0, rts0, h_cap):
        """Largest h such that for every t with |t - t0| <= h every F_t has exactly one root in disc(c_i, R_i),
        with R_i chosen per root among FACTORS * (distance to the nearest other centre) to maximise the
        admissible step.  Rouche on |x - c_i| = R_i, with the increment expanded in t (exact, degree 7):
            |F_t(x) - F_t0(x)| = |sum_j (t - t0)^j / j!  d_t^j F(x, t0)| <= sum_j h^j / j! |d_t^j F(x, t0)|,
            |d_t^j F(x, t0)| <= |lc_j| prod_l (|c_i - g_jl| + rad_jl + R_i)^e_jl   (factored at t0),
            |F_t0(x)| >= (R_i - r_i) prod_{j != i} (|c_i - c_j| - R_i - r_j).
        Returns (h, R list) or (None, reason)."""
        if not hasattr(self, 'Ck'):
            self.factored_increments()
        cent = [flint.acb(r.real.mid(), r.imag.mid()) for r in rts0]
        rad = [r.rad() for r in rts0]                 # Euclidean radii
        n = len(cent)
        dist = [[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i+1, n):
                dist[i][j] = dist[j][i] = abs(cent[i] - cent[j])
        derivs = self.t_derivative_factors(t0)
        rho = abs(t0) + flint.arb(h_cap)
        hcap = flint.arb(h_cap)
        Rs, hs = [], []
        for i in range(n):
            dmin = min((dist[i][j] for j in range(n) if j != i), key=lambda a: a.lower())
            best = (None, None)
            for fct in self.FACTORS:
                R = dmin * fct
                if not (R > rad[i] * 4):
                    continue
                low = R - rad[i]
                for j in range(n):
                    if j != i:
                        low = low * (dist[i][j] - R - rad[j])
                # the bound is a polynomial in h: sum_j a_j h^j; find the largest h <= h_cap with sum < low
                a = []
                for jd, dv in enumerate(derivs, start=1):
                    if dv is None:
                        # termwise fallback: |d_t^j F| <= sum_k k!/(k-j)! rho^(k-j) |C_k(x)|
                        val = flint.arb(0)
                        for lc, gc, gr, gm, k in self.Ck:
                            if k < jd:
                                continue
                            prod = lc * (math.factorial(k) // math.factorial(k - jd)) * rho**(k - jd)
                            for g, gr_, e in zip(gc, gr, gm):
                                prod = prod * (abs(cent[i] - g) + gr_ + R)**e
                            val += prod
                    else:
                        lc, gc, gr, gm, _ = dv
                        val = lc
                        for g, gr_, e in zip(gc, gr, gm):
                            val = val * (abs(cent[i] - g) + gr_ + R)**e
                    a.append(val / math.factorial(jd))
                # bisection on h in [0, h_cap] (the bound is increasing in h)
                def bound(h):
                    tot = flint.arb(0)
                    hp = flint.arb(1)
                    for aj in a:
                        hp = hp * h
                        tot += aj * hp
                    return tot
                if bound(hcap).upper() < low.lower():
                    h = hcap
                else:
                    lo, hi = flint.arb(0), hcap
                    for _ in range(40):
                        midh = (lo + hi) / 2
                        if bound(midh).upper() < low.lower():
                            lo = midh
                        else:
                            hi = midh
                    h = lo
                if best[0] is None or h.lower() > best[0].lower():
                    best = (h, R)
            if best[0] is None or not (best[0].lower() > 0):
                return None, 'no admissible disc for root %d' % i
            hs.append(best[0])
            Rs.append(best[1])
        return min(hs, key=lambda a_: a_.lower()), Rs

    def match(self, rts0, rts1, Rs):
        """Label the balls rts1 by the discs disc(c_i, R_i) of rts0 (each ball inside exactly one disc)."""
        cent0 = [flint.acb(r.real.mid(), r.imag.mid()) for r in rts0]
        n = len(cent0)
        perm = [None]*n
        for k, r in enumerate(rts1):
            c = flint.acb(r.real.mid(), r.imag.mid())
            rr = r.rad()
            hits = [i for i in range(n) if (abs(c - cent0[i]) + rr).upper() < Rs[i].lower()]
            if len(hits) != 1 or perm[hits[0]] is not None:
                return None
            perm[hits[0]] = k
        return perm

    def track(self, path, rts_start, h0=0.05, tag=''):
        """path: list of acb waypoints (closed: last == first).  Returns (permutation, steps, min step).
        Predictive stepping: each step is 0.9 of the certified maximum."""
        rts = rts_start
        self.displacement_shrinks, self.displacement_ratio_max = 0, 0.0
        order = list(range(65))          # order[i] = index in current rts of the root that started as i
        steps, hmin = 0, 1.0
        Rs_start = None
        for seg in range(len(path)-1):
            a, b = path[seg], path[seg+1]
            L = math.nextafter(float(abs(b - a).upper()), math.inf)     # proposals only; every acceptance is a ball check
            s = 0.0
            while s < 1.0:
                t0 = a + (b - a) * s
                remaining = (1.0 - s) * L
                hmax, Rs = self.max_step(t0, rts, min(remaining * (1 + 1e-9), h0))
                if hmax is None:
                    raise RuntimeError('no admissible step at segment %d s=%g (%s) %s' % (seg, s, Rs, tag))
                if Rs_start is None:
                    Rs_start = Rs
                if abs(b - t0).upper() <= hmax.lower():
                    # the certified disc covers the rest of the segment (rigorous ball check): end the segment
                    t1, s1 = b, 1.0
                    h = float(abs(b - t0).upper())
                else:
                    h = min(0.9 * float(hmax.lower()), h0)
                    if h < 1e-12 * max(L, 1e-300):
                        raise RuntimeError('step underflow at segment %d s=%g %s' % (seg, s, tag))
                    s1 = min(1.0, s + h / L)
                    t1 = a + (b - a) * s1
                    # the endpoint was proposed in binary64: check the ball displacement against the certified bound and
                    # shrink the proposal until it is provably inside
                    while not (abs(t1 - t0).upper() <= hmax.lower()):
                        s1_new = s + 0.9 * (s1 - s)
                        if not (s < s1_new < s1):
                            s1_new = math.nextafter(s1, s)
                        if not (s1_new > s):
                            raise RuntimeError('displacement check cannot be met at segment %d s=%g %s' % (seg, s, tag))
                        s1 = s1_new
                        t1 = a + (b - a) * s1
                        h = float(abs(t1 - t0).upper())
                        self.displacement_shrinks += 1
                self.displacement_ratio_max = max(self.displacement_ratio_max, float(abs(t1 - t0).upper() / hmax.lower()))
                rts1 = self.roots(t1)
                perm = self.match(rts, rts1, Rs)
                if perm is None:
                    raise RuntimeError('matching failed at segment %d s=%g %s' % (seg, s, tag))
                order = [perm[o] for o in order]
                rts = rts1
                s = s1
                steps += 1
                hmin = min(hmin, h)
                if self.verbose and steps % 50 == 0:
                    log(tag, 'segment', seg, 'of', len(path)-1, 's %.3f' % s, 'step %.2e' % h, 'steps', steps)
        perm = self.match(rts_start, rts, Rs_start)
        if perm is None:
            raise RuntimeError('closing match failed ' + tag)
        inv = {v: k for k, v in enumerate(perm)}      # rts index -> start label
        sigma = [inv[order[i]] for i in range(65)]    # start label i -> start label of the disc it ends in
        return sigma, steps, hmin


def cycle_type(sigma):
    seen, ct = set(), []
    for i in range(len(sigma)):
        if i in seen:
            continue
        l, j = 0, i
        while j not in seen:
            seen.add(j)
            j = sigma[j]
            l += 1
        ct.append(l)
    return sorted(ct, reverse=True)


def circle_path(centre, radius, npts):
    pts = [centre + flint.acb(radius * math.cos(2*math.pi*k/npts), radius * math.sin(2*math.pi*k/npts)) for k in range(npts)]
    return pts + [pts[0]]


def node_prec(base, tabs):
    """Working precision near |t| = tabs: the roots scale like |t|^(7/13) and the terms of F cancel over
    about 65 * (7/13) log10|t| digits, so add that many digits (times 3.33 bits) plus a margin."""
    return base + int(65 * (7/13) * math.log2(max(tabs, 1.0))) + 300


def _init(ct, prec):
    _G['ct'], _G['prec'] = ct, prec


def _node_loop(args):
    k, cx, cy, rad_loop = args
    try:
        centre = flint.acb(flint.arb(cx), flint.arb(cy))
        tabs = float(abs(centre).mid())
        prec = node_prec(_G['prec'], tabs)
        T = Tracker(_G['ct'], prec)
        path = circle_path(centre, rad_loop, 24)
        rts = T.roots(path[0])
        sigma, steps, hmin = T.track(path, rts, h0=rad_loop / 4, tag='node %d' % k)
        return k, cycle_type(sigma) == [1]*65, steps, hmin, None
    except Exception as e:                      # noqa
        return k, False, 0, None, str(e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prec', type=int, default=1200)
    ap.add_argument('--workers', type=int, default=10)
    ap.add_argument('--skip-nodes', action='store_true')
    ap.add_argument('--only-nodes', action='store_true', help='run the node loops only and merge into an existing report')
    ap.add_argument('--nodes', type=int, default=10**9)
    ap.add_argument('--out', default=str(OUT))
    a = ap.parse_args()
    out = Path(a.out)
    ct = load_f()
    disc = pickle.load(open(DISC, 'rb'))
    sys.set_int_max_str_digits(0)
    assert all(r['certified'] for r in disc['roots']) and disc.get('f_poly_sha256') == sha256(POLY), 'node boxes not all certified / pickle mismatch'
    nodes = [(float(F(r['re'])), float(F(r['im'])), (10.0**r['rad_exp10'] if r['rad_exp10'] > -300 else 0.0)) for r in disc['roots']]
    flint.ctx.prec = a.prec
    T = Tracker(ct, a.prec, verbose=True)
    z3 = complex(-0.5, math.sqrt(3)/2)
    pts = [complex(x, y) for x, y, _ in nodes]
    special = [z3, z3.conjugate()]
    report = json.load(open(out)) if out.exists() else {}
    report.update({'prec_bits': a.prec, 'nodes': len(nodes), 'f_poly_sha256': sha256(POLY), 'disc_pkl_sha256': sha256(DISC),
                   'python_flint_version': flint.__version__})
    report.setdefault('gates', {})
    # ---- (b) the two standard loops from b = 0
    def min_dist(z, excl=None):
        return min(abs(z - w) for w in pts + special if w != excl)
    for name, z in (() if a.only_nodes else (('gamma_1', z3), ('gamma_2', z3.conjugate()))):
        eps = min(min_dist(z, z) / 3, 0.1)
        # tail from 0 to the circle, then circle counter-clockwise from the entry point, then back
        entry = z - eps * (z / abs(z))
        npts = 24
        ang0 = math.atan2((entry - z).imag, (entry - z).real)
        circ = [z + eps * complex(math.cos(ang0 + 2*math.pi*k/npts), math.sin(ang0 + 2*math.pi*k/npts)) for k in range(npts+1)]
        path = [complex(0, 0)] + circ + [complex(0, 0)]
        # distance of the tail from the nodes (report only)
        d_tail = min(abs(w - complex(0, 0) - (z - 0) * max(0.0, min(1.0, ((w - 0) * (z - 0).conjugate()).real / abs(z)**2))) for w in pts)
        pathb = [flint.acb(p.real, p.imag) for p in path]
        t0 = time.monotonic()
        rts0 = T.roots(pathb[0])
        sigma, steps, hmin = T.track(pathb, rts0, h0=0.05, tag=name)
        ctype = cycle_type(sigma)
        report[name] = {'eps': eps, 'tail_min_distance_to_nodes': d_tail, 'steps': steps, 'min_step': hmin, 'cycle_type': ctype,
                        'permutation': sigma, 'displacement_shrinks': T.displacement_shrinks,
                        'max_displacement_over_certified_step': T.displacement_ratio_max, 'seconds': round(time.monotonic()-t0, 1)}
        report['gates'][name + '_cycle_type_3^20_1^5'] = (ctype == [3]*20 + [1]*5)
        log(name, 'cycle type', ctype, 'steps', steps, 'min step', hmin, '%.1fs' % (time.monotonic()-t0))
    if 'gamma_1' in report and 'gamma_2' in report:
      s1, s2 = report['gamma_1']['permutation'], report['gamma_2']['permutation']
      prod = [s2[s1[i]] for i in range(65)]
      report['gamma_1_gamma_2_cycle_type'] = cycle_type(prod)
      report['gates']['product_cycle_type_13^5'] = (cycle_type(prod) == [13]*5)
      # group
      from sympy.combinatorics import Permutation, PermutationGroup
      Gp = PermutationGroup([Permutation(s1), Permutation(s2)])
      order = Gp.order()
      report['group_order'] = int(order)
      report['group_transitive'] = bool(Gp.is_transitive())
      report['group_primitive'] = bool(Gp.is_primitive())
      report['gates']['group_order_87360'] = (int(order) == 87360)
      report['gates']['group_primitive'] = report['group_primitive']
      log('group order', order, 'transitive', report['group_transitive'], 'primitive', report['group_primitive'])
    # ---- (a) node loops
    if not a.skip_nodes:
        jobs = []
        for k, (x, y, r) in enumerate(nodes[:a.nodes]):
            z = complex(x, y)
            rl = min(min_dist(z, z) / 3, 0.05 * max(1.0, abs(z)))
            assert rl > 10 * r, ('node loop radius below the node ball radius', k, rl, r)
            jobs.append((k, x, y, rl))
        t0 = time.monotonic()
        res = []
        with mp.get_context('fork').Pool(a.workers, initializer=_init, initargs=(ct, a.prec)) as pool:
            for k, ident, steps, hmin, err in pool.imap_unordered(_node_loop, jobs):
                res.append((k, ident, steps, hmin, err))
                if len(res) % 25 == 0 or err:
                    el = time.monotonic() - t0
                    log('node loops', len(res), 'of', len(jobs), 'identity so far', sum(1 for r in res if r[1]), 'rate %.2f/s' % (len(res)/el),
                        'ETA %.0fs' % ((len(jobs)-len(res)) * el / len(res)), ('error: %s' % err) if err else '')
        res.sort()
        report['node_loops'] = {'count': len(res), 'identity': sum(1 for r in res if r[1]), 'errors': [(k, e) for k, _, _, _, e in res if e],
                                'total_steps': sum(r[2] for r in res), 'min_step': min((r[3] for r in res if r[3] is not None), default=None)}
        report['gates']['all_node_loops_identity'] = all(r[1] for r in res) and len(res) == len(nodes)
    required_sections = ['gamma_1', 'gamma_2']
    if not a.skip_nodes:
        required_sections.append('node_loops')
    report['all_gates_pass'] = all(report['gates'].values()) and all(k in report for k in required_sections)
    report['runtime_seconds'] = round(time.monotonic() - START, 1)
    json.dump(report, open(out, 'w'), indent=1)
    log('ALL GATES PASS' if report['all_gates_pass'] else 'SOME GATES FAIL', {k: v for k, v in report['gates'].items() if not v})


if __name__ == '__main__':
    main()
