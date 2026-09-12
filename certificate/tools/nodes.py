#!/usr/bin/env python3
"""Every root of the node polynomial S is an ordinary node of the plane model with two
unramified branches, so the normalised cover is unramified there (no loop needed).

Argument.  D(t) = disc_X f = c (t^2 + t + 1)^40 S(t)^2 exactly with S squarefree (tools/discriminant.py),
so at a root t* of S the discriminant vanishes to order exactly 2.  If F(., t*) has exactly one repeated
root xb, of multiplicity exactly 2 (F_XX(xb, t*) != 0), then near (xb, t*) Weierstrass preparation writes
F = unit * (X^2 + a(t) X + b(t)) whose discriminant a^2 - 4b has order exactly 2 at t*: (t - t*)^2 u(t)
with u a unit, so the two roots (-a +- (t - t*) sqrt(u)) / 2 are single-valued analytic functions of t
and the local monodromy is the identity.

Certificate per node, self-contained (ball arithmetic at this stage's own precision):
  0. the parameter box T: the exact rational box shipped by the discriminant stage (centre re, im and
     half-width 10^e) rebuilt outward and widened to half-width |t| 2^-(prec - extra) + 10^e, then
     proved by an interval Newton step on S (N(T) = m - S(m)/S'(T) inside T, 0 not in S'(T)) to contain
     exactly one root t* of S.  The 342 boxes are shown pairwise disjoint on outward float64 bounds, so
     they hold 342 distinct roots of S, i.e. all of them.  Nothing certified by the discriminant stage is
     assumed here except the exactness of S.
  1. the 64 roots of F_X(., t), t in T, are isolated in pairwise disjoint balls b_l, each re-certified by
     an interval Newton step valid for every t in T (so every F_X(., t) has exactly one root in each b_l,
     and the 64 balls hold all roots of F_X(., t*));
  2. F(b_l, T) excludes 0 for all l but one (l0): a repeated root of F(., t*) is a root of F_X(., t*),
     hence lies in b_l0; it exists because D(t*) = 0; and b_l0 holds only one root of F_X(., t*), so the
     repeated root is unique;
  3. F_XX(b_l0, T) excludes 0: the repeated root has multiplicity exactly 2.
Output: results/nodes.json (bound to the polynomial file and the discriminant pickle by sha256).

    python3 -u tools/nodes.py --workers 10
"""
import argparse, hashlib, json, math, multiprocessing as mp, pickle, sys, time
from fractions import Fraction as F
from pathlib import Path
import flint

POLY = Path('results/f_poly.json')
DISC = Path('results/discriminant.pkl')
OUT = Path('results/nodes.json')
START = time.monotonic()
EXTRA_LADDER = (64, 128, 256, 512, 1024)
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
    return [coef.get(i, [flint.fmpq(0)]*8) for i in range(66)]


def node_prec(tabs):
    return 1500 + int(1.5 * 65 * (7/13) * math.log2(max(tabs, 1.0))) + 500


def fmpq_of_decimal(s):
    fr = F(s)
    return flint.fmpq(fr.numerator, fr.denominator)


def poly_at(ct, T):
    """F(., t) for t in the ball T, as acb_poly with ball coefficients."""
    cs = []
    for row in ct:
        v = flint.acb(0)
        tp = flint.acb(1)
        for j in range(8):
            if row[j] != 0:
                v += flint.acb(row[j]) * tp
            tp = tp * T
        cs.append(v)
    return flint.acb_poly(cs)


def outward_float_bounds(T):
    """[lo_re, hi_re, lo_im, hi_im] floats with the box T inside (one ulp outward of the nearest rounding)."""
    return [math.nextafter(float(T.real.lower()), -math.inf), math.nextafter(float(T.real.upper()), math.inf),
            math.nextafter(float(T.imag.lower()), -math.inf), math.nextafter(float(T.imag.upper()), math.inf)]


def certify_S_box(Sq, re, im, e, prec):
    """Box T at precision prec containing the exact shipped box, proved to contain exactly one root of S.
    Returns (T, extra) or (None, None)."""
    flint.ctx.prec = prec
    Ap = flint.acb_poly([flint.acb(x) for x in Sq])
    Apd = Ap.derivative()
    mre, mim = flint.arb(fmpq_of_decimal(re)), flint.arb(fmpq_of_decimal(im))
    m = flint.acb(mre, mim)
    scale = abs(m).upper()
    Am = Ap(m)
    for extra in EXTRA_LADDER:
        rT = scale * flint.arb(2)**(-(prec - extra)) + flint.arb(10)**e
        E = flint.arb(0, 1) * rT
        T = flint.acb(mre + E, mim + E)
        dB = Apd(T)
        if not dB.is_finite() or dB.contains(0):
            continue
        NB = m - Am / dB
        if NB.is_finite() and T.real.contains(NB.real) and T.imag.contains(NB.imag):
            return T, extra
    return None, None


def _node(args):
    k, re, im, e = args
    ct, Sq = _G['ct'], _G['S']
    try:
        tabs = math.hypot(float(F(re)), float(F(im)))
        prec = node_prec(tabs)
        T, extra = None, None
        for _ in range(3):
            T, extra = certify_S_box(Sq, re, im, e, prec)
            if T is not None:
                break
            prec = int(prec * 1.5)
        if T is None:
            return k, False, 'S interval Newton failed on the parameter box', prec, None
        flint.ctx.prec = prec
        info = {'prec': prec, 'extra_bits': extra, 'box_bounds': outward_float_bounds(T)}
        P = poly_at(ct, T)
        PX = P.derivative()
        PXX = PX.derivative()
        rts = PX.roots(tol=flint.arb(2)**(-prec//3), maxprec=prec*4)
        if len(rts) != 64:
            return k, False, 'F_X roots isolated: %d' % len(rts), prec, info
        balls = []
        mids = [flint.acb(r.real.mid(), r.imag.mid()) for r in rts]
        for li, r in enumerate(rts):
            mid = mids[li]
            sep = min(float(abs(mid - mids[lj]).lower()) for lj in range(64) if lj != li)
            rr = max(float(r.rad()), 1e-300)
            ok = False
            PXm = PX(mid)
            cand = []
            x = rr * 4
            while x < sep / 4:
                cand.append(x)
                x *= 1e50
            cand.append(sep / 4)
            for rb in cand:
                b = flint.acb(flint.arb(mid.real, rb), flint.arb(mid.imag, rb))
                d2 = PXX(b)
                if not d2.is_finite() or d2.contains(0):
                    continue
                NB = mid - PXm / d2
                if NB.is_finite() and b.real.contains(NB.real) and b.imag.contains(NB.imag):
                    ok = True
                    break
            if not ok:
                return k, False, 'interval Newton failed on an F_X root', prec, info
            balls.append(b)
        for i in range(64):
            for j in range(i+1, 64):
                if not ((balls[i] - balls[j]).abs_lower() > 0):
                    return k, False, 'F_X root balls not disjoint', prec, info
        cand = [l for l in range(64) if P(balls[l]).contains(0)]
        if len(cand) != 1:
            return k, False, 'F vanishes on %d candidate balls' % len(cand), prec, info
        l0 = cand[0]
        if PXX(balls[l0]).contains(0):
            return k, False, 'F_XX not provably nonzero at the double root', prec, info
        return k, True, None, prec, info
    except Exception as ex:                       # noqa
        return k, False, 'exception: %s' % ex, 0, None


def _init(ct, Sq):
    _G['ct'], _G['S'] = ct, Sq


def boxes_disjoint(bounds):
    """Pairwise disjointness of closed float boxes [lo_re, hi_re, lo_im, hi_im] (exact float comparisons)."""
    n = len(bounds)
    for i in range(n):
        a = bounds[i]
        for j in range(i+1, n):
            b = bounds[j]
            if not (a[1] < b[0] or b[1] < a[0] or a[3] < b[2] or b[3] < a[2]):
                return False
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=10)
    ap.add_argument('--nodes', type=int, default=10**9, help='smoke test: only the first N nodes')
    a = ap.parse_args()
    sys.set_int_max_str_digits(0)
    ct = load_f()
    disc = pickle.load(open(DISC, 'rb'))
    assert disc['m'] == 40 and len(disc['roots']) == 342 and disc.get('f_poly_sha256') == sha256(POLY), 'discriminant pickle does not match'
    Sq = [flint.fmpq(x) for x in disc['S']]
    assert len(Sq) == 343 and Sq[-1] == 1
    jobs = [(k, r['re'], r['im'], r['rad_exp10']) for k, r in enumerate(disc['roots']) if r['certified']][:a.nodes]
    assert len(jobs) == min(342, a.nodes), 'a shipped root box is uncertified'
    res = []
    t0 = time.monotonic()
    with mp.get_context('fork').Pool(a.workers, initializer=_init, initargs=(ct, Sq)) as pool:
        for r in pool.imap_unordered(_node, jobs):
            res.append(r)
            if len(res) % 25 == 0 or not r[1]:
                log('nodes', len(res), 'of', len(jobs), 'certified', sum(1 for x in res if x[1]), 'rate %.2f/s' % (len(res)/(time.monotonic()-t0)),
                    '' if r[1] else 'FAIL node %d: %s' % (r[0], r[2]))
    res.sort()
    bounds = [r[4]['box_bounds'] for r in res if r[4] is not None]
    disjoint = len(bounds) == len(res) and boxes_disjoint(bounds)
    log('parameter boxes pairwise disjoint', disjoint)
    rep = {'f_poly_sha256': sha256(POLY), 'disc_pkl_sha256': sha256(DISC),
           'nodes': len(res), 'certified': sum(1 for r in res if r[1]), 'failures': [(k, why) for k, ok, why, _, _ in res if not ok],
           'max_prec_bits': max(r[3] for r in res), 'max_extra_bits': max((r[4]['extra_bits'] for r in res if r[4]), default=None),
           'parameter_boxes_pairwise_disjoint': disjoint,
           'all_nodes_certified': all(r[1] for r in res) and len(res) == 342 and disjoint,
           'box_definition': ('T = exact box (re +- 10^e, im +- 10^e) from the discriminant pickle, rebuilt outward at prec and widened to '
                              'half-width |t| 2^-(prec - extra) + 10^e; interval Newton on S proves exactly one root of S in T'),
           'argument': ('disc = c (t^2+t+1)^40 S^2 with S squarefree; at each root of S exactly one double root with F_XX != 0, '
                        'so two single-valued analytic branches: trivial local monodromy'),
           'per_node': [{'k': k, 'prec': prec, 'extra_bits': info['extra_bits'] if info else None} for k, ok, why, prec, info in res],
           'runtime_seconds': round(time.monotonic()-START, 1)}
    json.dump(rep, open(OUT, 'w'), indent=1)
    log({k: v for k, v in rep.items() if k != 'per_node'})


if __name__ == '__main__':
    main()
