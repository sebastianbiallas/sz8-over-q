#!/usr/bin/env python3
"""The exact X-discriminant of f(X, t) and its node polynomial.

D(t) = disc_X f(X, t) is a polynomial of degree <= 2 * 64 * 7 = 896 in t.  It is computed exactly:
f(X, t0) for t0 = 0, 1, ..., 896 has an exact discriminant (FLINT fmpq_poly.discriminant), and the
values are interpolated by Newton divided differences in fmpq.  The result is checked at extra
points.  Then D = c (t^2 + t + 1)^m S^2 with S squarefree and monic is extracted (m by exact division,
S = D1 / gcd(D1, D1') then D1 = c S^2 verified exactly), and the roots of S are located by PARI
polroots (Schoenhage splitting handles the dynamic range: nodes up to |t| ~ 4e34, where arb's
acb_poly.roots fails at any precision) and certified by an interval Newton step in arb.

Root boxes.  Each root is shipped as an EXACT rational box: the decimal strings re, im printed by
PARI (exact rationals) and an integer e; the box is
    B = { t : |Re t - re| <= 10^e, |Im t - im| <= 10^e }.
The certificate is: N(B) = m - S(m) / S'(B) lies inside B with 0 not in S'(B), where m = (re, im);
then B contains exactly one root of S (mean-value form, Brouwer for existence, 0 not in S'(B) for
uniqueness; B is convex).  Every consumer rebuilds B outward from (re, im, e) at its own precision
(arb of an fmpq is an enclosure; 10^e as a ball times [0 +/- 1]), so the box a later stage works
with contains the certified one.  No binary64 conversion anywhere in the serialisation.

Output: results/discriminant.pkl {D, m, S, c: exact coefficient strings; roots: [{re, im, rad_exp10,
certified}]; prec_bits; f_poly_sha256} and results/discriminant.json (summary with the same gates).

    python3 -u tools/discriminant.py
"""
import hashlib, json, math, pickle, subprocess, sys, time
from fractions import Fraction as F
from pathlib import Path
import flint

POLY = Path('results/f_poly.json')
OUT = Path('results/discriminant.pkl')
SUM = Path('results/discriminant.json')
GP_IN = Path('results/discriminant_S.gp')
START = time.monotonic()
CERT_PREC = 100000
PARI_DIGITS = 9000
RAD_LADDER = (8800, 8000, 4000, 1000, 300, 100)      # box half-width 10^(e10 - k), e10 = floor(log10 |t|) clamped >= 0


def log(*a):
    print('[%7.1fs]' % (time.monotonic()-START), *a, flush=True)


def sha256(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def load_f():
    d = json.load(open(POLY))
    coef = {}
    for k, v in d['coefficients'].items():
        i, j = map(int, k.split(','))
        x = F(v)
        coef.setdefault(i, [flint.fmpq(0)]*8)[j] = flint.fmpq(x.numerator, x.denominator)
    return [flint.fmpq_poly(coef.get(i, [flint.fmpq(0)])) for i in range(66)]   # c_i(t) for X^i


def f_at(ct, t0):
    t0 = flint.fmpq(t0)
    return flint.fmpq_poly([c(t0) for c in ct])


def newton_interp(xs, ys):
    """Coefficients (ascending) of the interpolating polynomial through (xs[i], ys[i]) in fmpq."""
    n = len(xs)
    coef = list(ys)
    for j in range(1, n):
        for i in range(n-1, j-1, -1):
            coef[i] = (coef[i] - coef[i-1]) / (xs[i] - xs[i-j])
    poly = flint.fmpq_poly([coef[n-1]])
    for i in range(n-2, -1, -1):
        poly = poly * flint.fmpq_poly([-xs[i], 1]) + flint.fmpq_poly([coef[i]])
    return poly


def fmpq_of_decimal(s):
    fr = F(s)
    return flint.fmpq(fr.numerator, fr.denominator)


def root_box(re, im, e):
    """Outward enclosure (at the current precision) of the exact box |Re t - re|, |Im t - im| <= 10^e,
    and the exact centre as a ball.  Shared definition with the consumers (tools/nodes.py)."""
    mre, mim = flint.arb(fmpq_of_decimal(re)), flint.arb(fmpq_of_decimal(im))
    r = flint.arb(10)**e
    E = flint.arb(0, 1) * r
    return flint.acb(mre, mim), flint.acb(mre + E, mim + E), r


def certify_root(Ap, Apd, re, im, e):
    """Interval Newton certificate that the box (re, im, 10^e) contains exactly one root of S."""
    m, B, r = root_box(re, im, e)
    dB = Apd(B)
    if not dB.is_finite() or dB.contains(0):
        return False
    NB = m - Ap(m) / dB
    return bool(NB.is_finite() and B.real.contains(NB.real) and B.imag.contains(NB.imag))


def main():
    sys.set_int_max_str_digits(0)
    fsha = sha256(POLY)
    ct = load_f()
    N = 897
    xs = [flint.fmpq(i) for i in range(N)]
    ys = []
    t0 = time.monotonic()
    for i in range(N):
        ys.append(f_at(ct, i).discriminant())
        if i % 100 == 0:
            log('discriminant values', i, 'of', N, '%.1fs' % (time.monotonic()-t0))
    log('values done; interpolating')
    D = newton_interp(xs, ys)
    log('interpolated; degree', D.degree())
    ok_extra = all(D(flint.fmpq(t)) == f_at(ct, t).discriminant() for t in (N, N+1, 5000, flint.fmpq(1, 3)))
    log('extra-point checks', ok_extra)
    q = flint.fmpq_poly([1, 1, 1])
    D1, m = D, 0
    while True:
        qq, rr = divmod(D1, q)
        if not rr.is_zero():
            break
        D1, m = qq, m+1
    g = D1.gcd(D1.derivative())
    S, r = divmod(D1, g)
    assert r.is_zero()
    S = S / S.coeffs()[-1]          # monic
    c = D1.coeffs()[-1]
    ok_square = (D1 == S*S*c)
    ok_sqfree = S.gcd(S.derivative()).degree() == 0
    log('m', m, 'deg S', S.degree(), 'D1 = c S^2', ok_square, 'S squarefree', ok_sqfree, 'c digits', len(str(c.p)), len(str(c.q)))
    exact = {'D': [str(x) for x in D.coeffs()], 'm': m, 'S': [str(x) for x in S.coeffs()], 'c': str(c), 'f_poly_sha256': fsha}
    pickle.dump(dict(exact, roots=None), open(OUT, 'wb'))
    log('saved exact D and S')
    # ---- roots of S by PARI, certified in arb
    L = 1
    for c_ in S.coeffs():
        L = L * int(c_.q) // math.gcd(L, int(c_.q))
    Si = [int(c_.p) * (L // int(c_.q)) for c_ in S.coeffs()]
    GP_IN.write_text('default(parisize, "4G");\ndefault(realprecision, %d);\nS = Pol(Vecrev([' % PARI_DIGITS + ','.join(map(str, Si)) +
                     ']));\nr = polroots(S);\nfor(i=1,#r, print(real(r[i]), ";", imag(r[i])));\n')
    t1 = time.monotonic()
    out = subprocess.run(['gp', '-q', '-f', str(GP_IN)], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=7200).stdout
    approx = []
    for l in out.splitlines():
        if ';' in l and not l.startswith(' ***'):
            re_, im_ = [x.replace(' ', '') for x in l.split(';')]
            F(re_), F(im_)                                    # must parse as exact decimals
            approx.append((re_, im_))
    log('PARI polroots returned', len(approx), 'roots in %.0fs' % (time.monotonic()-t1))
    assert len(approx) == S.degree(), 'PARI returned the wrong number of roots'
    flint.ctx.prec = CERT_PREC
    Ap = flint.acb_poly([flint.acb(x) for x in S.coeffs()])
    Apd = Ap.derivative()
    roots = []
    t1 = time.monotonic()
    for idx, (re_, im_) in enumerate(approx):
        tabs = math.hypot(float(F(re_)), float(F(im_)))
        e10 = max(0, int(math.floor(math.log10(tabs)))) if tabs > 0 else 0
        ok, e = False, None
        for k in RAD_LADDER:
            e = e10 - k
            if certify_root(Ap, Apd, re_, im_, e):
                ok = True
                break
        roots.append({'re': re_, 'im': im_, 'rad_exp10': e if ok else None, 'certified': ok})
        if idx % 50 == 0:
            log('root', idx, 'certified', ok, 'rad_exp10', e, '%.0fs' % (time.monotonic()-t1))
    ncert = sum(1 for r_ in roots if r_['certified'])
    boxes = [root_box(r_['re'], r_['im'], r_['rad_exp10'])[1] if r_['certified'] else None for r_ in roots]
    pair_ok = all(boxes[i] is not None and boxes[j] is not None and (boxes[i] - boxes[j]).abs_lower() > 0
                  for i in range(len(boxes)) for j in range(i+1, len(boxes)))
    log('roots certified', ncert, 'of', len(roots), 'pairwise disjoint', pair_ok)
    method = ('PARI polroots at %d digits; each root certified by an interval Newton step in arb at %d bits on the exact '
              'rational box |Re t - re|, |Im t - im| <= 10^rad_exp10 (re, im the exact decimal strings)' % (PARI_DIGITS, CERT_PREC))
    pickle.dump(dict(exact, roots=roots, roots_method=method, prec_bits=CERT_PREC), open(OUT, 'wb'))
    summ = {'f_poly': str(POLY), 'f_poly_sha256': fsha, 'degree_D': D.degree(), 'multiplicity_t2_t_1': m,
            'degree_S': S.degree(), 'S_squarefree': ok_sqfree, 'D1_equals_c_S_squared': ok_square, 'extra_point_checks': ok_extra,
            'roots_total': len(roots), 'roots_certified': ncert, 'roots_pairwise_disjoint': pair_ok,
            'min_rad_exp10': min(r_['rad_exp10'] for r_ in roots if r_['certified']),
            'max_rad_exp10': max(r_['rad_exp10'] for r_ in roots if r_['certified']),
            'roots_method': method, 'prec_bits': CERT_PREC,
            'max_coefficient_digits_D': max(len(str(x.p)) for x in D.coeffs()),
            'max_coefficient_digits_S': max(len(str(x.p)) for x in S.coeffs()),
            'gates': {'extra_point_checks': ok_extra, 'D1_equals_c_S_squared': ok_square, 'S_squarefree': ok_sqfree,
                      'multiplicity_40': m == 40, 'degree_S_342': S.degree() == 342,
                      'all_roots_certified': ncert == len(roots) == S.degree(), 'roots_pairwise_disjoint': pair_ok},
            'runtime_seconds': round(time.monotonic()-START, 1)}
    summ['all_gates_pass'] = all(summ['gates'].values())
    json.dump(summ, open(SUM, 'w'), indent=1)
    log({k: v for k, v in summ.items() if k != 'roots_method'})


if __name__ == '__main__':
    main()
