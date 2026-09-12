#!/usr/bin/env python3
"""The exact fibre of f over t = zeta3 (an independent exact check of the branch data).

f(X, zeta3) is factored over Q(zeta3) (PARI nffactor).  Expected from KB C40.7: one irreducible factor of
degree 5 with multiplicity 1 (the closed point of degree 5 over Q(zeta3)) and one of degree 20 with
multiplicity 3 (the closed point of degree 20).  Res_X(triple factor, F_t(X, zeta3)) != 0 shows the
triple roots are smooth points of the plane curve, so the ramification index there is exactly 3: the
local monodromy at zeta3 (and, by conjugation, at zeta3^2) has cycle type 3^20 1^5.
Output: results/fibre.json.

    python3 -u tools/fibre.py
"""
import hashlib, json, subprocess, time
from fractions import Fraction as F
from pathlib import Path

POLY = Path('results/f_poly.json')
OUT = Path('results/fibre.json')
GP = Path('results/fibre.gp')


def main():
    t0 = time.monotonic()
    d = json.load(open(POLY))
    c = {tuple(map(int, k.split(','))): F(v) for k, v in d['coefficients'].items()}

    def in_zeta3(coeffs):
        """sum_j v_j zeta3^j as a + b zeta3 (zeta3^2 = -zeta3 - 1)."""
        a, b = F(0), F(0)
        for j, v in enumerate(coeffs):
            r = j % 3
            if r == 0:
                a += v
            elif r == 1:
                b += v
            else:
                a -= v
                b -= v
        return a, b
    fterms, ftterms = [], []
    for m in range(66):
        a, b = in_zeta3([c.get((m, j), F(0)) for j in range(8)])
        fterms.append('(%s+(%s)*y)*x^%d' % (a, b, m))
        a, b = in_zeta3([j * c.get((m, j), F(0)) for j in range(1, 8)])
        ftterms.append('(%s+(%s)*y)*x^%d' % (a, b, m))
    script = ['default(parisize,"2G");', 'K = nfinit(y^2+y+1);', 'f = ' + '+'.join(fterms) + ';', 'ft = ' + '+'.join(ftterms) + ';',
              'fa = nffactor(K, f);', 'print(vector(#fa~, i, [poldegree(fa[i,1]), fa[i,2]]));',
              'g3 = 1; for(i=1,#fa~, if(fa[i,2]==3, g3 *= fa[i,1]));', 'print(poldegree(g3));',
              'print(polresultant(g3, ft, x) != 0);']
    GP.write_text('\n'.join(script) + '\n')
    out = subprocess.run(['gp', '-q', '-f', str(GP)], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=3600).stdout
    lines = [l for l in out.splitlines() if l.strip() and not l.startswith(' ***')]
    factors = eval(lines[0].replace('[', '(').replace(']', ')'))
    rep = {'f_poly_sha256': hashlib.sha256(POLY.read_bytes()).hexdigest(),
           'fibre_over_zeta3_factor_degrees_and_multiplicities': [list(x) for x in factors],
           'triple_part_degree': int(lines[1]), 'resultant_triple_part_with_F_t_nonzero': lines[2].strip() == '1',
           'gates': {'shape_5x1_plus_20x3': sorted(map(tuple, factors)) == [(5, 1), (20, 3)], 'triple_roots_smooth_points': lines[2].strip() == '1'},
           'runtime_seconds': round(time.monotonic() - t0, 1)}
    rep['all_gates_pass'] = all(rep['gates'].values())
    json.dump(rep, open(OUT, 'w'), indent=1)
    print(json.dumps(rep, indent=1))


if __name__ == '__main__':
    main()
