#!/usr/bin/env python3
"""Exact modular check of the double-root assertion, independently of interval boxes.

Given the characteristic-zero discriminant identity in the paper, a full-degree
reduction D = c*q^40*S^2 with S squarefree identifies the reduction of its monic S.
Degree-one gcds over every residue field show that the first principal
subresultant is a unit modulo S. Its resultant with S is therefore nonzero in
characteristic zero. This checks Proposition 4.1(ii), not the exact discriminant
identity or analytic continuation. Requires PARI/GP.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
PRIME = 1000003


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='optional JSON report')
    args = parser.parse_args()
    start = time.monotonic()
    source = ROOT / 'data/f.json'
    coefficients = json.loads(source.read_text())['coefficients']
    terms = []
    for key, value in coefficients.items():
        i, j = map(int, key.split(','))
        c = Fraction(value)
        residue = c.numerator % PRIME * pow(c.denominator, -1, PRIME) % PRIME
        if residue:
            terms.append(f'{residue}*X^{i}*t^{j}')
    script = f'''p={PRIME}; f0={'+'.join(terms)};
{{
f = f0*Mod(1,p);
pts = vector(900, k, Mod(k,p));
vals = vector(900, k, poldisc(substpol(f, t, pts[k]) + 0*X, X));
D = lift(polinterpolate(lift(pts), lift(vals), t))*Mod(1,p);
q = t^2+t+1; m = 0; while(D % q^(m+1) == 0, m++);
D1 = D / q^m; S = gcd(D1, deriv(D1)); S = S/pollead(S);
print("GATE|degree_764|", poldegree(D) == 764);
print("GATE|q_order_40|", m == 40);
print("GATE|S_degree_342|", poldegree(S) == 342);
print("GATE|discriminant_shape|", poldegree(D1) == 684 && D1 % S^2 == 0);
print("GATE|S_squarefree|", poldegree(gcd(S, deriv(S))) == 0);
print("GATE|S_coprime_q|", poldegree(gcd(S,q)) == 0);
fa = factor(S)[,1]; bad = 0;
for(i = 1, #fa, P = fa[i]; g = ffgen(P, 'a); fx = substpol(lift(f), t, g);
  d = poldegree(gcd(fx, deriv(fx, X)));
  print("FACTOR|", poldegree(P), "|", d); if(d != 1, bad++));
print("GATE|all_gcd_degrees_one|", bad == 0);
}}
'''
    with tempfile.TemporaryDirectory(prefix='su8-nodes-') as temp:
        path = Path(temp) / 'check.gp'
        path.write_text(script)
        run = subprocess.run(['gp', '-q', '-f', '--default', 'parisizemax=8G', str(path)],
                             stdin=subprocess.DEVNULL, capture_output=True, text=True)
    expected = {'degree_764', 'q_order_40', 'S_degree_342', 'discriminant_shape',
                'S_squarefree', 'S_coprime_q', 'all_gcd_degrees_one'}
    gates, factors = {}, []
    for line in run.stdout.splitlines():
        if line.startswith('GATE|'):
            _, name, value = line.split('|')
            gates[name] = value == '1'
        elif line.startswith('FACTOR|'):
            _, degree, gcd_degree = line.split('|')
            factors.append({'factor_degree': int(degree), 'gcd_degree': int(gcd_degree)})
    gates['complete_output'] = set(gates) == expected
    gates['factor_degrees'] = sorted(f['factor_degree'] for f in factors) == [1, 3, 5, 14, 78, 84, 157]
    gates['process_success'] = run.returncode == 0 and not any(
        line.lstrip().startswith('***') and 'Warning:' not in line for line in run.stderr.splitlines())
    report = {'prime': PRIME, 'f_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'gates': gates, 'factors': factors, 'all_gates_pass': all(gates.values()),
              'runtime_seconds': round(time.monotonic() - start, 2)}
    if args.out:
        args.out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    if not report['all_gates_pass']:
        print(run.stdout)
        print(run.stderr)
        raise SystemExit(1)
    print('PASS: every root of S carries exactly one double root.')


if __name__ == '__main__':
    main()
