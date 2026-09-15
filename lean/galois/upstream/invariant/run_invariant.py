#!/usr/bin/env python3
"""Upstream derivation of `galois/inputs/resolvent_coefficients.json` (not needed to regenerate Lean files).

Pipeline (as run on 2026-09-13; results independent of PREC/M choices 300/16 and 700/24):
1. GAP (`orb.g`): the N-orbit of the monomial index (0, {1, 3}) and its translates under σ₁^j, j = 0, 1, 2.
2. PARI/GP (`run.gp`): power-series roots of f(X, t) at t = 0 (matched to the certified disc centres),
   Θ_j as series, elementary symmetric functions scaled by 13^(4·kscale), rounded to integers.
3. `post.gp`, `coef.gp`: resolvent shape checks; coefficients printed and compared with the recorded JSON.
Lean does not trust this output: `Resolvent`/`MainTheorem` certify the resolvent identity independently.

Usage: python3 galois/upstream/invariant/run_invariant.py [--prec 300 --order 16] (needs `gap`, `gp`)."""
import argparse, json, os, re, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[2]
sys.path.insert(0, str(PROJECT / 'galois'))
import enc  # noqa: E402  (F and centres as PARI expressions)

GAP = os.environ.get('GAP', 'gap')


def cycles(perm):
    seen, out = set(), []
    for i in range(len(perm)):
        if i in seen or perm[i] == i:
            continue
        c, j = [], i
        while j not in seen:
            seen.add(j); c.append(j + 1); j = perm[j]
        out.append('(' + ','.join(map(str, c)) + ')')
    return ''.join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prec', type=int, default=300)
    ap.add_argument('--order', type=int, default=16)
    args = ap.parse_args()
    mono = json.loads((PROJECT.parent / 'data/monodromy.json').read_text())['permutations']
    src = (HERE / 'orb.g').read_text()
    assert f"g1 := {cycles(mono['gamma_1'])};" in src and f"g2 := {cycles(mono['gamma_2'])};" in src
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        (tmp / 'orb_run.g').write_text(f'OUT := "{tmp}/orbits.txt";\nRead("{HERE}/orb.g");\n')
        subprocess.run([GAP, '-q', str(tmp / 'orb_run.g')], check=True, stdin=subprocess.DEVNULL)
        rows = {0: [], 1: [], 2: []}
        for line in (tmp / 'orbits.txt').read_text().split('\n'):
            if line.strip():
                j, a, b, c = map(int, line.split())
                rows[j].append(f'{a},{b},{c}')
        (tmp / 'orb.gp').write_text(''.join(f'O{j} = [' + ';'.join(rows[j]) + '];\n' for j in range(3)))
        (tmp / 'data.gp').write_text(f'F = {enc.f_gp()};\ncenters = {enc.centers_gp()};\nkscale = 3;\n')
        script = (f'PREC={args.prec}; M={args.order}; DIR="{tmp}"; E=vector(3);\n'
                  f'read("{HERE}/run.gp");\nread("{HERE}/post.gp");\n'
                  f'read("{tmp}/resolvent.gp");\n'
                  + (HERE / 'coef.gp').read_text().replace('read("resolvent.gp");', ''))
        out = subprocess.run(['gp', '-q', '--default', 'parisizemax=8G'], input=script, text=True,
                             capture_output=True, check=True).stdout
    print(out)
    got = {m: json.loads(v.replace(' ', '')) for m, v in re.findall(r'^E(\d) (\[.*\])$', out, re.M)}
    rec = json.loads((PROJECT / 'galois/inputs/resolvent_coefficients.json').read_text())
    ok = all(got.get(m) == rec[f'Z{m}'] for m in '123')
    print('matches galois/inputs/resolvent_coefficients.json:', ok)
    if not ok:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
