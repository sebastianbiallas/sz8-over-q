#!/usr/bin/env python3
"""Upstream GAP cross-checks and the recorded relabelling `galois/inputs/suzuki_conj.txt`.

1. The 72 matrices T(a,b), M(κ), W (F8 element b0 + 2·b1 + 4·b2 ↦ b0 + b1·Z(8) + b2·Z(8)², GAP's GF(8) having
   Conway polynomial x³ + x + 1) generate GAP's `SuzukiGroup(IsMatrixGroup, 8)`.
2. Their action on the ovoid (orbit order) is 2-transitive of order 29120, and
   `RepresentativeAction(SymmetricGroup(65), P, N)` conjugates it onto N = [G, G], G = ⟨σ₁, σ₂⟩ from
   data/monodromy.json. The conjugator is printed as an image list and compared with the recorded input.
3. The labelled generator images (galois/suzuki.py) generate exactly N.
GAP's output is not a premise of the Lean proof; a different conjugator would only change the labelling.
Usage: GAP=/path/to/gap python3 galois/upstream/suzuki/run_gap.py [--write]"""
import argparse, json, os, re, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[2]
sys.path.insert(0, str(PROJECT / 'galois'))
import suzuki  # noqa: E402
from paths import INPUTS, MONODROMY_JSON  # noqa: E402

GAP = os.environ.get('GAP', 'gap')


def gf8(x):
    terms = [t for t, bit in (('One(GF(8))', 1), ('Z(8)', 2), ('Z(8)^2', 4)) if x & bit]
    return '+'.join(terms) if terms else '0*Z(8)'


def perm_list(p):
    return 'PermList([' + ','.join(str(v + 1) for v in p) + '])'


def orbit_action():
    orb = [(0, 0, 0, 1)]
    seen = set(orb)
    for p in orb:
        for g in suzuki.GENS:
            q = tuple(suzuki.normalize(suzuki.mv(g, p)))
            if q not in seen:
                seen.add(q)
                orb.append(q)
    idx = {p: i for i, p in enumerate(orb)}
    return [[idx[tuple(suzuki.normalize(suzuki.mv(g, p)))] for p in orb] for g in suzuki.GENS]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--write', action='store_true', help='overwrite inputs/suzuki_conj.txt')
    args = ap.parse_args()
    mono = json.loads(MONODROMY_JSON.read_text())['permutations']
    mats = ',\n'.join('[' + ','.join('[' + ','.join(gf8(x) for x in row) + ']' for row in g) + ']' for g in suzuki.GENS)
    _, labelled = suzuki.labelled()
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / 'conj.txt'
        script = f'''mymats := [{mats}];;
ovgens := [{','.join(perm_list(p) for p in orbit_action())}];;
lgens := [{','.join(perm_list(p) for p in labelled)}];;
g1 := {perm_list(mono['gamma_1'])};; g2 := {perm_list(mono['gamma_2'])};;
S := SuzukiGroup(IsMatrixGroup, 8);;
Print("matrix group = SuzukiGroup(IsMatrixGroup, 8): ", Group(mymats) = S, " order ", Size(S), "\\n");
P := Group(ovgens);;
Print("ovoid action order ", Size(P), ", transitivity ", Transitivity(P, [1..65]), "\\n");
N := DerivedSubgroup(Group(g1, g2));;
x := RepresentativeAction(SymmetricGroup(65), P, N);;
Print("P^x = N: ", x <> fail and P^x = N, "\\n");
PrintTo("{out}", ListPerm(x, 65), "\\n");
Print("labelled images generate N: ", Group(lgens) = N, "\\n");
QUIT;
'''
        (Path(tmp) / 'run.g').write_text(script)
        res = subprocess.run([GAP, '-q', str(Path(tmp) / 'run.g')], capture_output=True, text=True,
                             stdin=subprocess.DEVNULL, check=True)
        print(res.stdout)
        conj = out.read_text()
    same = re.findall(r'\d+', conj) == re.findall(r'\d+', (INPUTS / 'suzuki_conj.txt').read_text())
    print('conjugator equals galois/inputs/suzuki_conj.txt:', same)
    if args.write:
        (INPUTS / 'suzuki_conj.txt').write_text(conj)
    ok = res.stdout.count('true') == 3 and 'order 29120' in res.stdout and 'transitivity 2' in res.stdout
    if not ok:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
