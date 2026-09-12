#!/usr/bin/env python3
"""Final certificate report: merges the stage reports into results/monodromy.json and states
the theorem's gates.  Inputs and what each supplies:
  results/monodromy_gammas.json  (tools/monodromy.py --skip-nodes)  the two loop permutations, group
  results/nodes.json             (tools/nodes.py)                    every root of S is an unramified node
  results/discriminant.json              (tools/discriminant.py)                     disc = c (t^2+t+1)^40 S^2, S squarefree
  results/fibre.json             (tools/fibre.py)                    exact fibre g5 g20^3 over Q(zeta3)
  results/sz8_pullback.json               (tools/sz8_pullback.py)                      the twist T2 and g(X, s)
  results/primitive65.json          (tools/primitive65.py)              GAP census of degree 65, Sz(8) facts
Binding: every report carries the sha256 of results/f_poly.json, which must agree with the file on
disk; the node and monodromy reports carry the sha256 of results/discriminant.pkl, which must agree with
the pickle on disk; the Sz(8) pullback report carries the sha256 of results/g_poly.json.  The group is identified
by its order, transitivity and primitivity: of the 13 primitive groups of degree 65 only PrimitiveGroup(65, 7)
= Sz(8):3 has order 87,360.

    python3 tools/merge.py
"""
import hashlib, json, os, platform, subprocess, sys
from pathlib import Path
import flint

R = Path('results')
F_POLY, G_POLY, DISC_PKL = R / 'f_poly.json', R / 'g_poly.json', R / 'discriminant.pkl'


def sha256(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    g = json.load(open(R / 'monodromy_gammas.json'))
    n = json.load(open(R / 'nodes.json'))
    d = json.load(open(R / 'discriminant.json'))
    fb = json.load(open(R / 'fibre.json'))
    s4 = json.load(open(R / 'sz8_pullback.json'))
    pr = json.load(open(R / 'primitive65.json'))
    fsha, gsha, psha = sha256(F_POLY), sha256(G_POLY), sha256(DISC_PKL)
    gates = {k: v for k, v in g['gates'].items()}
    gates['group_transitive'] = g['group_transitive']
    gates['all_342_nodes_certified_ordinary_unramified'] = n['all_nodes_certified']
    gates['node_parameter_boxes_pairwise_disjoint'] = n['parameter_boxes_pairwise_disjoint']
    gates['discriminant_is_c_t2t1_40_S_squared'] = d['D1_equals_c_S_squared'] and d['multiplicity_t2_t_1'] == 40 and d['degree_S'] == 342 and d['S_squarefree']
    gates['all_S_roots_certified'] = d['roots_certified'] == d['roots_total'] == 342 and d['roots_pairwise_disjoint']
    gates['exact_fibre_g5_g20cubed_over_Q_zeta3'] = fb['all_gates_pass']
    gates['twist_identified_T2'] = s4['verdict'] == 'M_IDENTIFIED' and s4['chosen_twist'] == 2
    gates['g_leading_coefficient_den_s_7'] = s4.get('g_leading_coefficient_X65_equals_den_s_7', False)
    gates['primitive_degree65_census'] = pr['all_gates_pass']
    gates['f_poly_hash_bound_in_every_report'] = all(x.get('f_poly_sha256') == fsha for x in (g, n, d, fb, s4))
    gates['disc_pkl_hash_bound'] = n.get('disc_pkl_sha256') == psha == g.get('disc_pkl_sha256') and json.load(open(G_POLY)).get('f_poly_sha256') == fsha
    gates['g_poly_hash_bound'] = s4.get('g_poly_sha256') == gsha
    ok = all(gates.values())
    versions = {'python': platform.python_version(), 'python_flint': flint.__version__,
                'pari_gp': subprocess.run(['gp', '--version-short'], capture_output=True, text=True).stderr.strip() or
                           subprocess.run(['gp', '--version-short'], capture_output=True, text=True).stdout.strip(),
                'gap': subprocess.run([os.environ.get('GAP_BIN', 'gap'), '--version'], capture_output=True, text=True, stdin=subprocess.DEVNULL).stdout.strip(),
                'git_head': subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()}
    rep = {'gates': gates, 'all_gates_pass': ok,
           'inputs': {'f_poly': str(F_POLY), 'f_poly_sha256': fsha, 'g_poly': str(G_POLY), 'g_poly_sha256': gsha,
                      'disc_pkl': str(DISC_PKL), 'disc_pkl_sha256': psha},
           'versions': versions,
           'commands': ['python3 -u tools/discriminant.py', 'python3 -u tools/nodes.py --workers 10', 'python3 -u tools/fibre.py',
                        'python3 -u tools/monodromy.py --prec 1200 --skip-nodes --out results/monodromy_gammas.json',
                        'python3 -u tools/sz8_pullback.py --primes 60', 'python3 tools/primitive65.py', 'python3 tools/merge.py'],
           'gamma_1': {k: v for k, v in g['gamma_1'].items() if k != 'permutation'},
           'gamma_2': {k: v for k, v in g['gamma_2'].items() if k != 'permutation'},
           'permutations': {'gamma_1': g['gamma_1']['permutation'], 'gamma_2': g['gamma_2']['permutation']},
           'gamma_1_gamma_2_cycle_type': g['gamma_1_gamma_2_cycle_type'], 'group_order': g['group_order'],
           'group_transitive': g['group_transitive'], 'group_primitive': g['group_primitive'], 'prec_bits': g['prec_bits'],
           'nodes': {k: v for k, v in n.items() if k not in ('failures', 'per_node')}, 'discriminant': d,
           'fibre': {k: v for k, v in fb.items()}, 'twist': {k: v for k, v in s4.items() if k != 'rows'},
           'primitive65': {'facts': pr['facts'], 'groups': [(x['i'], x['name'], x['order']) for x in pr['primitive_groups_degree_65']]},
           'conclusion': ('f(X, t) defines a degree-65 cover of P^1 branched exactly over zeta3, zeta3^2, inf with geometric monodromy '
                          'Sz(8):3 (the unique primitive group of degree 65 and order 87,360); N_{S65}(Sz(8):3) = Sz(8):3 makes the '
                          'arithmetic monodromy equal, so Gal(f / Q(t)) = Sz(8):3 regular over Q; the Sz(8)-fixed field is the twist '
                          'T2 of the Shanks cover, Q(s) with t = T2(s), and g(X, s) = den(s)^7 f(X, T2(s)) has Gal = Sz(8) regular over Q(s).')
           if ok else 'SOME GATES FAIL: ' + ', '.join(k for k, v in gates.items() if not v)}
    json.dump(rep, open(R / 'monodromy.json', 'w'), indent=1)
    print(json.dumps({k: v for k, v in rep.items() if k not in ('permutations', 'discriminant', 'nodes', 'fibre', 'twist', 'primitive65')}, indent=1))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
