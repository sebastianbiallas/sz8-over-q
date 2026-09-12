#!/usr/bin/env python3
"""Run gap/primitive65.g and record the degree-65 primitive census as
results/primitive65.json.  Facts used by the certificate: among the 13 primitive groups of degree
65 exactly one has order 87,360 (PrimitiveGroup(65, 7) = Sz(8):3, derived subgroup Sz(8) of order
29,120); N_{S65}(Sz(8):3) = Sz(8):3; N_G(C13) = 13:12 with orbits 52 + 13; the maximal subgroups of
Sz(8) have orders 448, 52, 20, 14; the element orders of Sz(8) are 1, 2, 4, 5, 7, 13 and those of
Sz(8):3 outside Sz(8) are 3, 6, 12, 15.

    python3 tools/primitive65.py
"""
import json, os, re, subprocess, time
from pathlib import Path

GAP = os.environ.get('GAP_BIN', 'gap')
SCRIPT = Path('gap/primitive65.g')
OUT = Path('results/primitive65.json')


def main():
    t0 = time.monotonic()
    out = subprocess.run([str(GAP), '-q', '-b', '--quitonbreak', str(SCRIPT)], stdin=subprocess.DEVNULL, capture_output=True,
                         text=True, timeout=1800).stdout
    out = out.replace('\\\n', '')
    groups, classes, facts = [], [], {}
    for l in out.splitlines():
        l = l.strip()
        if l.startswith('PRIM '):
            i, name, order, dord, simple = [x.strip() for x in l[5:].split('|')]
            groups.append({'i': int(i), 'name': name, 'order': int(order), 'derived_order': int(dord), 'simple': simple == 'true'})
        elif l.startswith('CLASS '):
            order, cyc, inD = [x.strip() for x in l[6:].split('|')]
            classes.append({'element_order': int(order), 'cycle_lengths_with_multiplicity': eval(cyc), 'in_Sz8': inD == 'true'})
        elif l.startswith('NPRIM '):
            facts['n_primitive_groups'] = int(l.split()[1])
        elif l.startswith('NORMALISER_S65 '):
            facts['normaliser_in_S65_order'] = int(l.split()[1])
        elif l.startswith('SZ8_ORDER '):
            facts['Sz8_order'] = int(l.split()[1]); facts['Sz8_simple'] = l.split()[3] == 'true'
        elif l.startswith('SZ8_MAXIMAL_ORDERS '):
            facts['Sz8_maximal_subgroup_orders'] = eval(l.split(' ', 1)[1])
        elif l.startswith('SZ8_ELEMENT_ORDERS '):
            facts['Sz8_element_orders'] = eval(l.split(' ', 1)[1])
        elif l.startswith('G_ELEMENT_ORDERS '):
            facts['Sz8_3_element_orders'] = eval(l.split(' ', 1)[1])
        elif l.startswith('N_G_C13_ORDER '):
            m = re.match(r'N_G_C13_ORDER (\d+) ORBITS (.*)', l)
            facts['N_G_C13_order'] = int(m.group(1)); facts['N_G_C13_orbit_lengths'] = eval(m.group(2))
        elif l.startswith('N_SZ8_C13_ORDER '):
            facts['N_Sz8_C13_order'] = int(l.split()[1])
    of_order = [g for g in groups if g['order'] == 87360]
    gates = {'thirteen_primitive_groups': facts.get('n_primitive_groups') == 13 == len(groups),
             'unique_group_of_order_87360': len(of_order) == 1 and of_order[0]['i'] == 7,
             'derived_subgroup_is_simple_of_order_29120': of_order[0]['derived_order'] == 29120 if of_order else False,
             'normaliser_in_S65_is_itself': facts.get('normaliser_in_S65_order') == 87360,
             'N_G_C13_is_13_12_with_orbits_52_13': facts.get('N_G_C13_order') == 156 and sorted(facts.get('N_G_C13_orbit_lengths', [])) == [13, 52],
             'N_Sz8_C13_is_13_4': facts.get('N_Sz8_C13_order') == 52,
             'no_maximal_subgroup_order_divisible_by_91': all(o % 91 for o in facts.get('Sz8_maximal_subgroup_orders', [0])),
             'Sz8_has_no_element_of_order_3': 3 not in facts.get('Sz8_element_orders', [3]),
             'elements_outside_Sz8_have_order_divisible_by_3': all(c['element_order'] % 3 == 0 for c in classes if not c['in_Sz8']) and bool(classes)}
    rep = {'gap_script': str(SCRIPT), 'primitive_groups_degree_65': groups, 'facts': facts,
           'classes_of_Sz8_3_on_65_points': classes, 'gates': gates, 'all_gates_pass': all(gates.values()),
           'runtime_seconds': round(time.monotonic() - t0, 1)}
    json.dump(rep, open(OUT, 'w'), indent=1)
    print(json.dumps({k: v for k, v in rep.items() if k not in ('classes_of_Sz8_3_on_65_points',)}, indent=1))


if __name__ == '__main__':
    main()
