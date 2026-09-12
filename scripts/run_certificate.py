#!/usr/bin/env python3
"""Run the full certificate and the specialization proof."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / 'certificate'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-discriminant', action='store_true',
                        help='restore supplied discriminant instead of recomputing it; consumers still recertify nodes')
    parser.add_argument('--workers', type=int, default=4)
    args = parser.parse_args()
    gap = os.environ.get('GAP_BIN', 'gap')
    if shutil.which(gap) is None:
        raise SystemExit('Install GAP with primgrp, or set GAP_BIN to its executable.')
    if shutil.which('gp') is None:
        raise SystemExit('Install PARI/GP (gp must be on PATH).')
    commands = [[sys.executable, str(ROOT / 'scripts/check_cubic_maps.py')]]
    if args.reuse_discriminant:
        commands.append([sys.executable, str(ROOT / 'scripts/restore_discriminant.py')])
    else:
        commands.append([sys.executable, '-u', 'tools/discriminant.py'])
    commands.extend([
        [sys.executable, '-u', 'tools/nodes.py', '--workers', str(args.workers)],
        [sys.executable, '-u', 'tools/fibre.py'],
        [sys.executable, '-u', 'tools/monodromy.py', '--prec', '1200', '--skip-nodes', '--out', 'results/monodromy_gammas.json'],
        [sys.executable, '-u', 'tools/sz8_pullback.py', '--primes', '60'],
        [sys.executable, 'tools/primitive65.py'],
        [sys.executable, 'tools/merge.py'],
        [sys.executable, 'tools/specialisation.py', '--pmax', '400'],
    ])
    for command in commands:
        print('+', ' '.join(command), flush=True)
        subprocess.run(command, cwd=CERT, check=True)
    for report in ['monodromy.json', 'specialisation.json']:
        if not json.loads((CERT / 'results' / report).read_text())['all_gates_pass']:
            raise SystemExit('Failed final certificate: ' + report)
    print('PASS: generic certificate and specialization.')


if __name__ == '__main__':
    main()
