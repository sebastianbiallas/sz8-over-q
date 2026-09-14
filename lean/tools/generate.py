#!/usr/bin/env python3
"""Regenerate the generated Lean files (not tracked by git) and check them against pinned hashes.

  python3 tools/generate.py          # restore the discriminant pickle if needed, run every exporter,
                                     # then check all generated files against provenance/generated.json
  python3 tools/generate.py --check  # only the hash and git-ignore checks
  python3 tools/generate.py --pin    # rewrite provenance/generated.json from the current files

Exporters run with SZ8_PINNED_PROVENANCE=1: they refuse to write if the result would change a
committed provenance manifest. Generated files are the artifacts listed in provenance/export_*.json
plus the certificate files of Sz8/Monodromy/Meridian/ (export_meridian.py). Requires Python with sympy and
python-flint, and PARI/GP (`gp`)."""
import argparse, hashlib, json, os, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parent
PINS = HERE / 'provenance/generated.json'
EXPORTERS = [['export_inputs.py'], ['export_step.py'], ['export_monodromy.py'], ['export_groups.py'],
             ['export_sylow.py'], ['export_normalizer.py'], ['export_continuation.py'],
             ['export_meridian.py', 'emit'], ['export_galois.py']]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generated_paths():
    paths = set()
    for manifest in sorted((HERE / 'provenance').glob('export_*.json')):
        paths |= set(json.loads(manifest.read_text())['artifacts'])
    paths |= {str(p.relative_to(HERE)) for p in (HERE / 'Sz8/Monodromy/Meridian').glob('*.lean')}
    return sorted(paths)


def git(*args):
    return subprocess.run(['git', '-C', str(REPO), *args], capture_output=True, text=True)


def check(pins):
    missing = [p for p in pins if not (HERE / p).exists()]
    wrong = [p for p in pins if (HERE / p).exists() and sha256(HERE / p) != pins[p]]
    extra = sorted(set(generated_paths()) - set(pins))
    if missing or wrong or extra:
        raise SystemExit(f'generated files differ from provenance/generated.json: missing {missing[:5]}, '
                         f'changed {wrong[:5]}, unpinned {extra[:5]}')
    if git('rev-parse', '--is-inside-work-tree').returncode == 0:
        rel = [str(Path('lean') / p) for p in pins]
        ignored = set(git('check-ignore', '--no-index', *rel).stdout.split())
        not_ignored = sorted(set(rel) - ignored)
        tracked = git('ls-files', *rel).stdout.split()
        stray = [f for f in git('ls-files', '--others', '--ignored', '--exclude-standard',
                                'lean/Sz8').stdout.split()
                 if f.endswith('.lean') and f not in set(rel)]
        if not_ignored or tracked or stray:
            raise SystemExit(f'git ignore rules and generated files disagree: not ignored {not_ignored[:5]}, '
                             f'tracked {tracked[:5]}, ignored but not generated {stray[:5]}')
    print(f'{len(pins)} generated files match provenance/generated.json')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--pin', action='store_true')
    args = ap.parse_args()
    if args.pin:
        PINS.write_text(json.dumps({p: sha256(HERE / p) for p in generated_paths()}, indent=1) + '\n')
        print(f'pinned {len(generated_paths())} generated files')
        return
    pins = json.loads(PINS.read_text())
    if not args.check:
        if not (REPO / 'certificate/results/discriminant.pkl').exists():
            subprocess.run([sys.executable, 'scripts/restore_discriminant.py'], cwd=REPO, check=True)
        env = dict(os.environ, SZ8_PINNED_PROVENANCE='1')
        for cmd in EXPORTERS:
            print('Running:', ' '.join(['python3', *cmd]), flush=True)
            subprocess.run([sys.executable, *cmd], cwd=HERE, env=env, check=True)
    check(pins)


if __name__ == '__main__':
    main()
