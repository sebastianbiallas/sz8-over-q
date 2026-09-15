#!/usr/bin/env python3
"""Source snapshot of the Lean project: the file list, an isolated copy of the repository, and the manifest.

  python3 tools/snapshot.py list                        # the source files of lean/ that git tracks or would track
  python3 tools/snapshot.py copy-repo DEST              # copy those files of the whole repository into DEST
  python3 tools/snapshot.py manifest BUILD [--note ...] # write reproducibility.json from a finished clean build

Sources are the files git tracks or would add (not ignored); `reproducibility.json` itself is excluded from
the hashes. Generated files are not sources: their hashes are pinned in provenance/generated.json."""
import argparse, hashlib, json, os, platform, re, shutil, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parent
SELF = 'reproducibility.json'
PUBLIC_INPUTS = ['data/f.json', 'data/monodromy.json', 'certificate/manifest.json',
                 'certificate/results/discriminant.pkl.gz', 'certificate/results/discriminant.pkl',
                 'certificate/results/monodromy.json', 'scripts/restore_discriminant.py']
HEADLINE = ['Sz8.Galois.card_gal_specialization', 'Sz8.Galois.gal_specialization_eq_N',
            'Sz8.Galois.gal_specialization_equiv_suzuki', 'Sz8.Galois.N_equiv_suzuki']


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    return (r.stdout + r.stderr).strip()


def repo_files(subdir=None):
    args = ['git', '-C', str(REPO), 'ls-files', '--cached', '--others', '--exclude-standard', '-z']
    if subdir:
        args.append(subdir)
    out = subprocess.run(args, capture_output=True, text=True, check=True).stdout
    return sorted(f for f in out.split('\0') if f and (REPO / f).is_file())


def source_files(root=HERE):
    """Source files of the project at `root`: the git view for this checkout, a directory walk for copies."""
    if Path(root).resolve() == HERE:
        return [f[len('lean/'):] for f in repo_files('lean') if f != f'lean/{SELF}']
    pins = set(json.loads((Path(root) / 'provenance/generated.json').read_text()))
    ignored_dirs = {'.lake', 'lean-4.34.0-rc2-darwin_aarch64', '__pycache__'}
    ignored_files = {'lean-toolchain.tar.zst', 'verification.json', 'verification.log', 'build-batches.jsonl',
                     'full_build.log', SELF, '.DS_Store'}
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in ignored_dirs]
        rel = Path(dirpath).relative_to(root)
        for f in filenames:
            p = str(rel / f) if str(rel) != '.' else f
            if f not in ignored_files and p not in pins:
                out.append(p)
    return sorted(out)


def tool_versions(build):
    versions = {'python': sys.version.split()[0], 'platform': platform.platform(), 'machine': platform.machine(),
                'memory_bytes': int(run(['sysctl', '-n', 'hw.memsize']) or 0), 'cpus': os.cpu_count(),
                'lean': run(['sh', 'run-lake.sh', 'env', 'lean', '--version'], cwd=build),
                'lake': run(['sh', 'run-lake.sh', '--version'], cwd=build),
                'pari_gp': run(['gp', '--version-short'])}
    for mod in ('sympy', 'flint'):
        try:
            versions[f'python_{mod}'] = __import__(mod).__version__
        except ImportError:
            versions[f'python_{mod}'] = None
    return versions


def dependencies(build):
    deps = []
    for p in json.loads((build / 'lake-manifest.json').read_text())['packages']:
        d = build / '.lake/packages' / p['name'].strip('«»')
        head = run(['git', '-C', str(d), 'rev-parse', 'HEAD'])
        dirty = run(['git', '-C', str(d), 'status', '--porcelain', '--untracked-files=no'])
        deps.append({'name': p['name'], 'url': p.get('url'), 'rev': p.get('rev'),
                     'matches_manifest': head == p.get('rev'), 'clean': dirty == ''})
    return deps


def manifest(build, log, notes):
    build = Path(build).resolve()
    sources = {f: sha256(build / f) for f in source_files(build)}
    working = {f: sha256(HERE / f) for f in source_files(HERE)}
    if working != sources:
        diff = sorted(set(working) ^ set(sources)) + sorted(f for f in sources if working.get(f) not in (None, sources[f]))
        raise SystemExit(f'working tree differs from the built snapshot: {diff[:20]}')
    pins = json.loads((build / 'provenance/generated.json').read_text())
    bad = [p for p, h in pins.items() if sha256(build / p) != h]
    if bad:
        raise SystemExit(f'generated files of the build differ from their pins: {bad[:5]}')
    report = json.loads((build / 'verification.json').read_text())
    if not report.get('success'):
        raise SystemExit('clean build verification did not succeed')
    axiom_sets = {}
    for deps in report['axioms'].values():
        key = ', '.join(deps) or '(none)'
        axiom_sets[key] = axiom_sets.get(key, 0) + 1
    batches = [json.loads(l) for l in (build / 'build-batches.jsonl').read_text().splitlines() if l.strip()]
    verify_rss = None
    if log and Path(log).exists():
        m = re.findall(r'(\d+)\s+maximum resident set size', Path(log).read_text())
        verify_rss = int(m[-1]) if m else None
    status = subprocess.run(['git', '-C', str(REPO), 'status', '--porcelain', '--untracked-files=no'],
                            capture_output=True, text=True, check=True).stdout
    out = {
        'schema': 2,
        'description': 'Clean rebuild of the Lean project from an isolated copy of the repository: sources, '
                       'generated files, inputs, toolchain, dependency revisions, build commands and audit results.',
        'checkout': {
            'repository_commit': run(['git', '-C', str(REPO), 'rev-parse', 'HEAD']),
            'uncommitted_tracked_changes': status.splitlines(),
            'method': 'the files git tracks or would add (`tools/snapshot.py copy-repo`); discriminant.pkl '
                      'restored by scripts/restore_discriminant.py; generated files rebuilt by `make lean-data` '
                      'and checked against provenance/generated.json; compiler extracted from '
                      'lean-toolchain.tar.zst; .lake/packages cloned from the working tree after checking '
                      'lake-manifest.json revisions (Mathlib and Hex are not recompiled); empty .lake/build.',
            'notes': list(notes),
        },
        'public_inputs': {f: sha256(REPO / f) for f in PUBLIC_INPUTS if (REPO / f).exists()},
        'toolchain': {'lean-toolchain': (build / 'lean-toolchain').read_text().strip(),
                      'compiler_archive_sha256': sha256(HERE / 'lean-toolchain.tar.zst')
                      if (HERE / 'lean-toolchain.tar.zst').exists() else None},
        'tools': tool_versions(build),
        'dependencies': dependencies(build),
        'build': {
            'commands': ['make lean-data', 'sh lean/tools/full_build.sh  (batched builds, then python3 verify.py)'],
            'verify_commands': report['commands'],
            'batches': batches,
            'batch_seconds_total': round(sum(b['seconds'] for b in batches), 1),
            'verify_seconds_total': round(sum(c['seconds'] for c in report['commands']), 1),
            'verify_max_rss_bytes': verify_rss,
        },
        'audit': {
            'success': report['success'],
            'trust': report['trust'],
            'audited_declarations': len(report['axioms']),
            'axiom_sets': axiom_sets,
            'headline': {n: report['axioms'].get(n) for n in HEADLINE},
            'axioms': report['axioms'],
        },
        'generated_files_sha256': sha256(build / 'provenance/generated.json'),
        'sources': sources,
    }
    (HERE / SELF).write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
    print(f'wrote {SELF}: {len(sources)} source files, {len(pins)} generated files, '
          f'{len(report["axioms"])} audited declarations')


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    sub.add_parser('list')
    c = sub.add_parser('copy-repo'); c.add_argument('dest')
    m = sub.add_parser('manifest'); m.add_argument('build'); m.add_argument('--log')
    m.add_argument('--note', action='append', default=[])
    args = ap.parse_args()
    if args.cmd == 'list':
        print('\n'.join(source_files()))
    elif args.cmd == 'copy-repo':
        dest = Path(args.dest)
        if dest.exists() and any(dest.iterdir()):
            raise SystemExit(f'{dest} is not empty')
        for f in repo_files():
            (dest / f).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO / f, dest / f)
            shutil.copymode(REPO / f, dest / f)
    else:
        manifest(args.build, args.log, args.note)


if __name__ == '__main__':
    main()
