#!/bin/sh
# Clean rebuild of the Lean project in an isolated copy of the repository, then reproducibility.json.
# Usage: sh lean/tools/clean_rebuild.sh DEST   (DEST must not exist; needs git, make, python3 with sympy and
# python-flint, gp; the compiler archive lean/lean-toolchain.tar.zst and dependencies in lean/.lake/packages)
set -eu
project=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
repo=$(dirname "$project")
dest=$1
[ ! -e "$dest" ] || { echo "$dest already exists" >&2; exit 1; }
mkdir -p "$dest/sz8-over-q"
dest=$(CDPATH= cd -- "$dest" && pwd)
root="$dest/sz8-over-q"
echo "=== copy of the repository files git tracks or would add ($(git -C "$repo" rev-parse HEAD)) into $root"
python3 "$project/tools/snapshot.py" copy-repo "$root"
echo "=== make lean-data"
(cd "$root" && make lean-data)
echo "=== compiler from lean-toolchain.tar.zst"
tar --zstd -xf "$project/lean-toolchain.tar.zst" -C "$root/lean"
echo "=== dependencies (copy-on-write clone of .lake/packages, checked against lake-manifest.json)"
mkdir -p "$root/lean/.lake"
cp -Rc "$project/.lake/packages" "$root/lean/.lake/"
python3 - "$root/lean" <<'PY'
import json, subprocess, sys
from pathlib import Path
b = Path(sys.argv[1])
packages = json.loads((b / 'lake-manifest.json').read_text())['packages']
bad = []
for p in packages:
    d = b / '.lake/packages' / p['name'].strip('«»')
    head = subprocess.run(['git', '-C', str(d), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', '-C', str(d), 'status', '--porcelain', '--untracked-files=no'],
                           capture_output=True, text=True).stdout.strip()
    if head != p['rev'] or dirty:
        bad.append((p['name'], head, p['rev'], bool(dirty)))
if bad:
    raise SystemExit(f'dependency mismatch: {bad}')
print('all', len(packages), 'packages at pinned revisions, clean')
PY
[ ! -e "$root/lean/.lake/build" ] || { echo "unexpected .lake/build" >&2; exit 1; }
echo "=== full build"
(cd "$root/lean" && sh tools/full_build.sh > full_build.log 2>&1) || { tail -40 "$root/lean/full_build.log"; exit 1; }
tail -3 "$root/lean/full_build.log"
echo "=== manifest"
python3 "$project/tools/snapshot.py" manifest "$root/lean" --log "$root/lean/full_build.log"
