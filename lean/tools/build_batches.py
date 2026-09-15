#!/usr/bin/env python3
"""Build Lean modules in batches, bounding the number of simultaneous kernel replays.

Usage: python3 tools/build_batches.py BATCH_SIZE MODULE... (full module names). For every batch prints the wall
time and, when available, the largest resident set of any process in it (macOS `/usr/bin/time -l`).
Appends a JSON line to $BUILD_LOG_JSONL if set. Exits non-zero at the first failing batch."""
import json, os, re, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
TIME_PREFIX = (['/usr/bin/time', '-l']
               if sys.platform == 'darwin' and os.access('/usr/bin/time', os.X_OK) else [])


def main():
    size, mods = int(sys.argv[1]), sys.argv[2:]
    t0 = time.time()
    for i in range(0, len(mods), size):
        batch = mods[i:i + size]
        start = time.time()
        r = subprocess.run(TIME_PREFIX + ['sh', 'run-lake.sh', 'build'] + batch, cwd=HERE,
                           capture_output=True, text=True)
        m = re.search(r'(\d+)\s+maximum resident set size', r.stderr)
        rss = int(m.group(1)) if m else None
        rec = {'batch': batch, 'exit_code': r.returncode, 'seconds': round(time.time() - start, 1),
               'max_rss_bytes': rss}
        if os.environ.get('BUILD_LOG_JSONL'):
            with open(os.environ['BUILD_LOG_JSONL'], 'a') as fh:
                fh.write(json.dumps(rec) + '\n')
        gb = f'{rss / 2**30:.2f} GB' if rss else '?'
        print(f'[{time.time() - t0:7.0f}s] {batch[0]}..{batch[-1]} rc={r.returncode} '
              f'{rec["seconds"]} s, max RSS {gb}', flush=True)
        if r.returncode:
            for line in (r.stdout + r.stderr).splitlines():
                if 'error' in line:
                    print('   ', line[:300], flush=True)
            raise SystemExit(r.returncode)


if __name__ == '__main__':
    main()
