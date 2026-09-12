#!/usr/bin/env python3
"""Write certificate/manifest.json: SHA-256 digests of the certificate programs, reports, and data files.

With --pack-discriminant, first compress certificate/results/discriminant.pkl (written by a full run)
to the stored artifact certificate/results/discriminant.pkl.gz.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PKL = ROOT / 'certificate/results/discriminant.pkl'
PACKED = ROOT / 'certificate/results/discriminant.pkl.gz'
PATTERNS = ['certificate/tools/*.py', 'certificate/gap/*.g', 'certificate/results/*.json',
            'certificate/results/*.pkl.gz', 'data/*']


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pack-discriminant', action='store_true')
    args = parser.parse_args()
    if args.pack_discriminant:
        PACKED.write_bytes(gzip.compress(PKL.read_bytes(), compresslevel=9, mtime=0))
    paths = sorted({p for pattern in PATTERNS for p in ROOT.glob(pattern) if p.is_file()})
    raw = gzip.decompress(PACKED.read_bytes())
    manifest = {
        'files': [{'path': p.relative_to(ROOT).as_posix(), 'sha256': sha256(p.read_bytes())} for p in paths],
        'discriminant': {
            'compressed_file': PACKED.relative_to(ROOT).as_posix(),
            'compressed_sha256': sha256(PACKED.read_bytes()),
            'uncompressed_sha256': sha256(raw),
            'uncompressed_bytes': len(raw),
        },
    }
    (ROOT / 'certificate/manifest.json').write_text(json.dumps(manifest, indent=1) + '\n')
    print(f'Wrote certificate/manifest.json ({len(paths)} files).')


if __name__ == '__main__':
    main()
