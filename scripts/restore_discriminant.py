#!/usr/bin/env python3
"""Restore the recorded discriminant pickle, checking its digests."""
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def restore():
    info = json.loads((ROOT / 'certificate/manifest.json').read_text())['discriminant']
    packed = (ROOT / info['compressed_file']).read_bytes()
    if hashlib.sha256(packed).hexdigest() != info['compressed_sha256']:
        raise ValueError('Compressed discriminant digest mismatch')
    raw = gzip.decompress(packed)
    if hashlib.sha256(raw).hexdigest() != info['uncompressed_sha256']:
        raise ValueError('Uncompressed discriminant digest mismatch')
    target = ROOT / 'certificate/results/discriminant.pkl'
    target.write_bytes(raw)
    return target


if __name__ == '__main__':
    print(restore())
