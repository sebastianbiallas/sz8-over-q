#!/usr/bin/env python3
"""Build a TeX-source arXiv bundle with all JSON files as ancillary data."""

from __future__ import annotations

import io
import tarfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "dist" / "sz8-over-q-arxiv.tar.gz"
REPOSITORY = "https://github.com/sebastianbiallas/sz8-over-q"


def source_files() -> list[Path]:
    files = [ROOT / "main.tex", ROOT / "references.bib", ROOT / "LICENSE"]
    files.extend(sorted((ROOT / "sections").glob("*.tex")))
    return files


def ancillary_files() -> list[Path]:
    files: list[Path] = []
    for directory in (ROOT / "data", ROOT / "certificate"):
        files.extend(directory.rglob("*.json"))
        files.extend(directory.rglob("*.json.gz"))
    return sorted(set(files))


def add_bytes(archive: tarfile.TarFile, name: str, content: bytes) -> None:
    info = tarfile.TarInfo(name)
    info.size = len(content)
    info.mode = 0o644
    archive.addfile(info, io.BytesIO(content))


def main() -> None:
    sources = source_files()
    ancillary = ancillary_files()
    missing = [path for path in sources if not path.is_file()]
    if missing:
        raise SystemExit("missing source files: " + ", ".join(map(str, missing)))
    if not ancillary:
        raise SystemExit("no ancillary JSON files found")

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    readme = (
        "Ancillary data for A regular realization of the Suzuki group Sz(8) over Q\n"
        "\n"
        "The paths below anc/ preserve their locations in the proof repository.\n"
        "They comprise every .json and .json.gz file in data/ and certificate/.\n"
        "File formats and verification stages are described in Section 8 of the paper.\n"
        "The ancillary data and recorded results are released under CC0 1.0.\n"
        "See the top-level LICENSE file for the complete path-based licensing terms.\n"
        f"Repository: {REPOSITORY}\n"
    ).encode("utf-8")

    with tarfile.open(OUTPUT, "w:gz") as archive:
        for path in sources:
            archive.add(path, arcname=path.relative_to(ROOT), recursive=False)
        add_bytes(archive, "anc/README.txt", readme)
        for path in ancillary:
            archive.add(
                path,
                arcname=Path("anc") / path.relative_to(ROOT),
                recursive=False,
            )

    size_mib = OUTPUT.stat().st_size / (1024 * 1024)
    print(f"wrote {OUTPUT.relative_to(ROOT)} ({size_mib:.2f} MiB)")
    print(f"included {len(sources)} source files and {len(ancillary)} ancillary files")


if __name__ == "__main__":
    main()
