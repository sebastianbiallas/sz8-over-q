#!/usr/bin/env python3
"""The text of Sz8/Galois/Resolvent.lean: `inputs/Resolvent.tpl` with the recorded coefficients of `Z₁, Z₂, Z₃`."""
import json

from paths import INPUTS


def polyZ(cs):
    parts = []
    for k, c in enumerate(cs):
        parts.append(f"C ({c} : ℤ)" if k == 0 else (f"C ({c} : ℤ) * X" if k == 1 else f"C ({c} : ℤ) * X ^ {k}"))
    return " +\n    ".join(parts)


def poly(cs):
    parts = []
    for k, c in enumerate(cs):
        parts.append(f"C ({c} : ℚ)" if k == 0 else (f"C ({c} : ℚ) * X" if k == 1 else f"C ({c} : ℚ) * X ^ {k}"))
    return " +\n    ".join(parts)


def generate():
    d = json.loads((INPUTS / "resolvent_coefficients.json").read_text())
    E1, E2, E3 = d["Z1"], d["Z2"], d["Z3"]
    tpl = (INPUTS / "Resolvent.tpl").read_text()
    return (tpl.replace('@E1@', poly(E1)).replace('@E2@', poly(E2)).replace('@E3@', poly(E3))
            .replace('@Z1@', polyZ(E1)).replace('@Z2@', polyZ(E2)).replace('@Z3@', polyZ(E3)))
