# Generators for the `Sz8.Galois` data files

Paths are relative to `lean/` and the repository root. `python3 export_galois.py` regenerates the data
files of `Sz8.Galois`; `--check` (run by `verify.py`) compares them byte for byte and checks
`provenance/export_galois.json`. Lean does not trust these files: each supplies data that kernel-checked
theorems verify.

| Artifact (`Sz8/Galois/`) | Generator | Inputs |
|---|---|---|
| `EncData0–6.lean` | `enc.py` (PARI/GP `polroots`, 160 digits; the enclosure checks are replayed exactly in Python) | `data/f.json`, `certs/meridian1.json` |
| `ThetaData0–6.lean` | `theta.py` (exact Gaussian-integer grouped invariant at the enclosure centres) | `EncData*`, `Sz8/Monodromy/GroupCerts.lean`, `Sz8/Monodromy/MonodromyData.lean`, `inputs/resolvent_coefficients.json` |
| `Resolvent.lean` | `resolvent.py` | `inputs/Resolvent.tpl`, `inputs/resolvent_coefficients.json` |
| `Stab13Data.lean` | `stab13.py` | `data/monodromy.json` |
| `NodeData.lean` | `nodedata.py` (python-flint; about 45 s) | `data/f.json`, `certificate/results/discriminant.pkl` |
| `SepData.lean` | `sepdata.py` (python-flint) | `NodeData.lean` |
| `SuzukiData.lean`; the tables and ovoid list of `Suzuki.lean` (hand-written, checked) | `suzuki.py` | `inputs/suzuki_conj.txt`, `Sz8/Monodromy/GroupCerts.lean` |

`certificate/results/discriminant.pkl` is restored from the tracked `discriminant.pkl.gz` by
`scripts/restore_discriminant.py` (`tools/generate.py` does this when needed).

## Recorded inputs (`inputs/`)

* `resolvent_coefficients.json`: the integer coefficients of `Z₁, Z₂, Z₃`, produced by
  `upstream/invariant/run_invariant.py` (a GAP orbit of the monomial under `N`, PARI/GP power-series roots at
  `t = 0`; about 20 s). Lean proves the resolvent identity from a degree bound and seven pinning points.
* `Resolvent.tpl`: the Lean template of `Resolvent.lean`.
* `suzuki_conj.txt`: GAP's `RepresentativeAction(SymmetricGroup(65), P, N)`, relabelling the ovoid onto `N`,
  produced by `upstream/suzuki/run_gap.py`, which also checks that the 72 matrices generate GAP's
  `SuzukiGroup(IsMatrixGroup, 8)`. Lean checks every generator image and the isomorphism itself.

The PARI inputs of `enc.py` (the polynomial and the disc centres) are built from `data/f.json` and
`certs/meridian1.json`.

## Upstream scripts (`upstream/`)

Not needed to regenerate or check the Lean files; they reproduce the recorded inputs. Set `GAP` to a GAP
executable.

* `invariant/run_invariant.py` (with `orb.g`, `run.gp`, `post.gp`, `coef.gp`; `resolvent.gp` is the PARI form
  of the resolvent): rederives `inputs/resolvent_coefficients.json` and compares.
* `suzuki/run_gap.py` (with `gap1.g`, which prints GAP's own generators): the GAP cross-checks and the
  relabelling; `--write` refreshes `inputs/suzuki_conj.txt`.
