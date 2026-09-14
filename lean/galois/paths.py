"""Locations used by the generators; everything is relative to the Lean project directory `lean/`."""
from pathlib import Path

GENERATORS = Path(__file__).resolve().parent
PROJECT = GENERATORS.parent
REPO = PROJECT.parent
INPUTS = GENERATORS / 'inputs'
F_JSON = REPO / 'data/f.json'
MONODROMY_JSON = REPO / 'data/monodromy.json'
DISCRIMINANT_PKL = REPO / 'certificate/results/discriminant.pkl'
MERIDIAN1_JSON = PROJECT / 'certs/meridian1.json'
