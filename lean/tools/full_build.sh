#!/bin/sh
# End-to-end build from an empty .lake/build (generated files must exist: `make lean-data`), then verify.py.
# Memory-heavy modules are built in small batches first (Cert*: ~1.3 GB each; EncData: ~4.4 GB; ThetaData:
# ~5.2 GB); the remaining modules are then built by verify.py with Lake's default parallelism.
set -eu
cd "$(dirname "$0")/.."
export BUILD_LOG_JSONL="${BUILD_LOG_JSONL:-$PWD/build-batches.jsonl}"
certs=$(for f in $(seq 0 104); do printf "Sz8.Monodromy.Meridian.Cert%03d " "$f"; done)
python3 tools/build_batches.py 10 $certs
legs=$(ls Sz8/Monodromy/Meridian | sed -n 's/^\(Legs[B]*[0-9]*\)\.lean$/Sz8.Monodromy.Meridian.\1/p' | tr '\n' ' ')
python3 tools/build_batches.py 7 $legs Sz8.Monodromy.Meridian.Chain2 Sz8.Monodromy.Meridian.Gamma1 Sz8.Monodromy.Meridian.Gamma2
python3 tools/build_batches.py 3 Sz8.Galois.ThetaData0 Sz8.Galois.ThetaData1 Sz8.Galois.ThetaData2 \
  Sz8.Galois.ThetaData3 Sz8.Galois.ThetaData4 Sz8.Galois.ThetaData5 Sz8.Galois.ThetaData6
python3 tools/build_batches.py 1 Sz8.Galois.NodeData Sz8.Galois.SepData
echo "=== verify.py"
python3 verify.py
