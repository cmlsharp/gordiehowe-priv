#!/usr/bin/env bash
# Edge-pair test lower bound (edge_test.cc) on one host.  Run inside a shell that
# provides g++ with OpenMP and OpenSSL >= 3.5 (export NIX_ENFORCE_NO_NATIVE=0
# inside a Nix shell, for -march=native):
#   LABEL=host-a THREADS=200 N65=3000000000 bash ./edge_test_run.sh
# Environment:
#   LABEL    host label; the master seed is SHA-256("edge_test final 2026-10-24 $LABEL")
#   SEED     optional master seed (64 hex digits) overriding the one derived from LABEL
#   THREADS  OpenMP threads (default 200)
#   OUT      output directory (default results/edge-$LABEL)
#   N44 N65 N87  units per parameter set (a phase is skipped when its N is unset)
# Each phase writes OUT/edge_<param>.txt; edge_test_bound.py turns the files of one
# parameter set (from one or more hosts, distinct labels) into the bound.
set -euo pipefail
cd "$(dirname "$0")"
LABEL=${LABEL:?set LABEL}
T=${THREADS:-200}
OUT=${OUT:-results/edge-$LABEL}
SEED=${SEED:-$(printf "edge_test final 2026-10-24 %s" "$LABEL" | sha256sum | cut -c1-64)}
BLOCK=20000000
export OMP_NUM_THREADS=$T

g++ -O3 -march=native -fopenmp -std=c++17 -Wall -Wextra edge_test.cc -lcrypto -o edge_test
mkdir -p "$OUT"
{
  date -u
  hostname
  openssl version
  g++ --version | head -1
  echo "label $LABEL master_seed $SEED threads $T N44 ${N44:-} N65 ${N65:-} N87 ${N87:-}"
} > "$OUT/env.txt"
for p in 65 44 87; do
  ./edge_test --param "$p" --seed "$SEED" selftest 4000 > "$OUT/selftest_$p.txt"
done
for p in 65 44 87; do
  v="N$p"
  n=${!v:-}
  [ -z "$n" ] && continue
  ./edge_test --param "$p" --seed "$SEED" run 0 "$n" "$BLOCK" > "$OUT/edge_$p.txt"
  echo "phase $p done $(date -u)" >> "$OUT/env.txt"
done
echo done >> "$OUT/env.txt"
