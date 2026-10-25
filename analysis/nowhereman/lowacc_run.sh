#!/usr/bin/env bash
# ML-DSA-44 low-acceptance count (lowacc.cc, mode lowacc) on one host.  Run inside a shell
# that provides g++ with OpenMP and OpenSSL >= 3.5 (export NIX_ENFORCE_NO_NATIVE=0 inside a
# Nix shell, for -march=native):
#   LABEL=host-a THREADS=200 K0=0 N=1073741824 bash ./lowacc_run.sh
# Environment:
#   LABEL    host label (output directory name)
#   SEED     master seed, 64 hex digits (default SHA-256("lowacc 2026-10-25 p44"), shared by
#            all hosts; hosts split the key range with K0 and N)
#   THREADS  OpenMP threads (default 200)
#   K0 N     first key index and number of keys
#   M        challenges per key (default 16)
#   OUT      output directory (default results/44/lowacc/$LABEL)
set -euo pipefail
cd "$(dirname "$0")"
LABEL=${LABEL:?set LABEL}
T=${THREADS:-200}
K0=${K0:?set K0}
N=${N:?set N}
M=${M:-16}
OUT=${OUT:-results/44/lowacc/$LABEL}
SEED=${SEED:-$(printf "lowacc 2026-10-25 p44" | sha256sum | cut -c1-64)}
BLOCK=67108864
export OMP_NUM_THREADS=$T

g++ -O3 -march=native -fopenmp -std=c++17 -Wall -Wextra lowacc.cc -lcrypto -o lowacc
mkdir -p "$OUT"
{
  date -u
  echo "$LABEL"
  echo "seed $SEED k0 $K0 n $N M $M threads $T"
} > "$OUT/env.txt"
./lowacc --param 44 --seed "$SEED" lowacc "$K0" "$N" "$M" "$BLOCK" > "$OUT/lowacc_44.txt"
echo "exit $? $(date -u)" >> "$OUT/env.txt"
