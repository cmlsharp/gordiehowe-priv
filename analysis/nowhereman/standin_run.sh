#!/usr/bin/env bash
# standinGap measurement on one host.  Run inside a shell that provides g++
# with OpenMP and OpenSSL >= 3.5 (export NIX_ENFORCE_NO_NATIVE=0 inside a Nix
# shell, for -march=native):
#   LABEL=host-a THREADS=200 N44I=... bash ./standin_run.sh
# Environment:
#   LABEL    host label; the master seed is SHA-256("standin final 2026-10-24 $LABEL")
#   SEED     optional master seed (64 hex digits) overriding the one derived from LABEL
#   THREADS  OpenMP threads (default 200)
#   OUT      output directory (default results/standin-$LABEL)
#   N44I N44D N65I N65D  units for 44 ideal, 44 deployed, 65 ideal, 65 deployed
#   PHASES   subset of "44i 44d 65i 65d" (default all four)
# Each phase writes OUT/<param>_<ideal|deployed>.txt; standin_bound.py turns
# one or more of these (from several hosts) into the confidence bounds.
set -euo pipefail
cd "$(dirname "$0")"
LABEL=${LABEL:?set LABEL}
T=${THREADS:-200}
OUT=${OUT:-results/standin-$LABEL}
PHASES=${PHASES:-"44i 44d 65i 65d"}
SEED=${SEED:-$(printf "standin final 2026-10-24 %s" "$LABEL" | sha256sum | cut -c1-64)}
BLOCK=5000000
export OMP_NUM_THREADS=$T

g++ -O3 -march=native -fopenmp -std=c++17 -Wall -Wextra standin_gap.cc -lcrypto -o standin_gap
mkdir -p "$OUT"
{
  date -u
  hostname
  openssl version
  g++ --version | head -1
  echo "label $LABEL master_seed $SEED threads $T"
  echo "N44I ${N44I:-} N44D ${N44D:-} N65I ${N65I:-} N65D ${N65D:-} phases $PHASES"
} > "$OUT/env.txt"
for p in 44 65; do
  ./standin_gap --param "$p" --seed "$SEED" selftest 2000 200 1000 2000 200 > "$OUT/selftest_$p.txt"
done
for ph in $PHASES; do
  case $ph in
    44i) ./standin_gap --param 44 --seed "$SEED" --K 2 --M 1 ideal 0 "$N44I" "$BLOCK" > "$OUT/44_ideal.txt" ;;
    44d) ./standin_gap --param 44 --seed "$SEED" --K 2 --M 1 deployed 0 "$N44D" "$BLOCK" > "$OUT/44_deployed.txt" ;;
    65i) ./standin_gap --param 65 --seed "$SEED" --K 2 --M 1 ideal 0 "$N65I" "$BLOCK" > "$OUT/65_ideal.txt" ;;
    65d) ./standin_gap --param 65 --seed "$SEED" --K 2 --M 1 deployed 0 "$N65D" "$BLOCK" > "$OUT/65_deployed.txt" ;;
  esac
  echo "phase $ph done $(date -u)" >> "$OUT/env.txt"
done
echo done >> "$OUT/env.txt"
