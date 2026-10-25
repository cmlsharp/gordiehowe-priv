#!/usr/bin/env bash
# Full experiment.  Run inside a shell that provides g++ and OpenSSL >= 3.5:
#   bash ./run.sh
# Environment: THREADS (default 48), SCALE (divides every N; SCALE=100 for a
# quick check).
set -euo pipefail
cd "$(dirname "$0")"
T=${THREADS:-48}
SCALE=${SCALE:-1}
OUT=${OUT:-results}

g++ -O2 -std=c++17 -Wall -Wextra -pthread nm_attack.cc -lcrypto -o nm_attack
mkdir -p "$OUT"
{
  date -u
  hostname
  openssl version
  g++ --version | head -1
  echo "threads $T scale $SCALE"
} > "$OUT/env.txt"

# Test sizes (pairs: N real and N simulated presentations).
declare -A N_BEST=([44]=6000000 [65]=40000000 [87]=12000000)
declare -A N_FIX=([44]=12000000 [65]=100000000 [87]=24000000)
NCAL=2000000
NSEL=20000

field() { awk -v k="$2" '{for (i = 1; i < NF; i++) if ($i == k) print $(i + 1)}' "$1" | tail -1; }

for p in 65 44 87; do
  d="$OUT/$p"
  mkdir -p "$d"
  ./nm_attack --param "$p" selftest 1000 > "$d/selftest.txt"
  ./nm_attack --param "$p" --threads "$T" select 64 "$NSEL" > "$d/select.txt"
  best=$(field "$d/select.txt" best_seed)
  for seed in "$best" 0; do
    if [[ $seed == 0 ]]; then n=$((N_FIX[$p] / SCALE)); else n=$((N_BEST[$p] / SCALE)); fi
    ./nm_attack --param "$p" --threads "$T" calib "$seed" "$NCAL" > "$d/calib_seed$seed.txt"
    th=$(field "$d/calib_seed$seed.txt" theta)
    ./nm_attack --param "$p" --threads "$T" test "$seed" "$th" "$n" \
      > "$d/test_seed$seed.txt" 2> "$d/test_seed$seed.log"
    [[ $best == 0 ]] && break
  done
done
grep -h -E '^(summary|calib|test|RESULT|aux|selftest)' "$OUT"/*/*.txt > "$OUT/summary.txt"
echo done >> "$OUT/env.txt"
