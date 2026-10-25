set -e
# WORKDIR: directory holding the standin_gap binary and the pilot/ output directory.
cd "${WORKDIR:?usage: WORKDIR=<dir with standin_gap and pilot/> bash $0}"
export OMP_NUM_THREADS=200
for p in 44 65; do
  ./standin_gap --param $p --seed 7a721886e5fe7ba6bda0dc679d14a24df5400be4bba4cbe8bb70912649e9fe38 --K 2 --M 1 deployed 30000000 1000000 250000 > pilot/deployed_${p}_K2M1.txt
  ./standin_gap --param $p --seed 7a721886e5fe7ba6bda0dc679d14a24df5400be4bba4cbe8bb70912649e9fe38 uniform 40000000 400 20000 > pilot/uniform_${p}.txt
done
