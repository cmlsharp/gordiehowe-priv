#!/usr/bin/env python3
"""Confidence lower bound on Adv(g) from edge_test outputs (see edge_test.cc header).

usage: edge_test_bound.py [--log2delta 40] FILE...   (files of one parameter set, distinct seeds)

Pools the final block line of each file (sumY, sumY2, units), then applies Maurer & Pontil
(2009, Theorem 4) to (Y + B)/(2B) in [0, 1]:
  E Y >= mean - sqrt(2 V ln(2/delta)/n) - 2B * 7 ln(2/delta) / (3 (n-1)),
and Adv(g) >= (1/2) Pr[E] (LCB - 2/8193^2), Pr[E] computed exactly (rational arithmetic).
"""
import math, re, sys
from fractions import Fraction

Q = 8380417
K = {"ML-DSA-44": 4, "ML-DSA-65": 6, "ML-DSA-87": 8}


def pr_E(k):
    pe = Fraction(8193, Q)
    p2 = Fraction(256 * 255 // 2) * pe ** 2 * (1 - pe) ** 254   # a component has exactly 2 edges
    return 1 - (1 - p2) ** k


def main():
    args = sys.argv[1:]
    l2d = 40
    if args and args[0] == "--log2delta":
        l2d = int(args[1]); args = args[2:]
    lnd = math.log(2) * (l2d + 1)          # ln(2/delta), delta = 2^-l2d
    n = 0; S = 0.0; S2 = 0.0; B = None; name = None; seeds = set()
    for fn in args:
        head = None; last = None
        for line in open(fn):
            if line.startswith("run edge_test"):
                head = line
            elif line.startswith("block"):
                last = line
            elif line.startswith("RANGE VIOLATION"):
                sys.exit(f"{fn}: range violation")
        if head is None or last is None:
            sys.exit(f"{fn}: no data")
        m = re.search(r"param (\S+) master (\S+) .* B ([0-9.]+)", head)
        nm, seed, b = m.group(1), m.group(2), float(m.group(3))
        if name and nm != name:
            sys.exit("mixed parameter sets")
        if seed in seeds:
            sys.exit(f"{fn}: repeated master seed")
        seeds.add(seed); name = nm
        B = b if B is None else max(B, b)
        f = dict(re.findall(r"(\w+) ([-+0-9.eE]+)", last))
        nu = int(f["units"]); n += nu
        S += float(f["sumY"]); S2 += float(f["sumY2"])
    mean = S / n
    var = (S2 - S * S / n) / (n - 1)
    var_term = math.sqrt(2 * var * lnd / n)
    rng_term = 2 * B * 7 * lnd / (3 * (n - 1))
    lcb = mean - var_term - rng_term
    PE = pr_E(K[name])
    PEf = float(PE)
    adv = 0.5 * PEf * (lcb - 2 / 8193 ** 2)
    print(f"{name}: n={n} mean={mean:.6e} var={var:.4e} B={B:.6f} delta=2^-{l2d}")
    print(f"  var term {var_term:.3e}  range term {rng_term:.3e}  LCB(E[m|E]) = {lcb:.6e}")
    print(f"  Pr[E] = {PEf:.10f} (exact rational, {PE.numerator.bit_length()}-bit numerator)")
    if adv > 0:
        print(f"  Adv(g) >= {adv:.6e} = 2^{math.log2(adv):.3f}  (confidence 1 - 2^-{l2d})")
    else:
        print(f"  Adv(g) lower bound not positive ({adv:.3e}); more units needed")
    # projection: units needed so that the deductions are <= 10% of the mean
    for frac in (0.10, 0.05):
        t = frac * mean
        # solve sqrt(2 var lnd / N) + 14 B lnd / (3N) = t
        a = 14 * B * lnd / 3; c = math.sqrt(2 * var * lnd)
        x = (-c + math.sqrt(c * c + 4 * t * a)) / (2 * a)     # x = 1/sqrt(N): a x^2 + c x = t
        print(f"  units for deductions <= {frac:.0%} of the mean: {1 / x ** 2:.3e}")


main()
