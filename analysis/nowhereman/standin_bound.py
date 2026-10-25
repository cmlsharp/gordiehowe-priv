#!/usr/bin/env python3
"""Confidence bounds on standinGap from standin_gap block lines.

Each unit statistic Z lies in [-1, 1] and the units are i.i.d. with mean
standinGap.  With Y = (Z + 1)/2 in [0, 1], Maurer and Pontil (2009, Theorem 4)
give, with probability at least 1 - delta,

    E[Y] >= Ybar - sqrt(2 V_n ln(2/delta) / n) - 7 ln(2/delta) / (3 (n - 1)),

V_n the unbiased sample variance of Y.  In terms of Z (V_Z = 4 V_n):

    standinGap >= Zbar - sqrt(2 V_Z ln(2/delta) / n) - 14 ln(2/delta) / (3 (n - 1)).

The two-sided interval applies the bound to Z and to -Z at delta/2 each.  The
script also prints Hoeffding's lower bound Zbar - sqrt(2 ln(1/delta) / n) and a
CLT z-score (not a bound).

Usage: standin_bound.py [--field z|za] [--log2delta 40] FILE...
"""

import argparse
import math


def merge(a, b):
    n1, m1, q1 = a
    n2, m2, q2 = b
    n = n1 + n2
    if n == 0:
        return (0, 0.0, 0.0)
    d = m2 - m1
    return (n, m1 + d * n2 / n, q1 + q2 + d * d * n1 * n2 / n)


def read(files, field):
    acc = (0, 0.0, 0.0)
    extra = {"own": 0.0, "other": 0.0, "attempts": 0, "mismatch": 0, "secs": 0.0}
    seen = set()
    headers = []
    for f in files:
        master = None
        for line in open(f):
            t = line.split()
            if t and t[0] == "run":
                headers.append(line.strip())
                kv = dict(zip(t[1::2], t[2::2]))
                master = (kv["mode"], kv["param"], kv["master"])
            if not t or t[0] != "block":
                continue
            kv = dict(zip(t[1::2], t[2::2]))
            # A unit is identified by (mode, param, master seed, unit index).
            key = (master, kv["u0"])
            if key in seen:
                continue
            seen.add(key)
            n = int(kv["n"])
            acc = merge(acc, (n, float(kv[field + "_mean"]), float(kv[field + "_m2"])))
            extra["own"] += float(kv["own"]) * n
            extra["other"] += float(kv["other"]) * n
            extra["attempts"] += int(kv["attempts"])
            extra["mismatch"] += int(kv["mismatch"])
            extra["secs"] += float(kv["secs"])
    return acc, extra, headers


def bounds(n, mean, m2, log2delta):
    var = m2 / (n - 1)
    L1 = math.log(2) * (log2delta + 1)  # ln(2/delta)
    L2 = math.log(2) * (log2delta + 2)  # ln(4/delta)
    lo = mean - math.sqrt(2 * var * L1 / n) - 14 * L1 / (3 * (n - 1))
    lo2 = mean - math.sqrt(2 * var * L2 / n) - 14 * L2 / (3 * (n - 1))
    hi2 = mean + math.sqrt(2 * var * L2 / n) + 14 * L2 / (3 * (n - 1))
    hoeff = mean - math.sqrt(2 * math.log(2) * log2delta / n)
    se = math.sqrt(var / n)
    return var, lo, lo2, hi2, hoeff, se


def lg(x):
    return "%.3f" % math.log2(x) if x > 0 else "neg"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--field", default="z")
    ap.add_argument("--log2delta", type=float, default=40)
    ap.add_argument("files", nargs="+")
    a = ap.parse_args()
    (n, mean, m2), ex, headers = read(a.files, a.field)
    for h in headers:
        print("#", h)
    var, lo, lo2, hi2, hoeff, se = bounds(n, mean, m2, a.log2delta)
    print("field %s N %d mean %.6e (log2 %s) var %.6e sd %.4e se %.3e z %.2f" %
          (a.field, n, mean, lg(mean), var, math.sqrt(var), se, mean / se))
    print("own_mean %.9f other_mean %.9f attempts_per_unit %.4f mismatch %d block_secs %.1f" %
          (ex["own"] / n, ex["other"] / n, ex["attempts"] / n, ex["mismatch"], ex["secs"]))
    print("EB lower bound (1-2^-%g, one-sided) %.6e (log2 %s)" % (a.log2delta, lo, lg(lo)))
    print("EB two-sided interval (1-2^-%g) [%.6e, %.6e]" % (a.log2delta, lo2, hi2))
    print("Hoeffding lower bound %.6e; implied advantage lower bound (EB/2) %.6e (log2 %s)" %
          (hoeff, lo / 2, lg(lo / 2)))
    # Projection: units needed so that the EB lower bound reaches a target
    # when the true mean equals the measured mean and the variance is as measured.
    L1 = math.log(2) * (a.log2delta + 1)
    for tgt_frac in (0.25, 0.5):
        tgt = mean * tgt_frac
        if mean <= 0:
            break
        nn = 10.0
        while nn < 1e16:
            if mean - math.sqrt(2 * var * L1 / nn) - 14 * L1 / (3 * nn) >= tgt:
                break
            nn *= 1.05
        print("projection: N for EB lower bound >= %.2f * mean: %.3e units" % (tgt_frac, nn))


if __name__ == "__main__":
    main()
