// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the spectral sums of spectral.h as values, without its
// builders, so that an assert_mod declaration (system_core.h's ModDecl)
// can hold a spectral right-hand side.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_SUM_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_SUM_H_

#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"

namespace proofs::gordiehowe::ops {

// scale * spec[k] * Ntt(x)[k], spec read at an offset (in elements) of its
// node, x at an offset of its expression's coordinates. KEY names the
// operand x: a handle's node, or the expression itself, so that an operand
// passed twice is transformed once.
template <class F>
struct SpectralTerm {
  Ref<F> spec;
  size_t spec_at = 0;
  ExprPtr<F> x;
  size_t x_at = 0;
  typename F::Elt scale;
  std::pair<size_t, const void *> key;
};

// A sum of spectral terms under one staged transform (OP, the Ntt
// operator; NTT its stages).
template <class F>
struct SpectralSum {
  std::shared_ptr<const StagedNtt<F>> ntt;
  Op<F> op;
  std::vector<SpectralTerm<F>> terms;
};

// One spectral row: Ntt(lhs) == rhs, LHS an expression of n coordinates.
template <class F>
struct SpectralRow {
  ExprPtr<F> lhs;
  SpectralSum<F> rhs;
};

}  // namespace proofs::gordiehowe::ops

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_SUM_H_
