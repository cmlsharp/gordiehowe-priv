-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Base
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CausalRun

@[expose] public section

/-!
# The honest writes of the compiler data

The pieces of the honest prover of the compiler data of a composition (`GordieHowe.SPBCS.Base`,
`GordieHowe/SPBCS/Base.lean`), for every causal prover (`CausalProver`). The namespace
`GordieHowe.SPBCS` states completeness for the spBCS compiler with them
(`GordieHowe.SPBCS.prob_not_accepts_prove_le`, `GordieHowe/SPBCS/Complete.lean`).

* `ComponentModel.Encoder`: the honest encoding of a component's messages (the column bytes of
  each leaf and the write carrying given roots).
* `WriteFn`, `honestWrite`, `leafFn`: the honest writes of every leaf as functions of the
  challenges and the oracle, and the honest leaves of every position;
  `honestWrite_congr_oracle`: the honest writes depend on the oracle only through its answers.
* `overrun`: the samplers' rejection probabilities summed over all challenges of all leaves.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

/-! ### Encoders of components -/

namespace ComponentModel

variable {m : ℕ} {P : ProtocolSpec m} [∀ i, Fintype (P.Challenge i)]
  [∀ i, DecidableEq (P.Challenge i)] (C : ComponentModel P k kN L e)

/-- **The honest encoding of a component's messages**: the column bytes of
each leaf of each tree of a prover round, and the write carrying given roots, with the laws that
the write carries the roots and that the message read back from views holding the columns is the
message. -/
structure Encoder where
  /-- The column bytes of each leaf. -/
  cols : (i : P.MessageIdx) → P.Type i.1 → (τ : Fin (C.nTrees i)) → Fin (C.nLeaves i τ) → Bytes L
  /-- The write carrying the roots. -/
  write : (i : P.MessageIdx) → P.Type i.1 → (Fin (C.nTrees i) → Digest k) → C.MessageWrite i
  rootOf_write : ∀ i msg rts τ, C.rootOf i (write i msg rts) τ = rts τ
  msg_write : ∀ i msg rts (vw : (τ : Fin (C.nTrees i)) → MerkleView k kN L (C.nLeaves i τ)),
    (∀ τ j, ∃ ν, (vw τ).leaves j = some ⟨ν, cols i msg τ j⟩) → C.msg i (write i msg rts) vw = msg

end ComponentModel

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-- **The overrun term** of the composite: the samplers' rejection probabilities summed over all
challenges of all leaves. -/
noncomputable def overrun : ℝ≥0∞ :=
  ∑ c : ChIdx P t, ((M.comp c.leaf.label).sampler c.idx).rejectionProb

/-- The overrun is finite. -/
theorem overrun_ne_top : M.overrun ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun _ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (Sampler.rejectionProb_le_one _)

/-- A write function: the write of each prover round of each leaf as a function of its message. -/
abbrev WriteFn : Type := (p : t.Leaf) → (i : (P p.label).MessageIdx) → (P p.label).Type i.1 →
  (M.comp p.label).MessageWrite i

variable {M} (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS)

/-- Leaf `j` of tree `τ` of round `i` of leaf `p` with message `msg`: the Merkle salt of the
position and the column bytes; past the last leaf, a fixed value. -/
def leafFn (p : t.Leaf) (i : (P p.label).MessageIdx) (msg : (P p.label).Type i.1)
    (τ : Fin ((M.comp p.label).nTrees i)) (j : ℕ) : MerkleLeaf kN L :=
  if hj : j < (M.comp p.label).nLeaves i τ then
    ⟨ν ⟨p, ⟨i, τ, ⟨j, hj⟩⟩⟩, (E p.label).cols i msg τ ⟨j, hj⟩⟩
  else ⟨fun _ => 0, ⟨0, Fin.elim0⟩⟩

theorem leafFn_val (p : t.Leaf) (i : (P p.label).MessageIdx) (msg : (P p.label).Type i.1)
    (τ : Fin ((M.comp p.label).nTrees i)) (j : Fin ((M.comp p.label).nLeaves i τ)) :
    leafFn E ν p i msg τ j = ⟨ν ⟨p, ⟨i, τ, j⟩⟩, (E p.label).cols i msg τ j⟩ := by
  simp [leafFn]

/-- The honest write of round `i` of leaf `p` with message `msg`: the encoder's write at the
honest roots of its trees. -/
def honestWrite (h : Query k kN kS L → Out k e) : M.WriteFn := fun p i msg =>
  (E p.label).write i msg fun τ => MerkleTree.root h ((M.comp p.label).nLeaves i τ)
    (leafFn E ν p i msg τ)

variable [∀ j i, Nonempty ((P j).Challenge i)]

variable {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x)

variable (h : Query k kN kS L → Out k e)

/-! ### The probability bound -/

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The honest write function reads the oracle only at `leaf` and `node` queries. -/
theorem honestWrite_congr_oracle {h₁ h₂ : Query k kN kS L → Out k e}
    (hq : ∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) :
    honestWrite (M := M) E ν h₁ = honestWrite E ν h₂ := by
  funext p i msg
  unfold honestWrite
  congr 1
  funext τ
  exact MerkleTree.root_congr (fun a b => hq _ id) (fun l r => hq _ id) _ _

end Base

end GordieHowe.SPBCS
