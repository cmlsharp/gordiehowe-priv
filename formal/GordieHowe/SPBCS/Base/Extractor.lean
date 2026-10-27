-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Base.Stability
public import GordieHowe.SPBCS.Extraction.Transcript
public import GordieHowe.Model.QROM.Lifting
public import GordieHowe.Model.QROM.Expansion

@[expose] public section

/-!
# The database extractor of the compiler data

The database extractor of the compiler data of a composition (`GordieHowe.SPBCS.Base`), on a
database whose `transcript` inputs encode causal pasts (`Base.enc`).

* `treeProg`: the opening program of a tree at the positions the query phase reads;
  `openedAs_views_of_check`: at a database without a digest collision that records these programs'
  queries, the leaves of a proof whose openings check are those of the database's views.
* `dbExtract`: the database extractor at a statement: for each recorded salt and each recorded
  `transcript` input that decodes to the salt, the statement and the content of a challenge's
  causal past, the causal extractor on the past read from `D`. `extracts`: the databases from
  which it returns a witness; `mem_extracts_of`: one recorded chain input from which a witness is
  extracted suffices.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-! ### The verifier's queries as a classical program -/

section Program

variable (x : X) (π : M.NIProof)

variable [∀ j i, Nonempty ((P j).Challenge i)]

/-- The opening program of tree `τ` (`MerkleFormat.treeProg`) at the positions `ps` and the
leaves of `π`. -/
def treeProg (ps : List M.Pos) (τ : M.Tree) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k)) :=
  M.opening.treeProg ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
    ((M.openedIn τ ps π.leaves).map Prod.fst) ((M.openedIn τ ps π.leaves).map Prod.snd) (π.paths τ)

end Program

/-! ### Extraction reads off prefixes -/

/-- **An extraction of a chain at `m` rounds restricts to `r ≤ m` rounds.** -/
theorem extLeaf_of_le (D : ODB k kN kS L e) (x : X) (σ : FiatShamirSalt kS)
    (chs : (r : t.Leaf) → M.Items r) (q : t.Leaf) (l : M.Items q) {m : ℕ} (hm : m ≤ n q.label)
    {tr : (P q.label).Transcript ⟨m, by omega⟩} (h : M.extLeaf D x σ chs q l m hm = some tr)
    (r : ℕ) (hr : r ≤ m) :
    M.extLeaf D x σ chs q l r (hr.trans hm) = some (tr.take ⟨r, by omega⟩ hr) := by
  have hsteps := M.step_of_extLeaf D x σ chs q l m hm h
  have hall : ∀ j (hj : j < r), (M.step D x σ chs q l j (by omega)).isSome := fun j hj => by
    rw [hsteps j (by omega)]
    rfl
  have hstep_r : ∀ j (hj : j < n q.label), j < r → (M.step D x σ chs q l j hj).isSome :=
    fun j hj hjr => hall j hjr
  obtain ⟨tr', htr'⟩ : ∃ tr', M.extLeaf D x σ chs q l r (hr.trans hm) = some tr' := by
    suffices H : ∀ r' (hr' : r' ≤ r), (M.extLeaf D x σ chs q l r' (hr'.trans (hr.trans hm))).isSome from
      Option.isSome_iff_exists.1 (H r le_rfl)
    intro r'
    induction r' with
    | zero => intro _; rfl
    | succ r' ih =>
      intro hr'
      obtain ⟨tr₀, h₀⟩ := Option.isSome_iff_exists.1 (ih (by omega))
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hall r' (by omega))
      rw [extLeaf_succ, h₀, Option.bind_some, hv, Option.map_some]
      rfl
  rw [htr']
  congr 1
  funext i
  have h1 := M.step_of_extLeaf D x σ chs q l r (hr.trans hm) htr' i.1 i.2
  have h2 := hsteps i.1 (by have hi : i.1 < r := i.2; omega)
  exact Option.some_inj.1 (h1.symm.trans h2)

/-! ### The verifier's queries -/

section Queries

variable (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof)

variable [∀ j i, Nonempty ((P j).Challenge i)]

variable {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem mem_trees {ps : List M.Pos} {q : M.Pos} (hq : q ∈ ps) : q.treeOf ∈ M.trees ps :=
  List.mem_dedup.2 (List.mem_map.2 ⟨q, hq, rfl⟩)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem mem_openedIn {ps : List M.Pos} {as : List (MerkleLeaf kN L)} {q : M.Pos}
    {a : MerkleLeaf kN L} (hqa : (q, a) ∈ ps.zip as) :
    (q.pos.leaf.1, a) ∈ M.openedIn q.treeOf ps as :=
  List.mem_filterMap.2 ⟨(q, a), hqa, by simp⟩

end Queries

/-! ### The database extractor -/

section Extractor

variable {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)

/-- The challenge at round `r` of leaf `p`, if `r` is a challenge round. -/
def chAt (p : t.Leaf) (r : ℕ) : Option (P p.label).ChallengeIdx :=
  if h : r < n p.label then
    if hd : (P p.label).dir ⟨r, h⟩ = .P_to_V then none else some ((P p.label).chIdx ⟨r, h⟩ hd)
  else none

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] in
theorem chAt_idx (c : ChIdx P t) : chAt c.leaf c.idx.1.1 = some c.idx := by
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
  simp only [chAt, c.idx.1.2, ↓reduceDIte, hd]
  rfl

/-- The witness the causal extractor reads at the statement `x` and the salt `σ` from one
recorded query: for a `transcript` input that decodes to `σ`, `x` and the content of a chain
input whose own items end before a challenge round, the extractor on the causal past read from
`D`. -/
def candidate [DecidableEq X] (x : X) (D : ODB k kN kS L e) (σ : FiatShamirSalt kS) :
    Query k kN kS L → Option Wit
  | .transcript b => (M.enc.decode b).bind fun xc =>
      if xc.1 = ⟨σ, x⟩ then (chAt xc.2.leaf xc.2.own.length).bind fun i =>
        (M.extPast D x σ xc.2.chains ⟨xc.2.leaf, i⟩ xc.2.own).map (E ⟨xc.2.leaf, i⟩ x)
      else none
  | _ => none

/-- **The database extractor at the statement `x`** (`LExtract` with the causal extractor `E`,
CMS19 section 8.5.2, p. 44): for each salt of a recorded `xof` query, the witnesses `E` reads at
that salt from the recorded `transcript` inputs of `D` that decode to `x` and the content of a
challenge's causal past.

Running time, in the database size `|D|`, the input length `L`, the number of leaves and their
rounds: one scan of the keys for the recorded salts (at most `|D|`); for each salt and each key,
one run of `enc.decode` on at most `L` bytes (for `CausalEncoding.bytes`, the decoder of the
statement codec, then at most one label comparison and one item parse per item for each leaf),
then `extPast`: at most `t.size n` calls of `step`, each two lookups and one encoding of a chain
input, or one Merkle view per tree of a round; then one call of `E` (polynomial by its own
Running time paragraph). In all `|D|²` decodes and extractions and `|D|²` calls of `E`.
This running time is argued here, not proved in Lean. -/
def dbExtract [DecidableEq X] (x : X) (D : ODB k kN kS L e) : Multiset Wit :=
  (recordedSalts D).bind fun σ => D.keys.val.filterMap (M.candidate E x D σ)

end Extractor

end Base

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-! ### The opened leaves of a proof whose openings check -/

section Opened

variable [∀ j i, Nonempty ((P j).Challenge i)] {M}

/-- **The leaves of a proof whose openings check are the leaves of the database's views**: at a
database without a digest collision that records every opening query of the trees of the
positions `ps` with the answers of `h`, a proof with one leaf per position whose every tree's
opening checks opens the leaves of the Merkle views of the database at the roots of its writes. -/
theorem openedAs_views_of_check {D : ODB k kN kS L e} (hcol : D ∉ digestCollision)
    {h : Query k kN kS L → Out k e} {π : M.NIProof} {ps : List M.Pos}
    (hlen : ps.length = π.leaves.length) (hpaths : ∀ τ ∈ M.trees ps, checkTree h π ps τ)
    (hrec : ∀ τ ∈ M.trees ps, ∀ q ∈ (M.treeProg π ps τ).trace h, D.lookup q = some (h q)) :
    M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i)) ps π.leaves := by
  refine List.forall₂_iff_zip.2 ⟨hlen, fun {q a} hqa => ?_⟩
  have hτ := M.mem_trees (List.of_mem_zip hqa).1
  have hmem : (q.pos.leaf.1, a) ∈ ((M.openedIn q.treeOf ps π.leaves).map Prod.fst).zip
      ((M.openedIn q.treeOf ps π.leaves).map Prod.snd) := by
    rw [← List.zip_of_prod rfl rfl]
    exact M.mem_openedIn hqa
  exact M.opening.leafAt_of_check hcol (fun q' hq' => hrec _ hτ q' hq') (hpaths _ hτ) hmem
    q.pos.leaf.2

end Opened

/-! ### The database extractor -/

section Extractor

variable {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)

/-- The databases from which the extractor succeeds at `x`. -/
def extracts [DecidableEq X] (x : X) : Set (ODB k kN kS L e) :=
  {D | ∃ w ∈ M.dbExtract E x D, (x, w) ∈ rel}

/-- **A recorded chain input from which a witness is extracted puts `D` in `extracts`.** -/
theorem mem_extracts_of [DecidableEq X] {x : X} {D : ODB k kN kS L e} {σ : FiatShamirSalt kS}
    {c : ChIdx P t} {chs : (r : t.Leaf) → M.Items r} {l : M.Items c.leaf} {past : CausalPast P c}
    (hσ : ∃ κ, Query.xof κ σ ∈ D) (hfull : M.ChainsFull chs c.leaf) (hl : l.length = c.idx.1)
    (hmem : Query.transcript (M.inputAt x σ chs c.leaf l) ∈ D)
    (hp : M.extPast D x σ chs c l = some past) (hrel : (x, E c x past) ∈ rel) :
    D ∈ M.extracts rel E x := by
  have hwf := M.wf_content_of_extPast hfull hl hp
  refine ⟨E c x past, Multiset.mem_bind.2 ⟨σ, mem_recordedSalts.2 hσ,
    (Multiset.mem_filterMap _ _).2 ⟨_, Finmap.mem_keys.2 hmem, ?_⟩⟩, hrel⟩
  have hagree : ∀ r, r.Before c.leaf → M.chainsOf (M.ctxOfChains c.leaf chs) r = chs r :=
    fun r hr => chainsOf_of_before M _ hr
  simp only [candidate, inputAt, M.enc.decode_encode _ _ hwf, Option.bind_some, ite_true]
  simp only [content]
  rw [hl, chAt_idx, Option.bind_some, M.extPast_congr D x σ hagree, hp, Option.map_some]

end Extractor

end Base

end GordieHowe.SPBCS
