-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Base.Extractor
public import GordieHowe.SPBCS.Merkle.Visited
public import GordieHowe.Model.QROM.Partition

@[expose] public section

/-!
# The targeted extractor and Proposition 8.12 at recorded chains

`Base.targetedExtract D π ch E x` (for a composite) extracts along the proof `π` only: the
composite transcript (`trT`) has at each prover round the message of `π`'s write with the Merkle
views of `D` at its roots, and at each challenge round the challenge `ch` the verifier derived; the
causal extractor `E` is applied to every challenge's causal past in it.

- `RecordsChains D x π chs ch`: the database records the chains `chs` of the proof `π` at the
  challenges `ch` (full chains holding `π`'s writes, and at every challenge the chain input and
  the stream, whose digest is the absorbed item and from which the sampler reads the challenge).
  The transcript read from such chains is `trT` (`RecordsChains.extLeaf_eq`,
  `RecordsChains.extPast_eq`).
- `mem_of_recordsChains`, `mem_of_recordsChains_targeted` (CMS19 Proposition 8.12, p. 42,
  knowledge form, p. 44): when the proof's leaves are those of the database's views and the query
  phase accepts, the database extractor (or the targeted extractor at `ch`) returns a witness, or
  the database lies in `badAny`. The flip comes from `CausalRBR.exists_flip` on `trT`. The spBCS
  compiler applies them to its translated database (`GordieHowe.SPBCS.mem_of_verify`,
  `GordieHowe.SPBCS.mem_of_verify_targeted`).
- `targetedExtract_extend_of_notMem`: the extraction depends on `D` only through the views at
  `π`'s roots, so recording a new answer whose digest is not among their visited digests
  (`visitedAll`, at most `visitBound` digests) leaves it unchanged;
  `prob_targetedExtract_change_le`: one more recorded query changes the outcome with probability
  at most `visitBound / 2^(8k)` (for the spBCS compiler, `GordieHowe.SPBCS.instabPart_targetedExtractorOf_le`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

section Targeted

variable (D : ODB k kN kS L e) (π : M.NIProof) (ch : Chs P t)

/-- **The composite transcript along the proof `π`**: at a prover round of a leaf, the message of
`π`'s write with the Merkle views of `D` at its roots; at a challenge round, the challenge `ch`. -/
def trT : FullTr P t := fun q r =>
  if hd : (P q.label).dir r = .P_to_V then
    (M.comp q.label).msg ⟨r, hd⟩ (π.writes q ⟨r, hd⟩)
      ((M.comp q.label).views D ⟨r, hd⟩ (π.writes q ⟨r, hd⟩))
  else ch ⟨q, (P q.label).chIdx r hd⟩

theorem trT_message (q : t.Leaf) (i : (P q.label).MessageIdx) :
    M.trT D π ch q i.1 = (M.comp q.label).msg i (π.writes q i)
      ((M.comp q.label).views D i (π.writes q i)) := by
  simp only [trT, i.2, ↓reduceDIte]
  rfl

theorem trT_challenge (c : ChIdx P t) : M.trT D π ch c.leaf c.idx.1 = ch c := by
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
  simp only [trT, hd, ↓reduceDIte]
  rfl

theorem challenges_trT : (M.trT D π ch).challenges = ch := by
  funext c
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
  simp only [FullTr.challenges, trT, hd, ↓reduceDIte]
  rfl

variable {Wit : Type} (E : CausalExtractor P t X Wit) (x : X)

/-- **The targeted extractor**: the causal extractor `E` at the causal past of every challenge in
the composite transcript along `π` (`trT`), with the challenges `ch` and the prover messages read
from the Merkle views of `D` at the roots of `π`'s writes.

Running time, in the database size `|D|` and the leaf counts: each prover round reads, for each
of its trees, the view below the root (at most `2 · nLeaves` digests, each one scan of `D`), plus
`msg`; then one call of `E` per challenge of the composite (`t.size n` calls at most). It is
polynomial when `E` and `msg` are. This running time is argued here, not proved in Lean. -/
def targetedExtract : Multiset Wit :=
  (Finset.univ : Finset (ChIdx P t)).val.map fun c => E c x ((M.trT D π ch).past c)

theorem mem_targetedExtract {w : Wit} :
    w ∈ M.targetedExtract D π ch E x ↔ ∃ c, E c x ((M.trT D π ch).past c) = w := by
  simp [targetedExtract]

/-- **The number of visited digests**: at most `2 · nLeaves + 1` per tree, over all trees of all
prover rounds of all leaves. -/
def visitBound : ℕ :=
  ∑ q : t.Leaf, ∑ i : (P q.label).MessageIdx, ∑ τ : Fin ((M.comp q.label).nTrees i),
    (2 * (M.comp q.label).nLeaves i τ + 1)

variable {D π}

theorem trT_congr {D' : ODB k kN kS L e}
    (hD : ∀ q i, (M.comp q.label).views D' i (π.writes q i) = (M.comp q.label).views D i (π.writes q i)) :
    M.trT D' π ch = M.trT D π ch := by
  funext q r
  unfold trT
  exact dite_congr rfl (fun hd => by rw [hD q ⟨r, hd⟩]) fun _ => rfl

end Targeted

end Base

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

section Targeted

variable (D : ODB k kN kS L e) (π : M.NIProof) (ch : Chs P t)

variable {Wit : Type} (E : CausalExtractor P t X Wit) (x : X)

/-! ### The outcome depends on the database only through the views at `π`'s roots -/

/-- **The digests visited by the targeted extraction**: the visited digests of the views below
every root of `π`'s writes. -/
def visitedAll : Finset (Digest k) :=
  Finset.univ.biUnion fun q : t.Leaf => Finset.univ.biUnion fun i : (P q.label).MessageIdx =>
    Finset.univ.biUnion fun τ : Fin ((M.comp q.label).nTrees i) =>
      visited D ((M.comp q.label).nLeaves i τ) ((M.comp q.label).rootOf i (π.writes q i) τ)

theorem card_visitedAll_le : (M.visitedAll D π).card ≤ M.visitBound :=
  Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ =>
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ =>
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => card_visited_le _ _ _)))

variable {D π}

/-- **Recording a new answer whose digest is not visited leaves the extraction unchanged**
(`view_extend_of_notMem_visited`). -/
theorem targetedExtract_extend_of_notMem {q : Query k kN kS L} (hq : q ∉ D) {y : Out k e}
    (hy : y.digest ∉ M.visitedAll D π) :
    M.targetedExtract (D.extend q y) π ch E x = M.targetedExtract D π ch E x := by
  unfold targetedExtract
  rw [M.trT_congr ch fun r i => funext fun τ => view_extend_of_notMem_visited hq fun hmem => hy
    (Finset.mem_biUnion.2 ⟨r, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hmem⟩⟩⟩)]

variable (D π)

/-- **One more recorded query changes the targeted extraction with probability at most
`visitBound / 2^(8k)`**, for every database. -/
theorem prob_targetedExtract_change_le {q : Query k kN kS L} (hq : q ∉ D) :
    Pr[y ← Out k e : M.targetedExtract (D.extend q y) π ch E x ≠ M.targetedExtract D π ch E x] ≤
      M.visitBound / 2 ^ (8 * k) := by
  calc Pr[y ← Out k e : M.targetedExtract (D.extend q y) π ch E x ≠ M.targetedExtract D π ch E x]
      ≤ Pr[y ← Out k e : y.digest ∈ M.visitedAll D π] := QROM.probUniform_mono fun y hy => by
        by_contra hy'
        exact hy (M.targetedExtract_extend_of_notMem ch E x hq hy')
    _ = (M.visitedAll D π).card / 2 ^ (8 * k) := Out.probUniform_digest_mem _
    _ ≤ M.visitBound / 2 ^ (8 * k) := by
        gcongr
        exact_mod_cast M.card_visitedAll_le D π

end Targeted

/-! ### Proposition 8.12 at recorded chains -/

section Prop812

variable {V : X → FullTr P t → Bool} {Wit : Type}
  (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) (S : CausalStateFn P t X)
  {ε : ChIdx P t → ℝ≥0}

/-- **The database `D` records the chains `chs` of the proof `π` of `x` at the challenges `ch`**:
every chain is full and holds `π`'s write at each prover round; at each challenge `c`, `D` records
the chain input of `c` (the chains `chs` and the items of `c`'s leaf before its round) with an
answer `a`, and the stream at `a`'s digest and the salt with an answer `s`, whose digest is the
item of `c`'s round and from whose stream the sampler reads `ch c`. -/
structure RecordsChains (D : ODB k kN kS L e) (x : X) (π : M.NIProof)
    (chs : (q : t.Leaf) → M.Items q) (ch : Chs P t) : Prop where
  /-- Every chain is full. -/
  length_eq : ∀ q, (chs q).length = n q.label
  /-- The item of a prover round is `π`'s write. -/
  write_eq : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
    (chs p)[i.1.1]? = some (.write ⟨i, π.writes p i⟩)
  /-- The chain input and the stream of every challenge are recorded and read `ch`. -/
  challenge : ∀ c : ChIdx P t, ∃ a s : Out k e,
    D.lookup (.transcript (M.inputAt x π.salt chs c.leaf ((chs c.leaf).take c.idx.1))) = some a ∧
      D.lookup (.xof a.digest π.salt) = some s ∧
      (chs c.leaf)[c.idx.1.1]? = some (.absorb s.digest) ∧
      ((M.comp c.leaf.label).sampler c.idx).sample s.stream = some (ch c)

variable {M} {D : ODB k kN kS L e} {x : X} {π : M.NIProof} {chs : (q : t.Leaf) → M.Items q}
  {ch : Chs P t}

namespace RecordsChains

variable (hR : M.RecordsChains D x π chs ch)
include hR

/-- **A prover round read from the recorded chains is the message of `π`'s write.** -/
theorem step_message_eq (q : t.Leaf) (i : (P q.label).MessageIdx) :
    M.step D x π.salt chs q (chs q) i.1 i.1.2 =
      some ((M.comp q.label).msg i (π.writes q i) ((M.comp q.label).views D i (π.writes q i))) := by
  rw [M.step_message, hR.write_eq q i, Option.bind_some, (M.comp q.label).writeAt_write]
  rfl

/-- **A challenge round read from the recorded chains is the challenge `ch`.** -/
theorem step_challenge_eq (c : ChIdx P t) :
    M.step D x π.salt chs c.leaf (chs c.leaf) c.idx.1 c.idx.1.2 = some (ch c) := by
  obtain ⟨a, s, ha, hs, hit, hsm⟩ := hR.challenge c
  rw [M.step_challenge, hit]
  simp only [Option.bind_some, Item.getAbsorb, chal, ha, hs, ↓reduceIte]
  exact hsm

/-- **Every round read from the recorded chains is the round of the transcript along `π`.** -/
theorem step_eq (q : t.Leaf) (r : ℕ) (hr : r < n q.label) :
    M.step D x π.salt chs q (chs q) r hr = some (M.trT D π ch q ⟨r, hr⟩) := by
  by_cases hd : (P q.label).dir ⟨r, hr⟩ = .P_to_V
  · exact (hR.step_message_eq q ⟨⟨r, hr⟩, hd⟩).trans
      (congrArg some (M.trT_message D π ch q ⟨⟨r, hr⟩, hd⟩).symm)
  · exact (hR.step_challenge_eq ⟨q, (P q.label).chIdx ⟨r, hr⟩ hd⟩).trans
      (congrArg some (M.trT_challenge D π ch ⟨q, (P q.label).chIdx ⟨r, hr⟩ hd⟩).symm)

/-- **The full transcript of every leaf read from the recorded chains is the transcript along
`π`.** -/
theorem extLeaf_eq (q : t.Leaf) :
    M.extLeaf D x π.salt chs q (chs q) (n q.label) le_rfl = some (M.trT D π ch q) := by
  obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.1 (M.extLeaf_isSome D x π.salt chs q (chs q)
    (fun r hr => Option.isSome_iff_exists.2 ⟨_, hR.step_eq q r hr⟩) _ le_rfl)
  rw [htr]
  congr 1
  funext r
  have h1 := M.step_of_extLeaf D x π.salt chs q (chs q) _ le_rfl htr r.1 r.2
  rw [hR.step_eq q r.1 r.2] at h1
  exact (Option.some_inj.1 h1).symm

/-- **The causal past of every challenge read from the recorded chains is its past in the
transcript along `π`.** -/
theorem extPast_eq (c : ChIdx P t) :
    M.extPast D x π.salt chs c ((chs c.leaf).take c.idx.1) = some ((M.trT D π ch).past c) := by
  have hctx : M.extCtx D x π.salt chs c.leaf = some ((M.trT D π ch).ctx c.leaf) :=
    optAll_eq_some.2 fun q => hR.extLeaf_eq q.1
  rw [extPast, hctx, Option.bind_some, M.extLeaf_take D x π.salt chs c.leaf (chs c.leaf) _ _ le_rfl,
    M.extLeaf_of_le D x π.salt chs c.leaf (chs c.leaf) le_rfl (hR.extLeaf_eq c.leaf) _ c.idx.1.2.le,
    Option.map_some]
  rfl

theorem length_take (c : ChIdx P t) : ((chs c.leaf).take c.idx.1).length = c.idx.1.1 := by
  rw [List.length_take, hR.length_eq]
  exact Nat.min_eq_left c.idx.1.2.le

/-- **The composite verifier accepts the transcript along `π`** when the leaves of `π` are those of
the database's views at the positions the query phase reads, and the query phase accepts. -/
theorem accepts (Q : M.IOPQueries V x)
    (hopen : M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i)) (Q.pos chs ch)
      π.leaves) (hdec : Q.verdict chs ch π.leaves = true) : V x (M.trT D π ch) = true := by
  refine Q.accept_of_verdict chs ch (fun p i => (M.comp p.label).views D i (π.writes p i))
    (M.trT D π ch) _ ?_ (M.challenges_trT D π ch) hopen hdec
  intro p i w hw
  have hw' : w = π.writes p i := by
    have h2 := hR.write_eq p i
    rw [hw] at h2
    exact eq_of_heq (Sigma.mk.inj (Item.write.inj (Option.some_inj.1 h2))).2
  subst hw'
  exact M.trT_message D π ch p i

/-- **A flip at a challenge of the transcript along `π` puts `D` in `badAny`.** -/
theorem mem_badAny (c : ChIdx P t) (hflip : PastFlip rel E S x c ((M.trT D π ch).past c)
    ((M.trT D π ch).challenges c)) : D ∈ M.badAny rel E S := by
  obtain ⟨a, s, ha, hs, -, hsm⟩ := hR.challenge c
  refine ⟨x, π.salt, c, chs, (chs c.leaf).take c.idx.1, (M.trT D π ch).past c, a, s,
    (M.trT D π ch).challenges c, fun q _ => hR.length_eq q, hR.length_take c, hR.extPast_eq c, ha,
    hs, ?_, hflip⟩
  rw [M.challenges_trT D π ch]
  exact hsm

end RecordsChains

/-- **CMS19 Proposition 8.12** (p. 42), knowledge form (p. 44), at chains a database records: when
`D` records the chains `chs` of the proof `π` of `x` at the challenges `ch`, the leaves of `π` are
those of `D`'s views at the queried positions and the query phase accepts, the database extractor
returns a witness for `x` or `D` lies in `badAny`. The flip comes from `CausalRBR.exists_flip` on
the transcript along `π`, which is the transcript read from `D`. -/
theorem mem_of_recordsChains [∀ j i, Nonempty ((P j).Challenge i)] [DecidableEq X]
    (hrbr : CausalRBRKnowledgeSound rel V E S ε)
    (Q : M.IOPQueries V x) (hR : M.RecordsChains D x π chs ch)
    (hopen : M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i)) (Q.pos chs ch)
      π.leaves) (hdec : Q.verdict chs ch π.leaves = true) :
    D ∈ M.extracts rel E x ∪ M.badAny rel E S := by
  by_cases hE : ∃ c, (x, E c x ((M.trT D π ch).past c)) ∈ rel
  · obtain ⟨c, hc⟩ := hE
    obtain ⟨a, s, ha, hs, -, -⟩ := hR.challenge c
    exact Or.inl (M.mem_extracts_of rel E ⟨_, DB.mem_iff_lookup.2 ⟨_, hs⟩⟩
      (fun q _ => hR.length_eq q) (hR.length_take c) (DB.mem_iff_lookup.2 ⟨_, ha⟩)
      (hR.extPast_eq c) hc)
  · push Not at hE
    obtain ⟨c, hflip⟩ := hrbr.exists_flip x _ (hR.accepts Q hopen hdec) id hE
    exact Or.inr (hR.mem_badAny rel E S c ⟨hE c, hflip⟩)

/-- **CMS19 Proposition 8.12 at chains a database records, with the targeted extractor**: under
the hypotheses of `mem_of_recordsChains`, the targeted extractor at the challenges `ch` returns a
witness for `x` or `D` lies in `badAny`. -/
theorem mem_of_recordsChains_targeted [∀ j i, Nonempty ((P j).Challenge i)]
    (hrbr : CausalRBRKnowledgeSound rel V E S ε)
    (Q : M.IOPQueries V x) (hR : M.RecordsChains D x π chs ch)
    (hopen : M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i)) (Q.pos chs ch)
      π.leaves) (hdec : Q.verdict chs ch π.leaves = true) :
    (∃ w ∈ M.targetedExtract D π ch E x, (x, w) ∈ rel) ∨ D ∈ M.badAny rel E S := by
  by_cases hE : ∃ c, (x, E c x ((M.trT D π ch).past c)) ∈ rel
  · obtain ⟨c, hc⟩ := hE
    exact Or.inl ⟨_, (M.mem_targetedExtract D π ch E x).2 ⟨c, rfl⟩, hc⟩
  · push Not at hE
    obtain ⟨c, hflip⟩ := hrbr.exists_flip x _ (hR.accepts Q hopen hdec) id hE
    exact Or.inr (hR.mem_badAny rel E S c ⟨hE c, hflip⟩)

end Prop812

end Base

end GordieHowe.SPBCS
