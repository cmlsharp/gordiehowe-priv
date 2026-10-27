-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Verifier
public import GordieHowe.SPBCS.Base.Targeted

@[expose] public section

/-!
# An accepted spBCS proof and the translated database

A database `D` without a digest collision that records the spBCS verifier's queries on an
accepted proof with the answers of `h` translates (`GordieHowe.SPBCS.trans`,
`GordieHowe/SPBCS/Translate.lean`) into a database that records the verifier's chains with merges
and challenges in the sense of `Base.RecordsChains` (`recordsChains_trans`): each chain input of a
challenge, re-encoded as its causal past, carries the answer `D` holds for the chain input with
merges, and the stream queries are unchanged. The translated database answers the Merkle queries as
`D` (`trans_lookup_merkle`), so the proof's leaves are those of its views
(`openedAs_views_trans`). CMS19 Proposition 8.12 at recorded chains (`Base.mem_of_recordsChains`)
then applies to the translated database (`mem_of_verify`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e)

/-! ### Reading the translated database -/

section Lookup

variable {M} {D : ODB k kN kS L e}

theorem trans_lookup_of (hD : D ∉ digestCollision) {q q' : Query k kN kS L} {y : Out k e}
    (hq : D.lookup q = some y) (hφ : M.φ D q = some q') : (M.trans D).lookup q' = some y :=
  DB.lookup_image_of_lookup (injOnKeys_φ hD) hq hφ

/-- **The translated database has no digest collision** when `D` has none: its answers are
answers of `D` at distinct queries. -/
theorem trans_notMem_digestCollision (hD : D ∉ digestCollision) : M.trans D ∉ digestCollision := by
  rintro ⟨q₁, h₁, q₂, h₂, hne, heq⟩
  obtain ⟨y₁, hy₁⟩ := Finmap.mem_iff.1 h₁
  obtain ⟨y₂, hy₂⟩ := Finmap.mem_iff.1 h₂
  obtain ⟨p₁, hp₁, hφ₁⟩ := (DB.lookup_image_eq_some_iff (injOnKeys_φ hD)).1 hy₁
  obtain ⟨p₂, hp₂, hφ₂⟩ := (DB.lookup_image_eq_some_iff (injOnKeys_φ hD)).1 hy₂
  rw [hy₁, hy₂] at heq
  refine hD ⟨p₁, Finmap.mem_of_lookup_eq_some hp₁, p₂, Finmap.mem_of_lookup_eq_some hp₂,
    fun he => hne ?_, by rw [hp₁, hp₂]; exact heq⟩
  rw [he] at hφ₁
  exact Option.some_inj.1 (hφ₁.symm.trans hφ₂)

/-- Only a Merkle query translates to itself. -/
theorem φ_eq_merkle_iff {q q' : Query k kN kS L} (hq' : (∃ a b, q' = .leaf a b) ∨ ∃ l r, q' = .node l r) :
    M.φ D q = some q' ↔ q = q' := by
  constructor
  · intro h
    cases q with
    | leaf a b => exact Option.some_inj.1 h
    | node l r => exact Option.some_inj.1 h
    | transcript c =>
      obtain ⟨_, _, _, _, _, rfl⟩ := φ_transcript_eq_some h
      rcases hq' with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
    | xof u s =>
      rw [φ_of_not_transcript (fun b h' => by cases h')] at h
      rcases hq' with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] at h <;> cases h
  · rintro rfl
    rcases hq' with ⟨a, b, rfl⟩ | ⟨l, r, rfl⟩ <;> rfl

/-- **The translated database answers a Merkle query as `D`.** -/
theorem trans_lookup_merkle (hD : D ∉ digestCollision) {q : Query k kN kS L}
    (hq : (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r) : (M.trans D).lookup q = D.lookup q := by
  rcases hl : D.lookup q with _ | y
  · rw [trans, DB.lookup_image]
    refine DB.select_eq_none_of_forall fun q₀ y₀ hq₀ => ?_
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false]
    intro h
    rw [φ_eq_merkle_iff hq] at h
    subst h
    rw [hl] at hq₀
    cases hq₀
  · exact trans_lookup_of hD hl ((φ_eq_merkle_iff hq).2 rfl)

end Lookup

/-! ### The translated database records the chains with merges -/

section Chains

variable {M} [∀ j i, Nonempty ((P j).Challenge i)] {h : Query k kN kS L → Out k e} {x : X}
  {π : M.NIProof} {V : X → FullTr P t → Bool} {Q : M.IOPQueries V x} {D : ODB k kN kS L e}

/-- `D` records every query of the spBCS verifier on `π` with the answer of `h`. -/
def RecordsQueries (D : ODB k kN kS L e) (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof)
    (Q : M.IOPQueries V x) : Prop :=
  ∀ q ∈ M.queries x π h Q, Recorded h D q

theorem RecordsQueries.of_rounds (hrec : RecordsQueries D h x π Q) {q : Query k kN kS L}
    (hq : q ∈ (M.roundsProg x π).trace h) : Recorded h D q :=
  hrec q (by rw [queries_eq]; exact List.mem_append_left _ hq)

theorem RecordsQueries.finals (hrec : RecordsQueries D h x π Q) :
    M.RecordsFinals h (M.ssOf x π) π.writes D :=
  fun s => hrec.of_rounds (M.mem_roundsProg_final x π h s)

variable (hD : D ∉ digestCollision) (hrec : RecordsQueries D h x π Q)
include hD hrec

/-- **The translated database records the chains of an accepted proof**: the chains with merges
of `π`, at its challenges with merges. -/
theorem recordsChains_trans (hv : M.Accepts h x π Q) :
    M.toBase.RecordsChains (M.trans D) x π (M.chains h (M.ssOf x π) π.writes)
      (M.chV h (M.ssOf x π) π.writes) where
  length_eq := length_chains π.writes
  write_eq := chains_getElem?_message π.writes
  challenge c := by
    have hr := c.idx.1.2
    obtain ⟨h1, h2⟩ := M.mem_roundsProg_input x π h c.leaf c.idx.1 hr
    have htake : (M.chains h (M.ssOf x π) π.writes c.leaf).take c.idx.1 =
        (M.comp c.leaf.label).chainWith (π.writes c.leaf)
          (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes)
            (M.finals h (M.ssOf x π) π.writes) c.leaf) π.salt h c.idx.1 hr.le := by
      rw [chains_eq_chainWith]
      exact ComponentModel.take_chainWith _ _ _ _ _ _ _ _ hr.le
    obtain ⟨v, hsv⟩ := Option.isSome_iff_exists.1 (hv.sampled c)
    refine ⟨_, _, ?_, trans_lookup_of hD (hrec.of_rounds h2)
      (φ_of_not_transcript fun _ h' => by cases h'), ?_, ?_⟩
    · rw [htake]
      exact trans_lookup_of hD (hrec.of_rounds h1)
        (φ_transcript_honest hD hrec.finals c.leaf
          ((M.comp c.leaf.label).chainWF_chainWith _ _ _ _ _ hr.le)
          (by rw [ComponentModel.length_chainWith]; exact hr))
    · have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
      rw [chains_eq_chainWith, ComponentModel.chainWith_getElem? _ _ _ _ _ _ _ c.idx.1 hr]
      unfold ComponentModel.itemWith
      simp only [hd, ↓reduceDIte]
    · have hc : M.chV h (M.ssOf x π) π.writes c = v := by
        simp only [chV]
        rw [hsv]
        rfl
      rw [hc, ← hsv]
      rfl

/-- **The leaves of an accepted proof are those of the translated database's views.** -/
theorem openedAs_views_trans (hv : M.Accepts h x π Q) :
    M.OpenedAs (fun p i => (M.comp p.label).views (M.trans D) i (π.writes p i))
      (Q.pos (M.chains h (M.ssOf x π) π.writes) (M.chV h (M.ssOf x π) π.writes)) π.leaves :=
  Base.openedAs_views_of_check (trans_notMem_digestCollision hD) hv.leaves_length hv.paths
    fun τ hτ q hq => by
      have hrq : Recorded h D q := hrec q (by
        rw [queries_eq]
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨τ, hτ, hq⟩))
      have hm : (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r := M.opening.merkle_of_mem_trace hq
      exact (trans_lookup_merkle hD hm).trans hrq

end Chains

/-! ### Proposition 8.12 for spBCS -/

section Prop812

variable {M} [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} {Wit : Type}
  (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) (St : CausalStateFn P t X)
  {ε : ChIdx P t → NNReal}

/-- **CMS19 Proposition 8.12** (p. 42), knowledge form (p. 44), for the spBCS compiler at
one accepted proof: a database that records the verifier's queries on an accepted proof `π` of `x`
with the answers of `h` has a digest collision, or the database extractor on its translation
returns a witness for `x`, or its translation lies in `badAny`. -/
theorem mem_of_verify [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {h : Query k kN kS L → Out k e} {x : X} {π : M.NIProof} {Q : M.IOPQueries V x}
    {D : ODB k kN kS L e} (hv : M.Accepts h x π Q) (hrec : RecordsQueries D h x π Q) :
    D ∈ digestCollision ∨ M.trans D ∈ M.toBase.extracts rel E x ∪ M.toBase.badAny rel E St := by
  by_cases hD : D ∈ digestCollision
  · exact Or.inl hD
  · exact Or.inr (M.toBase.mem_of_recordsChains rel E St hrbr Q (recordsChains_trans hD hrec hv)
      (openedAs_views_trans hD hrec hv) hv.decides)

end Prop812

end

end GordieHowe.SPBCS
