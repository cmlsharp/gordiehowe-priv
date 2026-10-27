-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Anonymity
public import GordieHowe.Foundations.ToMathlib.PMFCoupling

@[expose] public section

/-!
# Anonymity of a ring signature whose public value the signer produces

BKM06 Definition 4 (anonymity against full key exposure, ePrint 2005/304, p. 5; keys given at
the start as in CCLM22 Experiment 2, p. 21), `Q` adaptive challenges, for a ring signature whose
public value (ML-DSA's `w₁`) is produced by the signer rather than drawn by the challenger, with
the base scheme's oracle `H` and the compiled argument's oracle both visible. The two oracles are
modelled as independent; this is equivalent to one oracle with domain separation.

- `pubRun`, `tvDist_pubRun_le` (identical until bad), `map_wiRun_replay`,
  `gameAdvantage_pubRun_le`: rounds with public outputs or refusals, and spBCS witness
  indistinguishability for them (`SPBCS.witnessIndistinguishable` through a recomputed history
  that discards the proofs of refused rounds).
- `PubSigner`, `PubAnonAdversary`, `PubAnonAdversary.game`, `PubAnonAdversary.advantage`: as in
  Definition 4 the adversary chooses any ring holding the two users' keys; the signer refuses the
  rings its public rule `PubSigner.Admit` rejects at `H`, and a refused round shows the adversary
  `⊥` (`none` in the history) in both experiments.
- `PubAnonAdversary.advantage_le`: per oracle `H` and keys, couple the two users' signing laws
  (`PMF.exists_coupling_map_le_tvDist`); when the public values agree the witnesses share a
  statement and witness indistinguishability applies, otherwise the round is bad. The bound is
  `Q · 𝔼 ε + Q · wiError δ (Q · C) + Pr[¬ Good]`.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

/-! ### Rounds with public outputs -/

section PubRun

variable {Ω X W Pub Pf : Type} [Fintype Ω] [Nonempty Ω] (law : Ω → X → W → PMF Pf)
  (pubOf : X → Pub) {Q : ℕ}

/-- The history after `j` rounds: the public value and the proof of each round, or `none` (the
refusal `⊥`) for a refused round. -/
abbrev PubHist (Pub Pf : Type) (j : ℕ) : Type := Fin j → Option (Pub × Pf)

/-- **A selector**: in round `j`, from the oracle and the history, the statement and the witness
proved, or `none` when the round is refused. -/
abbrev Selector (Ω X W Pub Pf : Type) (Q : ℕ) : Type :=
  (j : Fin Q) → Ω → PubHist Pub Pf j → Option (X × W)

/-- **The output of a round** at the oracle `h`: for a selected statement and witness, the
statement's public value and a proof from `law`; for a refused round, `none`. -/
noncomputable def roundLaw (h : Ω) : Option (X × W) → PMF (Option (Pub × Pf))
  | none => PMF.pure none
  | some xw => (law h xw.1 xw.2).map fun π => some (pubOf xw.1, π)

variable (sel : Selector Ω X W Pub Pf Q)

/-- Round `j` with the selector `sel`: the output of the round (`roundLaw`) appended to the
history. -/
noncomputable def pubStep (j : Fin Q) (s : Ω × PubHist Pub Pf j) : PMF (Ω × PubHist Pub Pf (j + 1)) :=
  (roundLaw law pubOf s.1 (sel j s.1 s.2)).map fun r =>
    (s.1, Fin.snoc (α := fun _ => Option (Pub × Pf)) s.2 r)

/-- The experiment after `j` rounds: the oracle uniform, then the rounds. -/
noncomputable def pubRun : (j : ℕ) → j ≤ Q → PMF (Ω × PubHist Pub Pf j)
  | 0, _ => (PMF.uniformOfFintype Ω).map fun h => (h, Fin.elim0)
  | j + 1, hj => (pubRun j (by omega)).bind (pubStep law pubOf sel ⟨j, by omega⟩)

variable {law pubOf}

/-- Two selectors that agree before round `j` give the same experiment after `j` rounds. -/
theorem pubRun_congr {sel sel' : Selector Ω X W Pub Pf Q} :
    ∀ j (hj : j ≤ Q), (∀ i : Fin Q, i.1 < j → sel i = sel' i) →
      pubRun law pubOf sel j hj = pubRun law pubOf sel' j hj
  | 0, _, _ => rfl
  | j + 1, hj, h => by
    rw [pubRun, pubRun, pubRun_congr j (by omega) fun i hi => h i (by omega)]
    congr 1
    funext s
    rw [pubStep, pubStep, h ⟨j, by omega⟩ (by simp)]

/-- The probability that two selectors select differently in round `i`, in the experiment of the
first. -/
noncomputable def selectDiffProb (sel sel' : Selector Ω X W Pub Pf Q) (i : Fin Q) : ℝ :=
  ((pubRun law pubOf sel i.1 i.2.le).toOuterMeasure {s | sel i s.1 s.2 ≠ sel' i s.1 s.2}).toReal

/-- **Identical until bad**: two selectors give experiments at most the sum, over the rounds, of
the probability that they select differently in that round apart. -/
theorem tvDist_pubRun_le (sel sel' : Selector Ω X W Pub Pf Q) :
    ∀ j (hj : j ≤ Q), PMF.tvDist (pubRun law pubOf sel j hj) (pubRun law pubOf sel' j hj) ≤
      ∑ i : Fin j, selectDiffProb (law := law) (pubOf := pubOf) sel sel' (Fin.castLE hj i)
  | 0, _ => by simp [pubRun]
  | j + 1, hj => by
    rw [Fin.sum_univ_castSucc]
    have hstep : PMF.tvDist ((pubRun law pubOf sel j (by omega)).bind
        (pubStep law pubOf sel ⟨j, by omega⟩)) ((pubRun law pubOf sel j (by omega)).bind
        (pubStep law pubOf sel' ⟨j, by omega⟩)) ≤
        selectDiffProb (law := law) (pubOf := pubOf) sel sel' ⟨j, by omega⟩ := by
      refine (PMF.tvDist_bind_le_toOuterMeasure_ne _ _ _).trans ?_
      refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
        (PMF.toOuterMeasure_apply_le_one _ _)) (PMF.toOuterMeasure_mono _ ?_)
      intro s hs he
      exact hs.1 (by simp only [pubStep]; rw [he])
    have hih := tvDist_pubRun_le sel sel' j (by omega)
    have hlast : Fin.castLE hj (Fin.last j) = ⟨j, by omega⟩ := rfl
    have hcast : ∀ i : Fin j, Fin.castLE hj i.castSucc = Fin.castLE (by omega) i := fun _ => rfl
    rw [hlast]
    simp only [hcast]
    rw [pubRun, pubRun]
    refine (PMF.tvDist_triangle _ ((pubRun law pubOf sel j (by omega)).bind
      (pubStep law pubOf sel' ⟨j, by omega⟩)) _).trans ?_
    exact (add_le_add hstep ((PMF.tvDist_bind_right_le _ _ _).trans hih)).trans_eq (add_comm _ _)

end PubRun

/-! ### Selectors from two-witness choices, and witness indistinguishability -/

section ReplayWI

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {X W Pub : Type} {M : SPBCS Mg P X k kN kS L e}
  (pubOf : X → Pub) {Q : ℕ}

/-- **Two-witness choices from the history**: in round `j`, from the oracle and the history of
public values and proofs, a statement and two witnesses, or `none` for a refused round. -/
abbrev HistChoices (M : SPBCS Mg P X k kN kS L e) (W Pub : Type) (Q : ℕ) : Type :=
  (j : Fin Q) → (Query k kN kS L → Out k e) → PubHist Pub M.NIProof j →
    Option (SPBCS.WIChoice X W)

variable (F : HistChoices M W Pub Q)

/-- **The history recomputed from the proofs**: round `i` is refused when the choice of round `i`
from the earlier recomputed history is `none`, and otherwise holds the public value of the chosen
statement with the proof of round `i`. -/
def replay : (j : ℕ) → j ≤ Q → (Query k kN kS L → Out k e) → (Fin j → M.NIProof) →
    PubHist Pub M.NIProof j
  | 0, _, _, _ => Fin.elim0
  | j + 1, hj, h, πs =>
    Fin.snoc (α := fun _ => Option (Pub × M.NIProof)) (replay j (by omega) h (Fin.init πs))
      ((F ⟨j, by omega⟩ h (replay j (by omega) h (Fin.init πs))).map fun c =>
        (pubOf c.stmt, πs (Fin.last j)))

theorem replay_succ_snoc (j : ℕ) (hj : j + 1 ≤ Q) (h : Query k kN kS L → Out k e)
    (πs : Fin j → M.NIProof) (π : M.NIProof) :
    replay pubOf F (j + 1) hj h (Fin.snoc (α := fun _ => M.NIProof) πs π) =
      Fin.snoc (α := fun _ => Option (Pub × M.NIProof)) (replay pubOf F j (by omega) h πs)
        ((F ⟨j, by omega⟩ h (replay pubOf F j (by omega) h πs)).map fun c => (pubOf c.stmt, π)) := by
  rw [replay, Fin.init_snoc, Fin.snoc_last]

/-- **The witness-indistinguishability adversary of two-witness choices from the history**, with
a finite set `S` of admissible choices containing every choice and a choice `c₀ ∈ S` for the
refused rounds, whose proofs the recomputed history discards. -/
def HistChoices.toWIAdversary {rel : Set (X × W)} (S : Finset (SPBCS.WIChoice X W))
    (hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel) {c₀ : SPBCS.WIChoice X W}
    (hc₀ : c₀ ∈ S) (hF : ∀ j h hist c, F j h hist = some c → c ∈ S) : M.WIAdversary rel Q where
  choices := S
  admissible := hS
  choose j h πs := (F j h (replay pubOf F j j.2.le h πs)).getD c₀
  choose_mem j h πs := by
    cases hc : F j h (replay pubOf F j j.2.le h πs) with
    | none => exact hc₀
    | some c => exact hF _ _ _ _ hc

/-- The selector answering round `j` with the second witness when `bs j`, refusing the rounds whose
choice is `none`. -/
def HistChoices.selector (bs : ℕ → Bool) : Selector (Query k kN kS L → Out k e) X W Pub M.NIProof Q :=
  fun j h hist => (F j h hist).map fun c => (c.stmt, if bs j then c.wit₁ else c.wit₀)

variable {F}

/-- **The witness-indistinguishability experiment with its history recomputed** is the experiment
with public outputs of the selector. -/
theorem map_wiRun_replay (law : (Query k kN kS L → Out k e) → X → W → PMF M.NIProof)
    {rel : Set (X × W)} {S : Finset (SPBCS.WIChoice X W)}
    {hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel} {c₀ : SPBCS.WIChoice X W}
    {hc₀ : c₀ ∈ S} {hF : ∀ j h hist c, F j h hist = some c → c ∈ S} (bs : ℕ → Bool) :
    ∀ j (hj : j ≤ Q), (SPBCS.wiRun law (F.toWIAdversary pubOf S hS hc₀ hF) bs j hj).map
        (fun s => (s.1, replay pubOf F j hj s.1 s.2)) =
      pubRun law pubOf (F.selector bs) j hj
  | 0, _ => by
    rw [SPBCS.wiRun, pubRun, PMF.map_comp]
    congr 1
  | j + 1, hj => by
    rw [SPBCS.wiRun, pubRun, ← map_wiRun_replay law (hS := hS) (hc₀ := hc₀) (hF := hF) bs j
      (by omega), PMF.map_bind, PMF.bind_map]
    congr 1
    funext s
    simp only [Function.comp_apply, SPBCS.wiStep, pubStep, PMF.map_comp, HistChoices.selector,
      HistChoices.toWIAdversary]
    simp only [Function.comp_def, replay_succ_snoc]
    cases hc : F ⟨j, by omega⟩ s.1 (replay pubOf F j (by omega) s.1 s.2) with
    | none =>
      simp only [Option.map_none, Option.getD_none, roundLaw, PMF.pure_map]
      exact PMF.map_const _ _
    | some c =>
      simp only [Option.map_some, roundLaw, PMF.map_comp, Function.comp_def]
      rfl

/-- **Witness indistinguishability with public outputs**: for the spBCS compilation `M` whose
honest prover has honest-verifier zero knowledge at error `δ` for `rel` (`h`), and two-witness
choices from the history in a finite admissible set `S` (every choice not `none` is in `S`), the
experiments with public outputs answering every round with the first and with the second witness
are distinguished by any event of the oracle and the history with advantage at most
`Q · wiError δ |S|`. Refused rounds are the same in the two experiments; if `S` is empty every
round is refused and the experiments agree. -/
theorem gameAdvantage_pubRun_le {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P τ → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {R : Type} [Fintype R] [Nonempty R]
    {honest : W → R → CausalProver P τ X} {rel : Set (X × W)} {PubZ : Type} {pubZ : X → PubZ}
    (Rv : M.Reveal E Qs) {sim : CausalJointSimulator Rv.MV PubZ} {δ : ℝ≥0}
    (h : CausalHVZK Rv.MV rel honest pubZ sim δ) (S : Finset (SPBCS.WIChoice X W))
    (hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel)
    (hF : ∀ j h hist c, F j h hist = some c → c ∈ S)
    (D : (Query k kN kS L → Out k e) → PubHist Pub M.NIProof Q → Prop) :
    GordieHowe.gameAdvantage
      (pubRun (fun h x w => proofLaw E Qs h x (honest w)) pubOf (F.selector fun _ => false) Q le_rfl)
      (pubRun (fun h x w => proofLaw E Qs h x (honest w)) pubOf (F.selector fun _ => true) Q le_rfl)
      {s | D s.1 s.2} ≤ Q * M.wiError δ S.card := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨c₀, hc₀⟩
  · have hnone : ∀ j h hist, F j h hist = none := fun j h hist => by
      cases hc : F j h hist with
      | none => rfl
      | some c => exact absurd (hF j h hist c hc) (by simp [hS0])
    have hsel : F.selector (fun _ => false) = F.selector fun _ => true := by
      funext j h hist
      simp [HistChoices.selector, hnone]
    rw [hsel]
    unfold GordieHowe.gameAdvantage GordieHowe.advantage
    rw [sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (SPBCS.wiError_nonneg δ _)
  rw [← map_wiRun_replay pubOf _ (hS := hS) (hc₀ := hc₀) (hF := hF),
    ← map_wiRun_replay pubOf _ (hS := hS) (hc₀ := hc₀) (hF := hF)]
  have hadv := SPBCS.witnessIndistinguishable Rv (SPBCS.obsClose_of_causalHVZK Rv h) Q S.card
    (F.toWIAdversary pubOf S hS hc₀ hF) le_rfl (fun h πs => D h (replay pubOf F Q le_rfl h πs))
  unfold SPBCS.wiAdvantage SPBCS.wiAdvantageWith SPBCS.wiGameWith at hadv
  unfold GordieHowe.gameAdvantage at hadv ⊢
  simp only [PMF.toOuterMeasure_map_apply] at ⊢
  exact hadv

end ReplayWI

/-! ### Ring signatures whose public value the signer produces -/

/-- **A ring signer producing the public value of its signature**, with rings of at most `N` keys
and ring messages `RMsg`: key generation from uniform coins, a signing law given the oracle `Orc`
of the base scheme (for ML-DSA: the commitment hash `H`, a random oracle), the secret key, the ring,
the signer's position and the ring message, with values a public value (`w₁` for ML-DSA) and a
base signature; the ring relation at an oracle: the base signature with the public value is
valid for the member at the position, on the ring message; and the signer's public refusal rule
`Admit`: at the oracle `H` the signer signs on the rings `R` with `Admit H R` and outputs `⊥` on the
others. The rule reads only the oracle and the ring, not the signer's key or position, so every
signer refuses the same rings; `signLaw` is the signer's law on the rings it admits. -/
structure PubSigner (N : ℕ) (RMsg : Type) where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- The coins of key generation. -/
  KeyCoins : Type
  /-- Public values. -/
  Pub : Type
  /-- Base signatures. -/
  Sig : Type
  /-- The oracle of the base scheme. -/
  Orc : Type
  [instFintypePK : Fintype PK]
  [instDecEqPK : DecidableEq PK]
  [instFintypeKeyCoins : Fintype KeyCoins]
  [instNonemptyKeyCoins : Nonempty KeyCoins]
  [instFintypePub : Fintype Pub]
  [instDecEqPub : DecidableEq Pub]
  [instFintypeSig : Fintype Sig]
  [instDecEqSig : DecidableEq Sig]
  [instFintypeOrc : Fintype Orc]
  [instNonemptyOrc : Nonempty Orc]
  /-- Key generation from its coins. -/
  keyGen : KeyCoins → PK × SK
  /-- The signing law: the public value and the base signature. -/
  signLaw : Orc → SK → RingOf PK N → ℕ → RMsg → PMF (Pub × Sig)
  /-- The ring relation at an oracle: ring, message, public value, position, base signature. -/
  Valid : Orc → RingOf PK N → RMsg → Pub → ℕ → Sig → Prop
  /-- The refusal rule: the rings the signer signs on at an oracle. -/
  Admit : Orc → RingOf PK N → Prop
  [instDecAdmit : ∀ H R, Decidable (Admit H R)]

attribute [instance] PubSigner.instFintypePK PubSigner.instDecEqPK PubSigner.instFintypeKeyCoins
  PubSigner.instNonemptyKeyCoins PubSigner.instFintypePub PubSigner.instDecEqPub
  PubSigner.instFintypeSig PubSigner.instDecEqSig PubSigner.instFintypeOrc
  PubSigner.instNonemptyOrc PubSigner.instDecAdmit

namespace PubSigner

variable {N : ℕ} {RMsg : Type} (S : PubSigner N RMsg)

/-- The public key generated from the coins `kc`. -/
def pk (kc : S.KeyCoins) : S.PK := (S.keyGen kc).1

/-- The secret key generated from the coins `kc`. -/
def sk (kc : S.KeyCoins) : S.SK := (S.keyGen kc).2

/-- **Correctness of the signer**: on every ring it admits, every signature it can output with an
honestly generated key at position `i` of the ring is valid, at every oracle. -/
def Correct : Prop :=
  ∀ (H : S.Orc) (kc : S.KeyCoins) (R : RingOf S.PK N) (i : ℕ) (m : RMsg) (hi : i < R.1.length),
    S.Admit H R → R.1[i] = S.pk kc →
      ∀ x ∈ (S.signLaw H (S.sk kc) R i m).support, S.Valid H R m x.1 i x.2

/-- **A statement**: a ring, a ring message and the public value. -/
structure Stmt where
  /-- The ring. -/
  ring : RingOf S.PK N
  /-- The ring message. -/
  msg : RMsg
  /-- The public value. -/
  pub : S.Pub

/-- **A witness**: the signer's position and the base signature. -/
structure Wit where
  /-- The position. -/
  idx : ℕ
  /-- The base signature. -/
  sig : S.Sig

/-- **The ring relation** at the oracle `H`. -/
def rel (H : S.Orc) : Set (S.Stmt × S.Wit) :=
  {p | S.Valid H p.1.ring p.1.msg p.1.pub p.2.idx p.2.sig}

variable [DecidableEq RMsg]

/-- **A challenge** of the anonymity game with `n` honest users: a ring, a ring message, two honest
users and the positions of their keys. With `user₀ = user₁` and `idx₀ = idx₁` it is a signing
query. -/
structure Choice (n : ℕ) where
  /-- The ring. -/
  ring : RingOf S.PK N
  /-- The ring message. -/
  msg : RMsg
  /-- The user signing when `b = 0`. -/
  user₀ : Fin n
  /-- The user signing when `b = 1`. -/
  user₁ : Fin n
  /-- The position of `user₀`'s key. -/
  idx₀ : ℕ
  /-- The position of `user₁`'s key. -/
  idx₁ : ℕ
deriving DecidableEq

/-- **A valid challenge** for the users' coins `keys` (BKM06 Definition 4, ePrint 2005/304, p. 5:
both users' public keys are in the ring): the positions hold the two users' public keys. -/
structure Choice.Valid {n : ℕ} (keys : Fin n → S.KeyCoins) (c : S.Choice n) : Prop where
  /-- The first position is in the ring. -/
  idx₀_lt : c.idx₀ < c.ring.1.length
  /-- The first position holds `user₀`'s key. -/
  key₀ : c.ring.1[c.idx₀] = S.pk (keys c.user₀)
  /-- The second position is in the ring. -/
  idx₁_lt : c.idx₁ < c.ring.1.length
  /-- The second position holds `user₁`'s key. -/
  key₁ : c.ring.1[c.idx₁] = S.pk (keys c.user₁)

variable {S}

/-- The user of a challenge in the experiment `b`. -/
def Choice.user {n : ℕ} (c : S.Choice n) (b : Bool) : Fin n := if b then c.user₁ else c.user₀

/-- The position of a challenge in the experiment `b`. -/
def Choice.idx {n : ℕ} (c : S.Choice n) (b : Bool) : ℕ := if b then c.idx₁ else c.idx₀

/-- **The signing law of a challenge** in the experiment `b`, at the oracle `H` and the users'
coins `keys`: user `b` signs at its position. -/
noncomputable def Choice.signLaw {n : ℕ} (H : S.Orc) (keys : Fin n → S.KeyCoins) (c : S.Choice n)
    (b : Bool) : PMF (S.Pub × S.Sig) :=
  S.signLaw H (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg

end PubSigner

/-! ### The anonymity game -/

section Game

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {S : PubSigner N RMsg}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] (M : SPBCS Mg P S.Stmt k kN kS L e)

variable (S) in
/-- **An anonymity adversary against full key exposure** with `n` honest users and `Q`
challenges: a finite set of challenges and, in round `j`, a challenge from it chosen as a function
of the honest users' key-generation coins (given at the start), the whole oracle `H` of the base
scheme, the whole oracle of the compiled argument, and the public values and ring signatures of the
earlier rounds, with `⊥` for the refused rounds. As in BKM06 Definition 4 (ePrint 2005/304, p. 5),
a chosen challenge may hold any ring containing the two users' public keys at its positions
(`Choice.Valid`); a ring the signer refuses at `H` (`PubSigner.Admit`) is answered by `⊥`, which
the adversary sees. -/
structure PubAnonAdversary (n Q : ℕ) where
  /-- The finite set of challenges the adversary may choose. -/
  choices : Finset (S.Choice n)
  /-- The challenge of round `j`. -/
  choose : (j : Fin Q) → (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
    PubHist S.Pub M.NIProof j → S.Choice n
  /-- Every chosen challenge is in the set. -/
  choose_mem : ∀ j keys H h hist, choose j keys H h hist ∈ choices
  /-- The positions of every chosen challenge hold the two users' public keys. -/
  choose_valid : ∀ j keys H h hist, (choose j keys H h hist).Valid S keys

namespace PubAnonAdversary

variable {M} {n Q : ℕ} (A : PubAnonAdversary S M n Q)

/-- **A table of signatures**: for each round and each challenge of the set, a public value and a
base signature. -/
abbrev Table : Type := Fin Q → A.choices → S.Pub × S.Sig

/-- **The law of the signature table** in the experiment `b` at the oracle `H` and the users'
coins `keys`: every entry independent, the entry of a challenge signed by its user `b`. Round `j`
uses the entry of its chosen challenge only, so its signature has the signing law of that
challenge. -/
noncomputable def tableLaw (H : S.Orc) (keys : Fin n → S.KeyCoins) (b : Bool) : PMF A.Table :=
  PMF.pi fun _ => PMF.pi fun c : A.choices => c.1.signLaw H keys b

/-- **The selector of the experiment `b`** at the table `T`: round `j` is refused when the signer
refuses the chosen challenge's ring at `H`, and otherwise proves the chosen challenge's statement,
with the table's public value, with the witness of user `b`. -/
def selector (keys : Fin n → S.KeyCoins) (H : S.Orc) (b : Bool) (T : A.Table) :
    Selector (Query k kN kS L → Out k e) S.Stmt S.Wit S.Pub M.NIProof Q :=
  fun j h hist =>
    if S.Admit H (A.choose j keys H h hist).ring then
      some (⟨(A.choose j keys H h hist).ring, (A.choose j keys H h hist).msg,
          (T j ⟨_, A.choose_mem j keys H h hist⟩).1⟩,
        ⟨(A.choose j keys H h hist).idx b, (T j ⟨_, A.choose_mem j keys H h hist⟩).2⟩)
    else none

variable (E : (j : ι) → (M.comp j).Encoder) {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type} [Fintype R] [Nonempty R]
  (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)

/-- The law of a ring signature at the oracle `H` of the base scheme: the compiled honest proof at
the oracle `h` of the compiled argument. -/
noncomputable def proofLawAt (H : S.Orc) (h : Query k kN kS L → Out k e) (x : S.Stmt) (w : S.Wit) :
    PMF M.NIProof :=
  proofLaw E (Qs H) h x (honest H w)

/-- **The experiment `b` of anonymity against full key exposure, with the public value produced by
the signer**: the honest users' coins uniform, the oracle `H` of the base scheme uniform, the
signature table of the experiment `b`; then the oracle of the compiled argument uniform and the `Q`
rounds, round `j` answered by `⊥` when the signer refuses the chosen challenge's ring at `H`, and
otherwise by the public value and the ring signature of user `b` of the chosen challenge. The
outcome is the users' coins, both oracles and the history. -/
noncomputable def game (b : Bool) :
    PMF ((Fin n → S.KeyCoins) × S.Orc × (Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q) :=
  (PMF.uniformOfFintype (Fin n → S.KeyCoins)).bind fun keys =>
    (PMF.uniformOfFintype S.Orc).bind fun H =>
      (A.tableLaw H keys b).bind fun T =>
        (pubRun (proofLawAt E Qs honest H) PubSigner.Stmt.pub (A.selector keys H b T) Q le_rfl).map
          fun s => (keys, H, s.1, s.2)

/-- **The anonymity advantage** of the distinguisher `D`, given the users' coins, both oracles and
the history. -/
noncomputable def advantage
    (D : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) : ℝ :=
  GordieHowe.gameAdvantage (A.game E Qs honest false) (A.game E Qs honest true)
    {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}

/-! ### The coupled table -/

section Coupled

variable (H : S.Orc) (keys : Fin n → S.KeyCoins)

/-- **The coupling of the two signers of a challenge**: a joint law of the entries of user `0` and
user `1`, with those marginals, whose public values differ with probability at most the distance
of the two public-value laws (`PMF.exists_coupling_map_le_tvDist`). -/
noncomputable def coupling (c : A.choices) : PMF ((S.Pub × S.Sig) × (S.Pub × S.Sig)) :=
  Classical.choose (PMF.exists_coupling_map_le_tvDist (c.1.signLaw H keys false)
    (c.1.signLaw H keys true) Prod.fst)

theorem map_fst_coupling (c : A.choices) :
    (A.coupling H keys c).map Prod.fst = c.1.signLaw H keys false :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (c.1.signLaw H keys false)
    (c.1.signLaw H keys true) Prod.fst)).1

theorem map_snd_coupling (c : A.choices) :
    (A.coupling H keys c).map Prod.snd = c.1.signLaw H keys true :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (c.1.signLaw H keys false)
    (c.1.signLaw H keys true) Prod.fst)).2.1

theorem toReal_coupling_ne_le (c : A.choices) :
    ((A.coupling H keys c).toOuterMeasure {x | x.1.1 ≠ x.2.1}).toReal ≤
      PMF.tvDist ((c.1.signLaw H keys false).map Prod.fst) ((c.1.signLaw H keys true).map Prod.fst) :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (c.1.signLaw H keys false)
    (c.1.signLaw H keys true) Prod.fst)).2.2

/-- A table of coupled entries. -/
abbrev CTable : Type := Fin Q → A.choices → (S.Pub × S.Sig) × (S.Pub × S.Sig)

/-- The law of the coupled table: every entry independent, from the coupling of its challenge. -/
noncomputable def coupledLaw : PMF A.CTable :=
  PMF.pi fun _ => PMF.pi fun c => A.coupling H keys c

/-- The entries of user `b` of a coupled table. -/
def side (b : Bool) (T : A.CTable) : A.Table := fun j c => if b then (T j c).2 else (T j c).1

/-- **The signature table is a side of the coupled table.** -/
theorem tableLaw_eq_map_side (b : Bool) :
    A.tableLaw H keys b = (A.coupledLaw H keys).map (A.side b) := by
  have h1 : (A.coupledLaw H keys).map (A.side b) =
      PMF.pi fun _ => ((PMF.pi fun c => A.coupling H keys c).map fun row c =>
        if b then (row c).2 else (row c).1) :=
    PMF.pi_map (fun _ => PMF.pi fun c => A.coupling H keys c)
      (fun _ row c => if b then (row c).2 else (row c).1)
  rw [h1, tableLaw]
  congr 1
  funext j
  rw [PMF.pi_map (fun c => A.coupling H keys c) (fun _ x => if b then x.2 else x.1)]
  congr 1
  funext c
  cases b
  · exact (A.map_fst_coupling H keys c).symm
  · exact (A.map_snd_coupling H keys c).symm

end Coupled

/-! ### The hybrid -/

section Hybrid

variable (H : S.Orc) (keys : Fin n → S.KeyCoins)

variable (S) in
/-- **The hybrid choice of a challenge at a coupled entry**: the statement with user `0`'s public
value, user `0`'s witness, and user `1`'s witness when both public values agree (user `0`'s
otherwise). -/
def hybChoice (c : S.Choice n) (x : (S.Pub × S.Sig) × (S.Pub × S.Sig)) :
    SPBCS.WIChoice S.Stmt S.Wit :=
  ⟨⟨c.ring, c.msg, x.1.1⟩, ⟨c.idx₀, x.1.2⟩,
    if x.1.1 = x.2.1 then ⟨c.idx₁, x.2.2⟩ else ⟨c.idx₀, x.1.2⟩⟩

/-- **The hybrid two-witness choices** at the coupled table `T`, refusing the rounds whose ring the
signer refuses at `H`. -/
def hybrid (T : A.CTable) : HistChoices M S.Wit S.Pub Q :=
  fun j h hist =>
    if S.Admit H (A.choose j keys H h hist).ring then
      some (hybChoice S (A.choose j keys H h hist) (T j ⟨_, A.choose_mem j keys H h hist⟩))
    else none

open Classical in
/-- **The hybrid choice set** at the coupled table `T`: the hybrid choices of the valid challenges
of the set whose ring the signer admits at `H`, at every round. -/
noncomputable def hybridSet (T : A.CTable) : Finset (SPBCS.WIChoice S.Stmt S.Wit) :=
  ((Finset.univ : Finset (Fin Q)) ×ˢ
      (A.choices.attach.filter fun c => c.1.Valid S keys ∧ S.Admit H c.1.ring)).image
    fun p => hybChoice S p.2.1 (T p.1 p.2)

theorem card_hybridSet_le (T : A.CTable) : (A.hybridSet H keys T).card ≤ Q * A.choices.card := by
  classical
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_left _ ((Finset.card_filter_le _ _).trans_eq (Finset.card_attach))

theorem hybrid_mem (T : A.CTable) (j : Fin Q) (h : Query k kN kS L → Out k e)
    (hist : PubHist S.Pub M.NIProof j) (x : SPBCS.WIChoice S.Stmt S.Wit)
    (hx : A.hybrid H keys T j h hist = some x) : x ∈ A.hybridSet H keys T := by
  classical
  unfold hybrid at hx
  split_ifs at hx with hA
  cases hx
  unfold hybridSet
  refine Finset.mem_image.2 ⟨(j, ⟨_, A.choose_mem j keys H h hist⟩), ?_, rfl⟩
  refine Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_attach _ _, ?_⟩⟩
  exact ⟨A.choose_valid j keys H h hist, hA⟩

/-- An entry of a table in the support of the coupled law is in the support of its coupling. -/
theorem coupling_ne_zero_of_mem_support {T : A.CTable} (hT : T ∈ (A.coupledLaw H keys).support)
    (j : Fin Q) (c : A.choices) : A.coupling H keys c (T j c) ≠ 0 := by
  rw [PMF.mem_support_iff, coupledLaw, PMF.pi_apply, Finset.prod_ne_zero_iff] at hT
  have := hT j (Finset.mem_univ _)
  rw [PMF.pi_apply, Finset.prod_ne_zero_iff] at this
  exact this c (Finset.mem_univ _)

/-- **The signers of the valid admitted challenges sign validly** at the oracle `H` and the users'
coins `keys`: every output of either user's signing law of every valid challenge of the set whose
ring the signer admits at `H` is valid for the challenge's ring and message at that user's
position. -/
def SignsValidly : Prop :=
  ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring → ∀ (b : Bool) (x : S.Pub × S.Sig),
    x ∈ (c.signLaw H keys b).support → S.Valid H c.ring c.msg x.1 (c.idx b) x.2

/-- A correct signer signs validly at every oracle. -/
theorem signsValidly_of_correct (hS : S.Correct) : A.SignsValidly H keys := by
  intro c _ hc hA b x hx
  cases b
  · exact hS H (keys c.user₀) c.ring c.idx₀ c.msg hc.idx₀_lt hA hc.key₀ x hx
  · exact hS H (keys c.user₁) c.ring c.idx₁ c.msg hc.idx₁_lt hA hc.key₁ x hx

/-- **The hybrid choices are admissible** at a table of the support, when the signers sign
validly. -/
theorem hybridSet_admissible (hS : A.SignsValidly H keys) {T : A.CTable}
    (hT : T ∈ (A.coupledLaw H keys).support) :
    ∀ c ∈ A.hybridSet H keys T, (c.stmt, c.wit₀) ∈ S.rel H ∧ (c.stmt, c.wit₁) ∈ S.rel H := by
  classical
  intro x hx
  obtain ⟨⟨j, c⟩, hp, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨hc, hA⟩ := (Finset.mem_filter.1 (Finset.mem_product.1 hp).2).2
  have hJ := A.coupling_ne_zero_of_mem_support H keys hT j c
  have h0 : c.1.signLaw H keys false (T j c).1 ≠ 0 := by
    rw [← A.map_fst_coupling H keys c]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hJ) (PMF.apply_le_map_apply _ _ _))
  have h1 : c.1.signLaw H keys true (T j c).2 ≠ 0 := by
    rw [← A.map_snd_coupling H keys c]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hJ) (PMF.apply_le_map_apply _ _ _))
  have hv0 := hS c.1 c.2 hc hA false _ ((PMF.mem_support_iff _ _).2 h0)
  have hv1 := hS c.1 c.2 hc hA true _ ((PMF.mem_support_iff _ _).2 h1)
  refine ⟨hv0, ?_⟩
  simp only [hybChoice]
  split_ifs with hv
  · change S.Valid H c.1.ring c.1.msg (T j c).1.1 c.1.idx₁ (T j c).2.2
    rw [hv]; exact hv1
  · exact hv0

/-- **In the experiment `0` the game is the hybrid answering with the first witnesses.** -/
theorem selector_false_eq (T : A.CTable) :
    A.selector keys H false (A.side false T) = (A.hybrid H keys T).selector fun _ => false := by
  funext j h hist
  by_cases hA : S.Admit H (A.choose j keys H h hist).ring <;>
    simp [selector, HistChoices.selector, hybrid, hybChoice, side, PubSigner.Choice.idx, hA]

/-- **In the experiment `1` the game selects as the hybrid answering with the second witnesses**
unless the signer admits the chosen ring and the two public values of the chosen entry differ. -/
theorem selector_true_ne (T : A.CTable) (j : Fin Q) (h : Query k kN kS L → Out k e)
    (hist : PubHist S.Pub M.NIProof j)
    (hne : A.selector keys H true (A.side true T) j h hist ≠
      (A.hybrid H keys T).selector (fun _ => true) j h hist) :
    S.Admit H (A.choose j keys H h hist).ring ∧
      (T j ⟨_, A.choose_mem j keys H h hist⟩).1.1 ≠ (T j ⟨_, A.choose_mem j keys H h hist⟩).2.1 := by
  by_cases hA : S.Admit H (A.choose j keys H h hist).ring
  · refine ⟨hA, fun hv => hne ?_⟩
    simp [selector, HistChoices.selector, hybrid, hybChoice, side, PubSigner.Choice.idx, hA, hv]
  · exact absurd (by simp [selector, HistChoices.selector, hybrid, hA]) hne

end Hybrid

/-! ### The bad event -/

section Bad

variable (E : (j : ι) → (M.comp j).Encoder) {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type} [Fintype R] [Nonempty R]
  (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt) (H : S.Orc) (keys : Fin n → S.KeyCoins)

/-- The experiment `b` at the table `T`. -/
noncomputable abbrev run (b : Bool) (T : A.Table) (j : ℕ) (hj : j ≤ Q) :
    PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof j) :=
  pubRun (proofLawAt E Qs honest H) PubSigner.Stmt.pub (A.selector keys H b T) j hj

/-- **The bad event of round `i`** at the coupled table `T`: in the experiment `1` before round
`i`, the signer admits the ring of round `i`'s chosen challenge and the two public values of its
entry differ. -/
noncomputable def badProb (T : A.CTable) (i : Fin Q) : ℝ≥0∞ :=
  (A.run E Qs honest H keys true (A.side true T) i i.2.le).toOuterMeasure
    {s | S.Admit H (A.choose i keys H s.1 s.2).ring ∧
      (T i ⟨_, A.choose_mem i keys H s.1 s.2⟩).1.1 ≠ (T i ⟨_, A.choose_mem i keys H s.1 s.2⟩).2.1}

/-- The experiment before round `i` does not read row `i` of the table. -/
theorem run_side_update (T : A.CTable) (i : Fin Q) (r : A.choices → (S.Pub × S.Sig) × (S.Pub × S.Sig)) :
    A.run E Qs honest H keys true (A.side true (Function.update T i r)) i i.2.le =
      A.run E Qs honest H keys true (A.side true T) i i.2.le := by
  refine pubRun_congr _ _ fun i' hi' => ?_
  have hne : i' ≠ i := fun h => by rw [h] at hi'; exact lt_irrefl _ hi'
  funext h hist
  simp only [selector, side, Function.update_of_ne hne]

/-- **The bad event of each round has probability at most `ε`** over the coupled table, when every
valid admitted challenge's two public-value laws are within `ε`. -/
theorem sum_coupledLaw_mul_badProb_le {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring →
      PMF.tvDist ((c.signLaw H keys false).map Prod.fst) ((c.signLaw H keys true).map Prod.fst) ≤ ε)
    (i : Fin Q) :
    ∑ T, A.coupledLaw H keys T * A.badProb E Qs honest H keys T i ≤ ENNReal.ofReal ε := by
  classical
  let G : A.CTable → (A.choices → (S.Pub × S.Sig) × (S.Pub × S.Sig)) → ℝ≥0∞ := fun T row =>
    (A.run E Qs honest H keys true (A.side true T) i i.2.le).toOuterMeasure
      {s | S.Admit H (A.choose i keys H s.1 s.2).ring ∧
        (row ⟨_, A.choose_mem i keys H s.1 s.2⟩).1.1 ≠ (row ⟨_, A.choose_mem i keys H s.1 s.2⟩).2.1}
  have hG : ∀ T r, G (Function.update T i r) = G T := fun T r => by
    funext row
    simp only [G, run_side_update]
  refine PMF.sum_pi_mul_apply_le _ i G hG fun T => ?_
  -- average the bad event of the chosen challenge over the row
  simp only [G, PMF.toOuterMeasure_apply]
  calc ∑ row, (PMF.pi fun c => A.coupling H keys c) row *
        ∑' s, {s : (Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof i |
          S.Admit H (A.choose i keys H s.1 s.2).ring ∧
          (row ⟨_, A.choose_mem i keys H s.1 s.2⟩).1.1 ≠
            (row ⟨_, A.choose_mem i keys H s.1 s.2⟩).2.1}.indicator
          (A.run E Qs honest H keys true (A.side true T) i i.2.le) s
      = ∑' s, A.run E Qs honest H keys true (A.side true T) i i.2.le s *
          ∑ row, (PMF.pi fun c => A.coupling H keys c) row *
            (if S.Admit H (A.choose i keys H s.1 s.2).ring ∧
              (row ⟨_, A.choose_mem i keys H s.1 s.2⟩).1.1 ≠
              (row ⟨_, A.choose_mem i keys H s.1 s.2⟩).2.1 then 1 else 0) := by
        rw [← tsum_fintype (L := SummationFilter.unconditional _)]
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun s => ?_
        rw [tsum_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun row _ => ?_
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        split_ifs <;> ring
    _ ≤ ∑' s, A.run E Qs honest H keys true (A.side true T) i i.2.le s * ENNReal.ofReal ε := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
        by_cases hA : S.Admit H (A.choose i keys H s.1 s.2).ring
        swap
        · simp only [hA, false_and, ite_false, mul_zero, Finset.sum_const_zero]
          exact bot_le
        simp only [hA, true_and]
        set c : A.choices := ⟨_, A.choose_mem i keys H s.1 s.2⟩
        rw [PMF.sum_pi_mul_apply_coord (fun c => A.coupling H keys c) c
          (fun x => if x.1.1 ≠ x.2.1 then 1 else 0)]
        have hm : ∑ x, A.coupling H keys c x * (if x.1.1 ≠ x.2.1 then 1 else 0) =
            (A.coupling H keys c).toOuterMeasure {x | x.1.1 ≠ x.2.1} := by
          rw [PMF.toOuterMeasure_apply, tsum_fintype]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Set.indicator_apply, Set.mem_setOf_eq]
          split_ifs <;> simp
        rw [hm, ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
          (PMF.toOuterMeasure_apply_le_one _ _))]
        exact ENNReal.ofReal_le_ofReal ((A.toReal_coupling_ne_le H keys c).trans
          (hε c.1 c.2 (A.choose_valid i keys H s.1 s.2) hA))
    _ = ENNReal.ofReal ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Bad

/-! ### One oracle and one set of keys -/

section Fixed

variable {E : (j : ι) → (M.comp j).Encoder} {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
  {honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt}

/-- **The experiments at a fixed oracle `H` and fixed users' coins are close**: for signers that
sign validly at `H` (`hS`), a compiled argument whose honest prover has honest-verifier zero knowledge at error `δ`
for the ring relation at `H` (`hz`), and an `ε` bounding the distance of the two public-value laws
of every valid challenge of the set whose ring the signer admits at `H`, every event of the
oracle of the compiled argument and the history has probabilities within
`Q · ε + Q · wiError δ (Q · C)`. A refused round is `⊥` in both experiments and reads no
signature. -/
theorem abs_condProb_sub_le (H : S.Orc) (keys : Fin n → S.KeyCoins) (hS : A.SignsValidly H keys)
    (Rv : M.Reveal E (Qs H)) {PubZ : Type} {pubZ : S.Stmt → PubZ}
    {sim : CausalJointSimulator Rv.MV PubZ} {δ : ℝ≥0}
    (hz : CausalHVZK Rv.MV (S.rel H) (honest H) pubZ sim δ) {C : ℕ} (hC : A.choices.card ≤ C)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring →
      PMF.tvDist ((c.signLaw H keys false).map Prod.fst) ((c.signLaw H keys true).map Prod.fst) ≤ ε)
    (U : (Query k kN kS L → Out k e) → PubHist S.Pub M.NIProof Q → Prop) :
    |(((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
        {s | U s.1 s.2}).toReal -
      (((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure
        {s | U s.1 s.2}).toReal| ≤ Q * ε + Q * M.wiError δ (Q * C) := by
  classical
  set μ := A.coupledLaw H keys
  let law := proofLawAt E Qs honest H
  let hyb : A.CTable → Bool → PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q) :=
    fun T b => pubRun law PubSigner.Stmt.pub ((A.hybrid H keys T).selector fun _ => b) Q le_rfl
  let U' : Set ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q) := {s | U s.1 s.2}
  let f : Bool → A.CTable → ℝ≥0∞ := fun b T =>
    (A.run E Qs honest H keys b (A.side b T) Q le_rfl).toOuterMeasure U'
  let g : A.CTable → ℝ≥0∞ := fun T => (hyb T true).toOuterMeasure U'
  have hcond : ∀ b, ((A.tableLaw H keys b).bind fun T =>
      A.run E Qs honest H keys b T Q le_rfl).toOuterMeasure U' = ∑ T, μ T * f b T := fun b => by
    rw [A.tableLaw_eq_map_side H keys b, PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_fintype]
    rfl
  change |(((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
        U').toReal - _| ≤ _
  rw [hcond false]
  change |(∑ T, μ T * f false T).toReal - (((A.tableLaw H keys true).bind fun T =>
    A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure U').toReal| ≤ _
  rw [hcond true]
  have hle1 : ∀ (p : PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q)),
      p.toOuterMeasure U' ≤ 1 := fun p => PMF.toOuterMeasure_apply_le_one _ _
  -- the hybrid at the witnesses of user `0` and of user `1`
  have hwi : ∀ T, (μ T).toReal * |(f false T).toReal - (g T).toReal| ≤
      (μ T).toReal * (Q * M.wiError δ (Q * C)) := fun T => by
    by_cases hT : μ T = 0
    · simp [hT]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    have hTs : T ∈ μ.support := (PMF.mem_support_iff _ _).2 hT
    have hadv := gameAdvantage_pubRun_le (F := A.hybrid H keys T) PubSigner.Stmt.pub Rv hz
      (A.hybridSet H keys T) (A.hybridSet_admissible H keys hS hTs) (A.hybrid_mem H keys T) U
    have hf : f false T = (hyb T false).toOuterMeasure U' := by
      simp only [f, hyb, run, A.selector_false_eq H keys T]
      rfl
    rw [hf]
    refine hadv.trans (mul_le_mul_of_nonneg_left (SPBCS.wiError_mono δ ?_) (Nat.cast_nonneg _))
    exact (A.card_hybridSet_le H keys T).trans (Nat.mul_le_mul_left _ hC)
  -- the hybrid at the witnesses of user `1` and the experiment `1`
  have hbad : ∀ T, |(g T).toReal - (f true T).toReal| ≤
      ∑ i : Fin Q, (A.badProb E Qs honest H keys T i).toReal := fun T => by
    refine (PMF.abs_toOuterMeasure_sub_le_tvDist _ _ _).trans ?_
    rw [PMF.tvDist_comm]
    refine (tvDist_pubRun_le _ _ Q le_rfl).trans (Finset.sum_le_sum fun i _ => ?_)
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.toOuterMeasure_apply_le_one _ _)) (PMF.toOuterMeasure_mono _ ?_)
    rintro s ⟨hs, -⟩
    exact A.selector_true_ne H keys T _ s.1 s.2 hs
  calc |(∑ T, μ T * f false T).toReal - (∑ T, μ T * f true T).toReal|
      ≤ |(∑ T, μ T * f false T).toReal - (∑ T, μ T * g T).toReal| +
          |(∑ T, μ T * g T).toReal - (∑ T, μ T * f true T).toReal| := abs_sub_le _ _ _
    _ ≤ ∑ T, (μ T).toReal * (Q * M.wiError δ (Q * C)) +
          ∑ T, (μ T).toReal * ∑ i : Fin Q, (A.badProb E Qs honest H keys T i).toReal := by
        refine add_le_add ((PMF.abs_sum_mul_sub_sum_mul_le μ (fun _ => hle1 _) fun _ => hle1 _).trans
          (Finset.sum_le_sum fun T _ => hwi T))
          ((PMF.abs_sum_mul_sub_sum_mul_le μ (fun _ => hle1 _) fun _ => hle1 _).trans
          (Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hbad T) ENNReal.toReal_nonneg))
    _ ≤ Q * M.wiError δ (Q * C) + Q * ε := by
        rw [← Finset.sum_mul, ← ENNReal.toReal_sum fun T _ => μ.apply_ne_top T, PMF.sum_coe,
          ENNReal.toReal_one, one_mul]
        refine add_le_add le_rfl ?_
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        calc ∑ i : Fin Q, ∑ T, (μ T).toReal * (A.badProb E Qs honest H keys T i).toReal
            ≤ ∑ _i : Fin Q, ε := Finset.sum_le_sum fun i _ => by
              have h := A.sum_coupledLaw_mul_badProb_le E Qs honest H keys hε0 hε i
              have hne : ∀ T, μ T * A.badProb E Qs honest H keys T i ≠ ⊤ := fun T =>
                ENNReal.mul_ne_top (μ.apply_ne_top T) (ne_top_of_le_ne_top ENNReal.one_ne_top
                  (PMF.toOuterMeasure_apply_le_one _ _))
              simp_rw [← ENNReal.toReal_mul]
              rw [← ENNReal.toReal_sum fun T _ => hne T]
              exact ENNReal.toReal_le_of_le_ofReal hε0 h
          _ = Q * ε := by simp
    _ = Q * ε + Q * M.wiError δ (Q * C) := add_comm _ _

end Fixed

/-! ### Anonymity -/

section Main

variable {E : (j : ι) → (M.comp j).Encoder} {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
  {honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt}

/-- The probability of the event `D` in the experiment `b`, at the users' coins `keys` and the
oracle `H`. -/
theorem toOuterMeasure_game_eq (b : Bool)
    (D : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) :
    (A.game E Qs honest b).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2} =
      ∑ keys, PMF.uniformOfFintype _ keys * ∑ H, PMF.uniformOfFintype _ H *
        ((A.tableLaw H keys b).bind fun T => A.run E Qs honest H keys b T Q le_rfl).toOuterMeasure
          {s | D keys H s.1 s.2} := by
  rw [game, PMF.toOuterMeasure_bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun keys _ => ?_
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype]
  refine congrArg _ (Finset.sum_congr rfl fun H _ => ?_)
  rw [← PMF.map_bind, PMF.toOuterMeasure_map_apply]
  rfl

/-- The probabilities of an event in the two experiments at fixed users' coins and oracle differ by
at most one. -/
theorem abs_condProb_sub_le_one (H : S.Orc) (keys : Fin n → S.KeyCoins)
    (U : (Query k kN kS L → Out k e) → PubHist S.Pub M.NIProof Q → Prop) :
    |(((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
        {s | U s.1 s.2}).toReal -
      (((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure
        {s | U s.1 s.2}).toReal| ≤ 1 := by
  have key : ∀ p : PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q),
      0 ≤ (p.toOuterMeasure {s | U s.1 s.2}).toReal ∧ (p.toOuterMeasure {s | U s.1 s.2}).toReal ≤ 1 :=
    fun p => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact PMF.toOuterMeasure_apply_le_one _ _)⟩
  have h1 := key ((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl)
  have h2 := key ((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl)
  rw [abs_sub_le_iff]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Anonymity against full key exposure, with the public value produced by the signer**
(BKM06 Definition 4, ePrint 2005/304, p. 5, with the keys given at the start as in CCLM22
Experiment 2, p. 21, `Q` adaptive challenges, signing queries included, and both oracles visible;
the adversary chooses any ring holding the two users' keys and sees `⊥` for the rings the signer
refuses): for the spBCS compilation `M` whose honest prover has honest-verifier zero knowledge at
error `δ` for the ring relation at every oracle `H` (`hz`), every adversary with at most `C`
challenges in its set, a predicate `Good` of the users' coins and the oracle under which the
signers of the valid admitted challenges sign validly (`hS`), and every `ε` bounding, at good
coins and oracles, the distance of the two users' public-value laws of every valid challenge of
the set whose ring the signer admits at `H` (`hε`), the advantage of every distinguisher given the
users' coins, both oracles and the history is at most
`Q · 𝔼_{keys, H} ε + Q · wiError δ (Q · C) + Pr_{keys, H}[¬ Good]`. Refused rounds are `⊥` in
both experiments, a function of `H`, the ring and the history, so they add nothing to the
bound. -/
theorem advantage_le (Rv : ∀ H, M.Reveal E (Qs H)) {PubZ : Type}
    {pubZ : S.Stmt → PubZ} {sim : ∀ H, CausalJointSimulator (Rv H).MV PubZ} {δ : ℝ≥0}
    (hz : ∀ H, CausalHVZK (Rv H).MV (S.rel H) (honest H) pubZ (sim H) δ) {C : ℕ}
    (hC : A.choices.card ≤ C) (Good : (Fin n → S.KeyCoins) → S.Orc → Prop)
    [∀ keys H, Decidable (Good keys H)] (hS : ∀ keys H, Good keys H → A.SignsValidly H keys)
    (ε : (Fin n → S.KeyCoins) → S.Orc → ℝ) (hε0 : ∀ keys H, 0 ≤ ε keys H)
    (hε : ∀ keys H, Good keys H → ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring →
      PMF.tvDist ((c.signLaw H keys false).map Prod.fst) ((c.signLaw H keys true).map Prod.fst) ≤
        ε keys H)
    (D : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) :
    A.advantage E Qs honest D ≤ Q * (𝔼 keys, 𝔼 H, ε keys H) + Q * M.wiError δ (Q * C) +
      𝔼 keys, 𝔼 H, (if Good keys H then 0 else 1 : ℝ) := by
  unfold advantage GordieHowe.gameAdvantage GordieHowe.advantage
  change |((A.game E Qs honest false).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal -
    ((A.game E Qs honest true).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal| ≤ _
  rw [toOuterMeasure_game_eq, toOuterMeasure_game_eq]
  have hwi0 : 0 ≤ M.wiError δ (Q * C) := SPBCS.wiError_nonneg δ (Q * C)
  have hle : ∀ (p : PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q)) (s : Set _),
      p.toOuterMeasure s ≤ 1 := fun p s => PMF.toOuterMeasure_apply_le_one _ _
  have hle2 : ∀ b (keys : Fin n → S.KeyCoins), ∑ H, PMF.uniformOfFintype S.Orc H *
      ((A.tableLaw H keys b).bind fun T => A.run E Qs honest H keys b T Q le_rfl).toOuterMeasure
        {s | D keys H s.1 s.2} ≤ 1 := fun b keys =>
    (Finset.sum_le_sum fun H _ => mul_le_of_le_one_right' (hle _ _)).trans_eq
      (by rw [← tsum_fintype (L := SummationFilter.unconditional _)]; exact PMF.tsum_coe _)
  -- one oracle and one set of keys
  have hpt : ∀ keys H,
      |(((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
        {s | D keys H s.1 s.2}).toReal -
      (((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure
        {s | D keys H s.1 s.2}).toReal| ≤
        Q * ε keys H + Q * M.wiError δ (Q * C) + (if Good keys H then 0 else 1 : ℝ) := by
    intro keys H
    have hQε : 0 ≤ (Q : ℝ) * ε keys H := mul_nonneg (Nat.cast_nonneg _) (hε0 keys H)
    have hQw : 0 ≤ (Q : ℝ) * M.wiError δ (Q * C) := mul_nonneg (Nat.cast_nonneg _) hwi0
    by_cases hG : Good keys H
    · rw [if_pos hG, add_zero]
      exact A.abs_condProb_sub_le H keys (hS keys H hG) (Rv H) (hz H) hC (hε0 keys H)
        (hε keys H hG) (D keys H)
    · rw [if_neg hG]
      linarith [A.abs_condProb_sub_le_one (E := E) (Qs := Qs) (honest := honest) H keys (D keys H)]
  refine (PMF.abs_sum_mul_sub_sum_mul_le _ (hle2 false) (hle2 true)).trans ?_
  have hinner : ∀ keys : Fin n → S.KeyCoins,
      |(∑ H, PMF.uniformOfFintype S.Orc H *
        ((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
          {s | D keys H s.1 s.2}).toReal -
        (∑ H, PMF.uniformOfFintype S.Orc H *
        ((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure
          {s | D keys H s.1 s.2}).toReal| ≤
        Q * (𝔼 H, ε keys H) + Q * M.wiError δ (Q * C) +
          𝔼 H, (if Good keys H then 0 else 1 : ℝ) := fun keys => by
    refine (PMF.abs_sum_mul_sub_sum_mul_le _ (fun _ => hle _ _) fun _ => hle _ _).trans ?_
    calc ∑ H, (PMF.uniformOfFintype S.Orc H).toReal * _
        ≤ ∑ H, (PMF.uniformOfFintype S.Orc H).toReal *
            (Q * ε keys H + Q * M.wiError δ (Q * C) + (if Good keys H then 0 else 1 : ℝ)) :=
          Finset.sum_le_sum fun H _ => mul_le_mul_of_nonneg_left (hpt keys H)
            ENNReal.toReal_nonneg
      _ = Q * (𝔼 H, ε keys H) + Q * M.wiError δ (Q * C) +
            𝔼 H, (if Good keys H then 0 else 1 : ℝ) := by
          simp only [PMF.toReal_uniformOfFintype_apply, Fintype.expect_eq_sum_div_card]
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hc : (Fintype.card S.Orc : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
          field_simp
  calc ∑ keys, (PMF.uniformOfFintype (Fin n → S.KeyCoins) keys).toReal * _
      ≤ ∑ keys, (PMF.uniformOfFintype (Fin n → S.KeyCoins) keys).toReal *
          (Q * (𝔼 H, ε keys H) + Q * M.wiError δ (Q * C) +
            𝔼 H, (if Good keys H then 0 else 1 : ℝ)) :=
        Finset.sum_le_sum fun keys _ => mul_le_mul_of_nonneg_left (hinner keys)
          ENNReal.toReal_nonneg
    _ = Q * (𝔼 keys, 𝔼 H, ε keys H) + Q * M.wiError δ (Q * C) +
          𝔼 keys, 𝔼 H, (if Good keys H then 0 else 1 : ℝ) := by
        simp only [PMF.toReal_uniformOfFintype_apply, Fintype.expect_eq_sum_div_card]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hc : (Fintype.card (Fin n → S.KeyCoins) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.2 Fintype.card_ne_zero
        field_simp

end Main

end PubAnonAdversary

end Game

end GordieHowe.Ring
