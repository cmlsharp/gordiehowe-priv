-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.ProductMod
public import GordieHowe.Language.Realizations.Derivation.Events

@[expose] public section

/-!
# GordieHowe: the kernel of a product form from a public-table selection

The interval source `tableKernel` (`lib/gordiehowe/compiler/derivation_check.h`, `src tableKernel`)
bounds the coefficients of the polynomial whose spectrum a product form's kernel holds, when that
spectrum is selected from a public table (`lib/gordiehowe/lib/table.h`, `select_row`): the
selection's record is the natural-order transform of a row of the table. The C++ checks the
bounds' fit and trusts the hull; the rule here recomputes it (`tableKernelFact`): the table's value
has a declared range `[0, B)` (`sr`), so a row's entries lie in `[0, B − 1]`, within `[lo, hi]`.

The selection holds only up to its fingerprint (`SelEvent`): where every field `equal` of rank below
the derivation's holds and the selection event does not occur, the record is a row's transform
(`SelExact`), and the inverse transform returns the row (`tableKernelFact_sound`).
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section

variable (ir : RealizedProgram)

/-- **Value `v` reads only what is fixed when challenge `j` is drawn** (`ReadFixedAt`), through
the reads table. -/
def readsFixedB (j v : ℕ) : Bool :=
  (ir.readsT.getD v []).all fun rd => decide (ir.ReadFixedAt j rd)

/-- **The side conditions of `tableKernel`** for the kernel fact of value `v` in domain `d` from
selection `sh` of predicate `q`, block `b` and hull `[lo, hi]`, at a derivation of rank `self`:
the block is `0`, the selection's record is `v` and its domain `d`, the record and the table read
in `d`'s field and are fixed when the fingerprint's challenge is drawn, the table's rows lie within
its value, the table's value has a declared range `[0, B)` with `[0, B − 1] ⊆ [lo, hi]`, the hull
is within `(−p/2, p/2)`, the transform's root is a primitive `2n`-th root of unity, and every field
`equal` has rank below `self`. -/
def tableKernelOkB (sr : List (ℕ × ℕ)) (ctx : DerivCtx) (self d v q b : ℕ) (lo hi : ℤ)
    (sh : SelShape) : Bool :=
  decide (b = 0 ∧ sh.record = v ∧ sh.domain = d ∧ d < ir.domains.length ∧
    q < ir.predicates.length ∧
    ir.valueField sh.record = ir.domainField d ∧ ir.valueField sh.table = ir.domainField d ∧
    sh.rows * sh.n ≤ (ir.value sh.table).size ∧ lo ≤ 0 ∧
    2 * |lo| < (ir.charOf (ir.domainField d) : ℤ) ∧ 2 * |hi| < (ir.charOf (ir.domainField d) : ℤ)) &&
    ir.readsFixedB sh.chal sh.record && ir.readsFixedB sh.chal sh.table &&
    sr.any (fun vN => vN.1 == sh.table && decide ((vN.2 : ℤ) - 1 ≤ hi)) &&
    rootOkB (ir.charOf (ir.domainField d)) sh.n sh.psi &&
    (List.range ir.predicates.length).all fun p =>
      !(ir.predicate p).body.isEqual || decide (ctx.rank p < self)

/-- **The rule `tableKernel`** for value `v` in domain `d` at a derivation of rank `self`: from the
selection of predicate `qs[0]` whose record a product form's kernel reads (`kernelSel?`), its side
conditions checked (`tableKernelOkB`), the kernel fact of block `0` of `v`: the coefficients of the
polynomial whose spectrum (in natural order at the selection's root) it holds lie in `[lo, hi]`;
none for any other source. -/
def tableKernelFact (sr : List (ℕ × ℕ)) (ctx : DerivCtx) (self d v : ℕ) : IvlSrc → Option Fact
  | .tableKernel _ b (q :: _) lo hi =>
    match ir.kernelSel? q with
    | some sh =>
      if ir.tableKernelOkB sr ctx self d v q b lo hi sh = true then
        some (.kernel d v 0 sh.n sh.psi true lo hi)
      else none
    | none => none
  | _ => none

end

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **`readsFixedB` decides that a value reads only what is fixed when `j` is drawn.** -/
theorem readsFixedB_iff (hwf : ir.WellFormed) {j v : ℕ} :
    ir.readsFixedB j v = true ↔ ∀ rd ∈ ir.nodeReads ir.fuel v, ir.ReadFixedAt j rd := by
  simp only [readsFixedB, List.all_eq_true, decide_eq_true_eq]
  exact forall_congr' fun rd => imp_congr_left (mem_readsT hwf v rd).symm

/-- **A predicate whose values are fixed when challenge `j` is drawn** (`readsFixedB`, through
the reads table) reads only what is fixed then. -/
theorem predReads_fixed_of_readsFixedB (hwf : ir.WellFormed) {j : ℕ} {b : PredBody}
    (h : (ir.predNodes b).all (ir.readsFixedB j) = true) :
    ∀ rd ∈ ir.predReads b, ir.ReadFixedAt j rd := by
  intro rd hrd
  obtain ⟨v, hv, hrv⟩ := List.mem_flatMap.1 hrd
  exact (readsFixedB_iff hwf).1 (List.all_eq_true.1 h v hv) rd hrv

/-- **`tableKernelFact_sound`**: the kernel fact holds, or the selection event occurs. Without the
event, the fields' `equal`s (of rank below `self`, `CitesHold`) give the record as the transform of
a row of the table (`SelExact`); the inverse transform returns the row (`inverseNttNatural_nttNatural`),
whose entries are naturals below the table's declared bound (`hS`), read centred as themselves. -/
theorem tableKernelFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {sr : List (ℕ × ℕ)} {e : ir.Env I}
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    {ctx : DerivCtx} {self : ℕ} (hc : CitesHold e ctx self) {d v : ℕ} {s : IvlSrc} {f : Fact}
    (hf : ir.tableKernelFact sr ctx self d v s = some f) :
    f.Holds e ∨ ∃ j, ir.RealEvent j e := by
  unfold tableKernelFact at hf
  split at hf
  swap
  · cases hf
  rename_i b q _ lo hi
  split at hf
  swap
  · cases hf
  rename_i sh hk
  split_ifs at hf with hok
  cases hf
  simp only [tableKernelOkB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨rfl, rfl, rfl, hd, hq, hfr, hft, hrows, hlo0, hlo, hhi⟩, hrr⟩, hrt⟩,
    ⟨⟨T, B⟩, hTB, rfl, hB⟩⟩, hroot⟩, hrank⟩ := hok
  simp only at hTB hB
  by_cases hev : ir.SelEvent sh.chal e
  · exact .inr ⟨_, .inr (.inr hev)⟩
  refine .inl ?_
  have hx : ir.SelExact (ir.reader e) sh := by
    by_contra hx
    refine hev ⟨q, hq, sh, hk, rfl, fun rd hrd => ?_, fun p hp heq _ => ?_, hx⟩
    · rcases List.mem_append.1 hrd with hrd | hrd
      · exact (readsFixedB_iff hwf).1 hrr rd hrd
      · exact (readsFixedB_iff hwf).1 hrt rd hrd
    · refine hc.1 p hp ?_
      rcases hrank p hp with h | h
      · rw [h] at heq
        cases heq
      · exact h
  obtain ⟨r, hr, hrow⟩ := hx
  have hdF := domainField_lt hwf hd
  have hchar := charP_field hI hdF
  have hp := hI.characteristic _ hdF
  have htn := hL.toNat_natCast _ hdF
  have hR := rootFacts_of_rootOkB hwf hI hL hd hroot
  intro i hin
  -- coefficient `i` of the kernel's polynomial is entry `r n + i` of the table
  have hpoly : ir.kernelPoly (ir.reader e) sh.domain sh.record 0 sh.n sh.psi true i =
      castElt (ir.reader e sh.table (r * sh.n + i)) := by
    unfold kernelPoly
    simp only [ite_true, NamedOp.formPoly, zero_mul, zero_add]
    rw [Ops.inverseNttNatural_congr hrow, Ops.inverseNttNatural_nttNatural hR.prim hR.ne _ hin]
  have hidx : r * sh.n + i < (ir.value sh.table).size := by
    have : r * sh.n + i < sh.rows * sh.n := by
      have : (r + 1) * sh.n ≤ sh.rows * sh.n := Nat.mul_le_mul_right _ hr
      rw [Nat.succ_mul] at this
      omega
    omega
  obtain ⟨c, hcB, hcv⟩ := hS (sh.table, B) hTB _ hidx
  rw [hpoly, hcv, castElt_natCast hft]
  have hcz : 2 * |(c : ℤ)| < (ir.charOf (ir.domainField sh.domain) : ℤ) := by
    rw [abs_of_nonneg (Int.natCast_nonneg c)]
    have : (c : ℤ) ≤ hi := by omega
    have : hi ≤ |hi| := le_abs_self hi
    omega
  have hcast : ((c : ℕ) : (I (ir.domainField sh.domain)).K) =
      ((c : ℤ) : (I (ir.domainField sh.domain)).K) := (Int.cast_natCast c).symm
  rw [hcast, FieldInterp.coefInt_intCast hp hchar htn hcz]
  exact ⟨by omega, by omega, rfl⟩

end

end GordieHowe.RealizedProgram
