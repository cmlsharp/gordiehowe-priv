-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.HonestFull
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Honest
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.HashFacts
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.AlgebraFacts
public import GordieHowe.Applications.Falcon512.Native.QROMParams.ProofSystem

@[expose] public section

/-!
# GordieHowe: the honest prover's program facts of `Falcon512.Native.QROMParams`

The program facts the generic honest files read (`FalconHHonest`, `FalconHSelHonest`,
`FalconAHonest`), decided on the tables of `GordieHowe.Generated.Falcon512.Native.QROMParams.Program.program`
(export `3ed06086`).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open ROMParams

open Generated.Falcon512.Native.QROMParams.Program

set_option maxRecDepth 4096 in
/-- The honest hash facts of the program of `Falcon512.Native.QROMParams`. -/
instance : FalconHHonest program where
  words_checks := by decide +kernel
  state_checks := by decide +kernel
  buf_checks := by decide +kernel

/-- The selection values of the program of `Falcon512.Native.QROMParams`. -/
instance : FalconHSelHonest program where
  sel_checks := by decide +kernel

set_option maxRecDepth 8192 in
/-- The honest norm facts of the program of `Falcon512.Native.QROMParams` (`Norm.FalconNormHonest`): the norm's
values are private committed cells. -/
noncomputable instance : Norm.FalconNormHonest program where
  privCell := by decide +kernel

set_option maxRecDepth 8192 in
/-- The facts of honest domain A of the program of `Falcon512.Native.QROMParams`: the norm at domain and field `1`, the
field-form signature `289`, `c_A`'s check `292` and `mac.equal` `309`. -/
noncomputable instance : FalconAHonest program where
  toFalconAAlg := inferInstance
  norm_dA := rfl
  norm_fA := rfl
  norm_ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  pSigE := 289
  pCA := 292
  pMac := 309
  a_checks := by decide +kernel
  sizes_H := by decide +kernel
  const44 := by decide +kernel
  sigE_body := ⟨_, rfl⟩
  sigE_len := by decide +kernel
  ca_body := ⟨_, rfl⟩
  mac_body := ⟨_, _, rfl, by decide⟩
  cross_fields := by decide +kernel

/-! ## The honest strategy's program facts -/

namespace Facts

open RealizedProgram

/-- The blind's cells, decided. -/
theorem blind_cells : (program.value 606).kind = .padCopy 609 "polynomialBits" ∧
    (program.value 606).domain < program.domains.length ∧
    (∀ j < 256, CellKey.val 606 j ∈ program.cellKeys (program.value 606).domain) ∧
    program.valueField 606 = 1 ∧ (program.value 606).size = 256 :=
  ⟨kind_of_isPadCopyB (by decide +kernel), by decide +kernel,
    fun j hj => (program.mem_cellKeys_val).2 ⟨by decide +kernel, by decide +kernel,
      by have : (program.value 606).size = 256 := by decide +kernel
         omega⟩, by decide +kernel, by decide +kernel⟩

/-- **The MAC's predicates**: the H predicate, the accumulator rows, the residues' check, the
lookups on the digits and the final quotient, the tail. -/
def macRolePreds : List ℕ := [274, 285, 286, 287, 288, 296, 305, 306, 307]

open Honest in
/-- The only cross-field `equal` is `mac.equal` (predicate `309`), decided. -/
theorem cross_only : (List.range program.predicates.length).all (fun q => q == 309 ||
    match (program.predicate q).body with
    | .cross _ _ _ _ _ _ => false
    | _ => true) = true := by
  decide +kernel

end Facts

set_option maxRecDepth 4096 in
/-- The values of the program of `Falcon512.Native.QROMParams` are distinct where the honest valuation reads them. -/
instance : FalconHValues program where
  not_hash_sel := by decide +kernel
  not_hash_norm := by decide +kernel
  blind_not := by decide +kernel

namespace Facts

set_option maxRecDepth 4096 in
/-- Every other predicate is the hash's or of `aPreds`, decided (`FalconHonestFull.src_cover`). -/
theorem src_cover : ∀ q < program.predicates.length, q ∉ Facts.macRolePreds →
    (program.inSource (program.predicate q) = true ∨ program.fieldRowRealB q = true) →
      q < 270 ∨ q ∈ aPreds program := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- The committed source values' classes, decided (`FalconHonestFull.cell_classes`). -/
theorem cell_classes : (List.range program.values.length).all (fun v =>
    !program.isCellValue (program.value v).domain v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        (v == 96 || (wordsOwner? v).isSome || v == 588 || v == 590)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "bit" &&
        [45, 46, 47, 591].contains v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        (NormValues program).contains v)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Only the blind is a pad copy, decided (`FalconHonestFull.padCopy_only`). -/
theorem padCopy_only : (List.range program.values.length).all (fun w => w == 606 ||
    match (program.value w).kind with
    | .padCopy _ _ => false
    | _ => true) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- The node-typed values that are not late, decided (`FalconHonestFull.typed_classes`). -/
theorem typed_classes : (List.range program.values.length).all (fun v =>
    !((program.value v).typeSource == .node) || decide (program.IsLate v) ||
      ((match (program.value v).kind with
        | .bits w _ => (match (program.value w).kind with
          | .priv => true
          | _ => false)
        | _ => false) && (program.value v).type == .bit) ||
      (program.privCellB v && program.isCellValue (program.value v).domain v &&
        (match (program.value v).type with
          | .sub S => (program.value v).node.map (·.name) == some S
          | .bit => (program.value v).node.map (·.name) == some "bit" && program.valueField v == 0
          | .field => true))) = true := by
  decide +kernel

end Facts

/-- The program's one statement bound: the key's entries `hhat` below `q`. -/
theorem bounds : program.declaredRanges = [(593, 12289)] := by decide +kernel

open Facts RealizedProgram in
set_option maxRecDepth 4096 in
/-- **The honest-strategy facts of the program of `Falcon512.Native.QROMParams`**: the MAC `mac.equal` with its grouped
tail (`QROMParams.Honest.mac`), its role predicates. -/
noncomputable instance : FalconHonestFull program
    (RealizedProgram.primeNodesOf Generated.Falcon512.Native.QROMParams.Plan.plan program) where
  bounds := bounds
  mac := Honest.mac
  macRolePreds := Facts.macRolePreds
  bw := 256
  mac_shape := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  crossMac p hp dx x dy y k real hb := by
    obtain ⟨q, hq, rfl⟩ := RealizedProgram.exists_index_of_mem hp
    have := List.all_eq_true.1 Facts.cross_only q (List.mem_range.2 hq)
    rw [hb] at this
    simp only [beq_iff_eq, Bool.or_false] at this
    subst this
    rfl
  src_cover := Facts.src_cover
  checks_list := by decide +kernel
  blind_cells := Facts.blind_cells
  cell_classes := Facts.cell_classes
  padCopy_only := Facts.padCopy_only
  typed_classes := Facts.typed_classes

end GordieHowe.Falcon512.Native.QROMParams
