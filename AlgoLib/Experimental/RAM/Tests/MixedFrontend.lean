/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.MixedAlgorithms
import AlgoLib.Experimental.RAM.Prototype.Composition.Encoding
import AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation

/-!
# Mixed scalar, array and owned-procedure regression

The client has no address or backend proof. Its direct indexing and procedure calls
produce one Composition.Program. Backend certificates below are reconstructed for
that exact program, including both eager and lazy buffer implementations.
-/
namespace AlgoLib.Experimental.RAM.Tests.MixedFrontend
open Prototype Prototype.Composition Prototype.Frontend
open Buffer.API MixedAlgorithms

private abbrev leftLayout : Storage.ArrayLayout := ⟨⟨"a.size"⟩, 0, 4⟩
private abbrev rightLayout : Storage.ArrayLayout := ⟨⟨"b.size"⟩, 4, 4⟩
private abbrev bufferLayout : BufferImplementation.Layout := ⟨"buffer", 8, 4⟩
private abbrev inputs (eager : Bool) := (Storage.array leftLayout).sep
  ((Storage.array rightLayout).sep
    ((BufferImplementation.representation bufferLayout eager).sep (Storage.scalar ⟨"count"⟩)))
private abbrev representation (eager : Bool) := (inputs eager).hide (Storage.scalar ⟨"x"⟩)

/-- All expression, ownership, and call certificates are reconstructed from the same body. -/
example (eager : Bool) : Linked 24 (representation eager) mixed.body (representation eager) :=
  inferInstance

/-- Locals do not appear in the public method interface. -/
example : Algorithm (Array Nat × Array Nat × List Nat × Nat)
    (Array Nat × Array Nat × List Nat × Nat) := mixed

/-- Actual Loom correctness is obtained from exactly the same generated obligations. -/
example (a : Array Nat × Array Nat × List Nat × Nat) (h : mixed.requires a) :
    _root_.wp (denote mixed.body a) (fun b _ _ => mixed.ensures a b) () (mixed.credits a) :=
  mixed.loom_correct mixedVerification a h

private abbrev inputEncoder (eager : Bool) : Encoder (inputs eager) :=
  (arrayEncoder leftLayout).sep
    ((arrayEncoder rightLayout).sep
      ((BufferImplementation.encoder bufferLayout eager).sep (scalarEncoder ⟨"count"⟩)
        (by dsimp [BufferImplementation.encoder, scalarEncoder]; decide))
        (by dsimp [Encoder.sep, arrayEncoder, BufferImplementation.encoder, scalarEncoder]; decide))
    (by dsimp [Encoder.sep, arrayEncoder, BufferImplementation.encoder, scalarEncoder]; decide)

private abbrev encoder (eager : Bool) : Encoder (representation eager) :=
  (inputEncoder eager).hide (scalarEncoder ⟨"x"⟩) trivial
    (by dsimp [inputEncoder, Encoder.sep, arrayEncoder, BufferImplementation.encoder,
        scalarEncoder]; decide)

/-- Ordinary values in and out; private scalar initialization and all machine work are counted. -/
def execute (eager : Bool) (a b : Array Nat) (xs : List Nat) (count : Nat)
    (ha : 0 < a.size ∧ a.size ≤ 4) (hb : 0 < b.size ∧ b.size ≤ 4) (hx : xs.length ≤ 4) :=
  runEncoded (rate := 24) (Q := representation eager) mixedProcedure (encoder eager)
    (a, b, xs, count) ⟨ha.1, hb.1, trivial⟩ ⟨ha.2, hb.2, hx, trivial⟩

set_option linter.hashCommand false in
#eval show IO Unit from do
  for eager in [false, true] do
    for hn : n in List.range 5 do
      for x in List.range 5 do
        let result := execute eager #[99] #[x] (List.replicate n 7) 42
          (by decide) (by simp) (by simpa using Nat.le_of_lt_succ (List.mem_range.mp hn))
        unless result.value == (#[x+1], #[x], [], x+1) do
          throw <| IO.userError "mixed values"
        let expected := if eager then 12*n+22 else 21
        unless result.steps == expected do
          throw <| IO.userError s!"mixed cost: {result.steps}, expected {expected}"


private abbrev nestedScratch := local_storage% "nested" : nestedLocals
private abbrev nestedEncoder (eager : Bool) :=
  ((arrayEncoder leftLayout).sep
    ((BufferImplementation.encoder bufferLayout eager).sep (scalarEncoder ⟨"total"⟩)
      (by dsimp [BufferImplementation.encoder, scalarEncoder]; decide))
    (by dsimp [Encoder.sep, arrayEncoder, BufferImplementation.encoder, scalarEncoder]
        decide)).hide
    nestedScratch (by simp [nestedScratch, Encoder.sep, scalarEncoder])
    (by dsimp [nestedScratch, Encoder.sep, arrayEncoder, BufferImplementation.encoder,
        scalarEncoder]; decide)

private instance (eager : Bool) : Linked 24 (nestedEncoder eager).representation
    nestedProcedure.body (nestedEncoder eager).representation := by ram_link

set_option linter.hashCommand false in
#eval show IO Unit from do
  for eager in [false, true] do
    for x in List.range 4 do
      let r := runEncoded (rate := 24) (Q := (nestedEncoder eager).representation)
        nestedProcedure (nestedEncoder eager) (#[x], [7, 8], 99)
        (by simp) (by simp [Encoder.hide, Encoder.sep, arrayEncoder,
          BufferImplementation.encoder, scalarEncoder])
      unless r.value == (#[x+4], [], 4) do
        throw <| IO.userError "nested mixed RAM execution"
      unless r.steps ≤ 24024 do
        throw <| IO.userError "nested mixed budget"

private abbrev flagScratch := local_storage% "flag" : nonzeroLocals
private abbrev flagEncoder := (scalarEncoder ⟨"n"⟩).hide flagScratch
  (by simp [flagScratch, Encoder.sep, scalarEncoder]) (by decide)
private instance : Linked 24 flagEncoder.representation nonzeroProcedure.body
    flagEncoder.representation := by ram_link

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 8 do
    let r := runEncoded (rate := 24) (Q := flagEncoder.representation)
      nonzeroProcedure flagEncoder n trivial trivial
    unless r.value == (if n = 0 then 0 else 1) do
      throw <| IO.userError "compiled inequality"

/- An unsafe read still fails verification when surrounded by valid owned calls. -/
ram method unsafeRead (mut a : Array Nat) (mut buffer : List Nat)
    (mut n : Nat) return (u : Unit)
  do
    buffer.clear()
    n := a[0]!

example : ¬ unsafeRead.Obligations := by
  intro h
  have bad := h (#[], [], 0) trivial
  dsimp [unsafeRead] at bad
  contract_vc

/-- Ownership cannot be duplicated by assigning the same storage to two arrays. -/
example : ¬ Disjoint leftLayout.footprint leftLayout.footprint := by decide

/-- error: Local 'x' is not in scope -/
#guard_msgs in
ram method escapedLocal (mut n : Nat) return (u : Unit)
  do
    if n < 1 then
      let x := 1
    n := x

/-- error: Immutable local; use 'let mut' -/
#guard_msgs in
ram method immutableLocal (mut n : Nat) return (u : Unit)
  do
    let x := n
    x := 1

private abbrev argumentScratch := local_storage% "append" : appendHeadLocals
private abbrev appendEncoder (eager : Bool) :=
  ((arrayEncoder leftLayout).sep (BufferImplementation.encoder bufferLayout eager)
    (by dsimp [arrayEncoder, BufferImplementation.encoder]; decide)).hide argumentScratch
    (by simp [argumentScratch, Encoder.sep, scalarEncoder])
    (by dsimp [argumentScratch, Encoder.sep, scalarEncoder, arrayEncoder,
        BufferImplementation.encoder]; decide)

private instance (eager : Bool) : Linked 24 (appendEncoder eager).representation
    (appendHeadProcedure 4).body (appendEncoder eager).representation := by ram_link

set_option linter.hashCommand false in
#eval show IO Unit from do
  for eager in [false, true] do
    for hn : n in List.range 4 do
      for x in List.range 5 do
        let r := runEncoded (rate := 24) (Q := (appendEncoder eager).representation)
          (appendHeadProcedure 4) (appendEncoder eager) (#[x], List.replicate n 7)
          ⟨by simp, by simpa using List.mem_range.mp hn, trivial⟩
          (by simp [Encoder.hide, Encoder.sep, arrayEncoder, BufferImplementation.encoder]
              have := List.mem_range.mp hn
              omega)
        unless r.value == (#[x], List.replicate n 7 ++ [x+1]) && r.steps == 24 do
          throw <| IO.userError s!"runtime argument: {repr r}"

private abbrev pairEncoder (eager : Bool) := (scalarEncoder ⟨"a"⟩).sep
  ((BufferImplementation.encoder bufferLayout eager).sep (scalarEncoder ⟨"b"⟩)
    (by dsimp [BufferImplementation.encoder, scalarEncoder]; decide))
  (by dsimp [Encoder.sep, scalarEncoder, BufferImplementation.encoder]; decide)

private instance (eager : Bool) : Linked 24 (pairEncoder eager).representation
    callWithFrameProcedure.body (pairEncoder eager).representation := by ram_link

set_option linter.hashCommand false in
#eval show IO Unit from do
  for eager in [false, true] do
    let r := runEncoded (rate := 24) (Q := (pairEncoder eager).representation)
      callWithFrameProcedure (pairEncoder eager) (5, [3,4,5], 8) trivial
      (by simp [Encoder.sep, scalarEncoder, BufferImplementation.encoder])
    unless r.value == (6, [], 10) && r.steps == (if eager then 47 else 10) do
      throw <| IO.userError "paired procedure framing"

/-- error: A procedure cannot receive the same owned resource twice -/
#guard_msgs in
ram method aliasedCall (mut a : Nat) return (u : Unit)
  do
    (a, a) := addBothProcedure

end AlgoLib.Experimental.RAM.Tests.MixedFrontend
