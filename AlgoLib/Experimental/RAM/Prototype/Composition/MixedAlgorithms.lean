/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition
import AlgoLib.Experimental.RAM.Prototype.Composition.Buffer

/-!
# Arrays, local variables, and procedure contracts in one method

`mixed` reads a second array, calls an independently verified buffer procedure,
writes the first array, and returns a scalar. Its allowance is inferred.
`nested` combines direct indexing, locals, a conditional call and nested annotated
loops. Both proofs use mathematical values and logical credits only.

The backend tests link these exact bodies to RAM. No proof here mentions memory,
registers, layouts, or a compiler. Locals are absent from both public interfaces.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.MixedAlgorithms
open Frontend Buffer.API

ram method mixed (mut a : Array Nat) (mut b : Array Nat) (mut buffer : List Nat)
    (mut count : Nat) return (result : Unit)
  require 0 < a.size
  require 0 < b.size
  ensures a[0]! = bOld[0]! + 1
  ensures b = bOld
  ensures buffer = []
  ensures count = bOld[0]! + 1
  do
    let x := b[0]!
    buffer.clear()
    a[0] := x + 1
    count := a[0]!

prove_algorithm mixed by
  contract_vc
  intro a b ha hb
  simp_all [getElem!_pos]
  omega

ram method nested (mut a : Array Nat) (mut buffer : List Nat) (mut total : Nat)
    return (result : Unit)
  require 0 < a.size
  ensures a.size = aOld.size
  ensures buffer = []
  ensures total = 4
  credits 1000
  do
    buffer.clear()
    total := 0
    let mut i := 0
    while i < 2
      invariant i ≤ 2
      invariant 0 < a.size
      invariant a.size = aOld.size
      invariant buffer = []
      invariant total = 2 * i
      invariant 300 * (2 - i) + 100 ≤ remaining
      decreasing 2 - i
      do
        let mut j := 0
        while j < 2
          invariant j ≤ 2
          invariant i < 2
          invariant 0 < a.size
          invariant a.size = aOld.size
          invariant buffer = []
          invariant total = 2 * i + j
          invariant 300 * (2 - (i + 1)) + 50 * (2 - j) + 120 ≤ remaining
          decreasing 2 - j
          do
            let x := a[0]!
            if x < 1 then
              buffer.clear()
            a[0] := x + 1
            total := total + 1
            j := j + 1
        i := i + 1

set_option maxHeartbeats 800000 in
-- This regression intentionally combines two loops and a contract call under a branch.
prove_algorithm nested by
  contract_solve []

ram method nonzero (mut n : Nat) return (result : Nat)
  ensures n = if nOld = 0 then 0 else 1
  do
    if n ≠ 0 then
      n := 1

prove_algorithm nonzero by
  contract_solve []

ram method increment (mut n : Nat) return (result : Nat)
  ensures n = nOld + 1
  do
    n := n + 1

prove_algorithm increment by
  contract_solve []

ram method incrementTwice (mut n : Nat) return (result : Nat)
  ensures n = nOld + 2
  do
    n.incrementProcedure()
    n := n + 1

prove_algorithm incrementTwice by
  contract_solve []

/- A computed array value crosses the procedure boundary through a charged runtime slot. -/
ram method appendHead (capacity : Nat) (mut a : Array Nat) (mut buffer : List Nat)
    return (result : Array Nat × List Nat)
  require 0 < a.size
  require buffer.length < capacity
  ensures a = aOld
  ensures buffer = bufferOld ++ [aOld[0]! + 1]
  do
    let x := a[0]!
    buffer.append(capacity, x + 1)

prove_algorithm appendHead by
  contract_solve []

ram method addBoth (mut a : Nat) (mut b : Nat) return (result : Nat × Nat)
  ensures a = aOld + 1
  ensures b = bOld + 2
  do
    a := a + 1
    b := b + 2

prove_algorithm addBoth by
  contract_solve []

ram method callWithFrame (mut a : Nat) (mut buffer : List Nat) (mut b : Nat)
    return (result : Nat × List Nat × Nat)
  ensures a = aOld + 1
  ensures b = bOld + 2
  ensures buffer = []
  do
    (a, b) := addBothProcedure
    buffer.clear()

prove_algorithm callWithFrame by
  contract_solve []

end AlgoLib.Experimental.RAM.Prototype.Composition.MixedAlgorithms
