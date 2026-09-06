/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend
import AlgoLib.Experimental.RAM.Prototype.Composition.Buffer

/-!
# Paper-style owned buffer algorithms

Read this file before the implementation demo. `ram method` infers the straight-line
logical allowance and frames other mutable resources. `prove_algorithm` reasons only
through public procedure summaries. No body, address, compiler certificate, or private
potential appears in these proofs. `capacity` specializes the program before runtime;
`left` and `right` are its actual mutable inputs and outputs.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BufferAlgorithms
open Buffer.API
open Buffer (nonempty)

ram method recycle (capacity : Nat) (mut left : List Nat) (mut right : List Nat)
  return (result : List Nat × List Nat)
  require left.length + 2 ≤ capacity
  require right.length + 2 ≤ capacity
  ensures result = ([], [])
  do
    left.append(capacity, 7)
    left.append(capacity, 8)
    left.clear()
    right.append(capacity, 9)
    right.append(capacity, 10)
    right.clear()

prove_algorithm recycle by
  contract_vc
  omega

ram method clearLeft (mut left : List Nat) (mut right : List Nat)
  return (result : List Nat × List Nat)
  ensures left = []
  ensures right = rightOld
  credits 4
  do
    while left.nonempty
      invariant 1 ≤ remaining ∧ (left = [] ∨ 4 ≤ remaining)
      do
        if left.nonempty then
          left.clear()
        else
          left.clear()

prove_algorithm clearLeft by
  contract_vc
  grind [Buffer.nonempty]

end AlgoLib.Experimental.RAM.Prototype.Composition.BufferAlgorithms
