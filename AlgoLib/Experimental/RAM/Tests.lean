/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Demo

/-!
# Executable and verification regressions

Runtime tests execute the compiled, proof-erased evaluator without fuel.
Logical tests check that the verification layer rejects nondecreasing loops
and that the compiler/runner do not introduce a zero-time escape hatch.
-/

namespace AlgoLib.Experimental.RAM.Checked.Tests

open Source Reg

/-- A nondecreasing loop must not receive a termination certificate. -/
def badLoop : Stmt := imperative {
  while count > 0
    invariant (fun _ _ => True)
    decreases (fun s => s.regs count)
  {
    count := count;
  }
}

theorem badLoop_rejected (s : State) (hs : 0 < s.regs count) :
    ¬ VC badLoop (fun _ => True) s := by
  intro h
  have hb := h.2.1 s trivial (by simpa [Test.eval, Operand.eval] using hs)
  simp [VC, block, Simple.eval, Expr.eval, State.set, Operand.eval] at hb

/-- The total evaluator also respects the model's zero-step property. -/
theorem zero_run_preserves (p : TotalProgram) (s : State) (hz : (p.run s).1 = 0) :
    (p.run s).2 = s := Exec.zero (hz ▸ p.run_correct s)

-- Exact costs and boundary behavior, using the public fuel-free source API.
set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  let cases : List (List Nat × List Nat × Nat) :=
    [([], [], 2), ([7], [7], 13), ([3, 1, 4, 2], [1, 2, 3, 4], 71),
     ([1, 2, 3, 4], [1, 2, 3, 4], 52), ([4, 3, 2, 1], [1, 2, 3, 4], 88),
     ([3, 1, 3, 2], [1, 2, 3, 3], 71)]
  for (xs, expected, cost) in cases do
    let actual := Demo.sort xs
    unless actual == (expected, cost) do
      throw (IO.userError s!"sorting regression: {xs} produced {actual}")
  let (_, t) := Demo.insertionSort.run (initial (ofList [99, 88, 3, 1, 3, 2, 77]) 2 4)
  unless contents t.memory 0 7 == [99, 88, 1, 2, 3, 3, 77] do
    throw (IO.userError "nonzero-base or frame regression")
  for n in [0, 1, 5, 20] do
    let (steps, t) := Demo.summation.run (initial (ofList []) 0 n)
    unless 2 * t.regs key == n * (n + 1) && steps == 3 * n + 3 do
      throw (IO.userError s!"summation regression at {n}")

end AlgoLib.Experimental.RAM.Checked.Tests
