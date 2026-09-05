/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Runner
import AlgoLib.Experimental.RAM

/-!
# One fixed RAM sorting program

`sortCode` is a closed syntax tree, independent of the input length and values.
Its inputs are an existing memory block and the `base` and `count` registers.
All other registers can initially contain arbitrary words. The outer loop
visits the block from right to left; the inner loop inserts each saved word
into the sorted suffix using reads and writes.

The shallow functions from `RAM.lean` appear only as mathematical specifications
in the proof. Their cost fields are never used. Every cost bound here accompanies
an `Exec` derivation for the restricted language in `Machine.lean`.
-/

namespace AlgoLib.Experimental.RAM.Checked

open Reg

/-- The inner loop's run flag is an ordinary register. -/
def innerTest : Test := .lt (.lit 0) (.reg live)

/-- Move a smaller suffix element into the hole, then advance the hole. -/
def shift : List Instr :=
  [.store (.reg cursor) (.reg temp),
   .mov cursor (.reg next),
   .bin .add next (.reg next) (.lit 1)]

def stop : Code := .block [.mov live (.lit 0)]

def innerBody : Code :=
  .ite (.lt (.reg next) (.reg limit))
    (.seq (.block [.load temp (.reg next)])
      (.ite (.le (.reg key) (.reg temp)) stop (.block shift)))
    stop

/-- Insert the word in `key` into the suffix following the hole in `cursor`. -/
def insertCode : Code :=
  .seq (.while innerTest innerBody) (.block [.store (.reg cursor) (.reg key)])

def outerTest : Test := .lt (.lit 0) (.reg count)

/-- Prepare the insertion registers for the next outer iteration. -/
def prepare : List Instr :=
  [.bin .sub count (.reg count) (.lit 1),
   .bin .add cursor (.reg base) (.reg count),
   .load key (.reg cursor),
   .bin .add next (.reg cursor) (.lit 1),
   .mov live (.lit 1)]

def outerBody : Code := .seq (.block prepare) insertCode

/-- A single fixed program for every input length, base address, and memory. -/
def sortCode : Code :=
  .seq (.block [.bin .add limit (.reg base) (.reg count)])
    (.while outerTest outerBody)

/-- Simplify fixed straight-line instruction blocks inside proofs. -/
macro "ram_simp" : tactic =>
  `(tactic| simp [blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set])

/-- Stopping the inner loop and filling its hole. -/
private theorem stopped_exec (s : State) (hl : s.regs live = 0) :
    Exec insertCode s 2 (blockEval [.store (.reg cursor) (.reg key)] s) := by
  exact .seq (.whileFalse (by simp [innerTest, Test.eval, Operand.eval, hl]))
    (.block _ _)

/-- Insert a word with an actual execution derivation. Only the memory of the
shallow insertion is used; its freely writable cost annotation is irrelevant. -/
theorem insertCode_exec (n : Nat) (s : State)
    (hn : s.regs next = s.regs cursor + 1)
    (he : s.regs limit = s.regs cursor + n + 1)
    (hl : s.regs live = 1) :
    ∃ k t, Exec insertCode s k t ∧
      t.memory = (insert (s.regs cursor) (s.regs key) n s.memory).memory ∧
      t.regs base = s.regs base ∧ t.regs count = s.regs count ∧
      t.regs limit = s.regs limit ∧ k ≤ 7 * n + 5 := by
  induction n generalizing s with
  | zero =>
    let u := blockEval [.mov live (.lit 0)] s
    let t := blockEval [.store (.reg cursor) (.reg key)] u
    have hb : Exec innerBody s 2 u := by
      apply Exec.ifFalse (i := 1)
      · simp [Test.eval, Operand.eval, hn, he]
      · exact .block _ _
    have hu : u.regs live = 0 := by dsimp [u]; ram_simp
    have hx : Exec insertCode s 5 t :=
      Exec.while_seq_step (by simp [innerTest, Test.eval, Operand.eval, hl]) hb
        (stopped_exec u hu)
    refine ⟨5, t, hx, ?_, ?_, ?_, ?_, by omega⟩ <;>
      simp [t, u, blockEval, Instr.eval, Operand.eval, State.set]
  | succ n ih =>
    let u := blockEval [.load temp (.reg next)] s
    have huMem : u.memory = s.memory := rfl
    by_cases hsmall : s.regs key ≤ s.memory (s.regs cursor + 1)
    · let v := blockEval [.mov live (.lit 0)] u
      let t := blockEval [.store (.reg cursor) (.reg key)] v
      have hb : Exec innerBody s 4 v := by
        apply Exec.ifTrue (i := 3)
        · simp [Test.eval, Operand.eval]; omega
        · exact .seq (.block _ _) (.ifTrue
            (by simpa [u, blockEval, Instr.eval, Operand.eval, State.set, Test.eval, hn]
              using hsmall)
            (.block _ _))
      have hv : v.regs live = 0 := by dsimp [v]; ram_simp
      have hx : Exec insertCode s 7 t :=
        Exec.while_seq_step (by simp [innerTest, Test.eval, Operand.eval, hl]) hb
          (stopped_exec v hv)
      refine ⟨7, t, hx, ?_, ?_, ?_, ?_, by omega⟩
      · rw [insert_succ, if_pos hsmall]
        simp [t, v, u, blockEval, Instr.eval, Operand.eval, State.set]
      all_goals simp [t, v, u, blockEval, Instr.eval, Operand.eval, State.set]
    · let v := blockEval shift u
      have hvCursor : v.regs cursor = s.regs cursor + 1 := by
        simp [v, u, shift, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set, hn]
      have hvKey : v.regs key = s.regs key := by
        simp [v, u, shift, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set]
      have hvMem : v.memory = Function.update s.memory (s.regs cursor)
          (s.memory (s.regs cursor + 1)) := by
        simp [v, u, shift, blockEval, Instr.eval, Operand.eval, State.set, hn]
      have hvBase : v.regs base = s.regs base := by
        simp [v, u, shift, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set]
      have hvCount : v.regs count = s.regs count := by
        simp [v, u, shift, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set]
      have hvLimit : v.regs limit = s.regs limit := by
        simp [v, u, shift, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set]
      have hvNext : v.regs next = v.regs cursor + 1 := by
        simp [v, u, shift, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set]
      have hvLive : v.regs live = 1 := by
        simpa [v, u, shift, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set] using hl
      have hvEnd : v.regs limit = v.regs cursor + n + 1 := by omega
      obtain ⟨k, t, hx, hm, hb, hc, he', hk⟩ := ih v hvNext hvEnd hvLive
      have hbody : Exec innerBody s 6 v := by
        apply Exec.ifTrue (i := 5)
        · simp [Test.eval, Operand.eval]; omega
        · exact .seq (.block _ _) (.ifFalse
            (by simpa [u, blockEval, Instr.eval, Operand.eval, State.set, Test.eval, hn]
              using hsmall)
            (.block _ _))
      refine ⟨7 + k, t,
        Exec.while_seq_step (by simp [innerTest, Test.eval, Operand.eval, hl]) hbody hx,
        ?_, hb.trans hvBase, hc.trans hvCount, he'.trans hvLimit, by omega⟩
      rw [insert_succ, if_neg hsmall]
      simpa only [hvCursor, hvKey, hvMem] using hm

/-- Execute the last `n` outer iterations above `remaining`, leaving the loop
ready to continue there. The induction adds one iteration to the end of the
execution, mirroring the recursive list specification. -/
theorem outer_prefix (n remaining : Nat) (s : State)
    (hc : s.regs count = n + remaining)
    (he : s.regs limit = s.regs base + (n + remaining)) :
    ∃ k t, Prefix outerTest outerBody s k t ∧
      t.memory = (insertionSort (s.regs base + remaining) n s.memory).memory ∧
      t.regs base = s.regs base ∧ t.regs count = remaining ∧
      t.regs limit = s.regs limit ∧ k ≤ 4 * n ^ 2 + 8 * n := by
  induction n generalizing remaining s with
  | zero =>
    exact ⟨0, s, .refl s, rfl, rfl, by simpa using hc, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨k, u, hu, hm, hb, hcount, hend, hk⟩ :=
      ih (remaining + 1) s (by omega) (by omega)
    let v := blockEval prepare u
    have hvBase : v.regs base = s.regs base := by
      simpa [v, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set] using hb
    have hvCount : v.regs count = remaining := by
      simp [v, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set, hcount]
    have hvCursor : v.regs cursor = s.regs base + remaining := by
      simp [v, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set, hcount, hb]
    have hvKey : v.regs key = s.memory (s.regs base + remaining) := by
      simp only [v, prepare, blockEval, List.foldl_cons, List.foldl_nil, Instr.eval,
        Operand.eval, BinOp.eval, State.set]
      simp only [Function.update_of_ne (by decide : key ≠ live),
        Function.update_of_ne (by decide : key ≠ next), Function.update_self,
        Function.update_of_ne (by decide : base ≠ count), Function.update_self]
      rw [hcount, hb, Nat.add_sub_cancel, hm]
      exact insertionSort_frame _ _ _ _ (Or.inl (by omega))
    have hvMem : v.memory = u.memory := rfl
    have hvLimit : v.regs limit = s.regs limit := by
      simpa [v, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set] using hend
    have hvNext : v.regs next = v.regs cursor + 1 := by
      simp [v, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set]
    have hvLive : v.regs live = 1 := by
      simp [v, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set]
    obtain ⟨j, t, ht, htm, htb, htc, hte, hj⟩ :=
      insertCode_exec n v hvNext (by omega) hvLive
    have hbody : Exec outerBody u (5 + j) t := .seq (.block _ _) ht
    refine ⟨k + 1 + (5 + j), t,
      hu.snoc (by simp [outerTest, Test.eval, Operand.eval, hcount]) hbody,
      ?_, htb.trans hvBase, htc.trans hvCount, hte.trans hvLimit, ?_⟩
    · rw [insertionSort_succ]
      dsimp only
      rw [htm, hvCursor, hvKey, hvMem, hm]
      congr 3
    · nlinarith

/-- The same fixed program sorts every block and has a uniform quadratic bound.
Initialization of the limit register and the final loop test are included. -/
theorem sortCode_exec (s : State) :
    ∃ k t, Exec sortCode s k t ∧
      t.memory = (insertionSort (s.regs base) (s.regs count) s.memory).memory ∧
      k ≤ 4 * (s.regs count) ^ 2 + 8 * s.regs count + 2 := by
  let u := blockEval [.bin .add limit (.reg base) (.reg count)] s
  have hb : u.regs base = s.regs base := by dsimp [u]; ram_simp
  have hc : u.regs count = s.regs count := by dsimp [u]; ram_simp
  have he : u.regs limit = u.regs base + (s.regs count + 0) := by
    simp [u, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set]
  obtain ⟨k, t, ht, hm, _, hcount, _, hk⟩ := outer_prefix (s.regs count) 0 u (by omega) he
  refine ⟨1 + (k + 1), t,
    .seq (.block _ _) (ht.finish (by simp [outerTest, Test.eval, Operand.eval, hcount])),
    ?_, by omega⟩
  simpa [hb, u, blockEval, Instr.eval, Operand.eval, BinOp.eval, State.set] using hm


/-- A precise sorting specification with machine time. The input is exactly
the initial memory block, with its address and length held in two registers. -/
def SortsWithin (c : Code) (budget : Nat → Nat) : Prop :=
  ∀ s, ∃ k t, Exec c s k t ∧
    (contents t.memory (s.regs base) (s.regs count)).Pairwise (· ≤ ·) ∧
    (contents t.memory (s.regs base) (s.regs count)).Perm
      (contents s.memory (s.regs base) (s.regs count)) ∧
    (∀ a, a < s.regs base ∨ s.regs base + s.regs count ≤ a → t.memory a = s.memory a) ∧
    k ≤ budget (s.regs count)

/-- Correctness, memory preservation, termination, and time for one fixed program. -/
theorem sortCode_correct : SortsWithin sortCode (fun n => 4 * n ^ 2 + 8 * n + 2) := by
  intro s
  obtain ⟨k, t, hx, hm, hk⟩ := sortCode_exec s
  refine ⟨k, t, hx, ?_, ?_, ?_, hk⟩
  · rw [hm, insertionSort_contents]
    exact List.pairwise_insertionSort _ _
  · rw [hm, insertionSort_contents]
    exact List.perm_insertionSort _ _
  · intro a ha
    rw [hm]
    exact insertionSort_frame _ _ _ _ ha

/-- The program is quantified *before* all runtime inputs in `SortsWithin`. -/
theorem exists_quadratic_sort :
    ∃ c : Code, SortsWithin c (fun n => 4 * n ^ 2 + 8 * n + 2) :=
  ⟨sortCode, sortCode_correct⟩

/-- An explicit asymptotic witness: fourteen times `n²` for `n ≥ 1`. -/
theorem sortCode_quadratic (s : State) (hn : 1 ≤ s.regs count) :
    ∃ k t, Exec sortCode s k t ∧
      (contents t.memory (s.regs base) (s.regs count)).Pairwise (· ≤ ·) ∧
      (contents t.memory (s.regs base) (s.regs count)).Perm
        (contents s.memory (s.regs base) (s.regs count)) ∧
      k ≤ 14 * (s.regs count) ^ 2 := by
  obtain ⟨k, t, hx, hs, hp, _, hk⟩ := sortCode_correct s
  refine ⟨k, t, hx, hs, hp, ?_⟩
  have : s.regs count ≤ (s.regs count) ^ 2 := by nlinarith
  nlinarith

/-- Standard input state; constructing/loading it is outside the sorting cost. -/
def initial (m : Nat → Nat) (b n : Nat) : State where
  memory := m
  regs r := match r with
    | .base => b
    | .count => n
    | _ => 0

/-- The cost-erasure attack from the shallow prototype is impossible here:
no program can sort every input in zero machine operations. -/
theorem no_zero_time_sort : ¬ ∃ c : Code, SortsWithin c (fun _ => 0) := by
  rintro ⟨c, hc⟩
  let s := initial (ofList [2, 1]) 0 2
  obtain ⟨k, t, hx, hs, _, _, hk⟩ := hc s
  have hz : k = 0 := Nat.eq_zero_of_le_zero hk
  have ht : t = s := Exec.zero (hz ▸ hx)
  subst t
  norm_num [s, initial, contents, ofList] at hs

/-- Package the RAM program once; callers only supply the input state. -/
def sortProgram : TotalProgram where
  code := sortCode
  terminates s := by
    obtain ⟨k, t, hx, _, _⟩ := sortCode_exec s
    exact ⟨k, t, hx⟩

end AlgoLib.Experimental.RAM.Checked
