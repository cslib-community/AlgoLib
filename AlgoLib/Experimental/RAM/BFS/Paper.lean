/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Program
import AlgoLib.Experimental.RAM.Interface

/-!
# A paper-language frontend for adjacency-list traversals

This is a small domain-specific language with one bitmap and one FIFO. Its
compositional lowering expands traversal operations into the existing source
language. Seeding and mark-before-enqueue are fused operations: the syntax
checks both statements and their bindings before constructing those nodes.
Unsupported statements or mismatched names are errors, never ignored text.
-/
namespace AlgoLib.Experimental.RAM.BFS.Paper
open Checked Checked.Source Lean

/-- Structured traversal operations. All computation lowers to RAM syntax. -/
inductive Plan where
  | clear
  | seed
  | pop
  | discover
  | neighbors (body : Plan)
  | queueLoop (body : Plan)
  | seq (first second : Plan)
  | skip
  deriving Repr

/-- Group adjacent source instructions without changing their order. -/
private def prepend (is : List Simple) : Stmt → Stmt
  | .block js => .block (is ++ js)
  | .seq (.block js) rest => .seq (.block (is ++ js)) rest
  | rest => .seq (.block is) rest

private def attach (p : Stmt) : Stmt → Stmt
  | .block [] => p
  | rest => .seq p rest

/-- Continuation-based lowering keeps sequential instructions in one block.
The iterator introduces its own address calculations and cursor advancement. -/
def Plan.lower : Plan → Stmt → Stmt
  | .skip, rest => rest
  | .seq a b, rest => a.lower (b.lower rest)
  | .clear, rest => prepend [.assign head (.atom (.lit 0))]
      (attach (.loop clearTest (fun _ _ => True) (fun _ => 0) clearBody) rest)
  | .seed, rest => match BFS.seed with
      | .block is => prepend is rest
      | p => attach p rest
  | .pop, rest => prepend [
      .assign addr (.bin .mul (.lit 5) (.reg head)),
      .assign addr (.bin .add (.reg addr) (.lit 2)),
      .assign vertex (.load (.reg addr)),
      .assign head (.bin .add (.reg head) (.lit 1))] rest
  | .neighbors body, rest => prepend [
      .assign addr (.bin .mul (.lit 5) (.reg vertex)),
      .assign ptr (.load (.reg addr))]
      (attach (.loop scanTest (fun _ _ => True) (fun _ => 0)
        (prepend [
          .assign addr (.bin .mul (.lit 5) (.reg ptr)),
          .assign addr (.bin .add (.reg addr) (.lit 3)),
          .assign neighbor (.load (.reg addr))]
          (body.lower (.block [
            .assign addr (.bin .mul (.lit 5) (.reg ptr)),
            .assign addr (.bin .add (.reg addr) (.lit 4)),
            .assign ptr (.load (.reg addr))])))) rest)
  | .discover, rest => prepend [
      .assign addr (.bin .mul (.lit 5) (.reg neighbor)),
      .assign addr (.bin .add (.reg addr) (.lit 1)),
      .assign marked (.load (.reg addr))]
      (attach (.ite (.eq (.reg marked) (.lit 0)) (.block [
        .store (.reg addr) (.lit 1),
        .assign addr (.bin .mul (.lit 5) (.reg tail)),
        .assign addr (.bin .add (.reg addr) (.lit 2)),
        .store (.reg addr) (.reg neighbor),
        .assign tail (.bin .add (.reg tail) (.lit 1))]) (.block [])) rest)
  | .queueLoop body, rest =>
      attach (.loop bfsTest (fun _ _ => True) (fun _ => 0) (body.lower (.block []))) rest

structure Program where
  verticesName : String
  adjacencyName : String
  sourceName : String
  outputName : String
  body : Plan

def Program.source (p : Program) : Stmt := p.body.lower (.block [])
def Program.compile (p : Program) : Code := p.source.compile
/-- `return visited` exposes the output region; it does not enumerate it. -/
def Program.output (_ : Program) : Output Bitmap := .bitmap size 5 1

/-- Lowered source and RAM executions agree in state and exact time. -/
theorem Program.compile_correct (p : Program) (s t : State) (k : Nat) :
    Eval p.source s k t ↔ Exec p.compile s k t := ⟨Eval.compile, Eval.of_compile⟩

declare_syntax_cat graphStmt
syntax "for " ident " in " ident " {" graphStmt* "}" : graphStmt
syntax "for " ident " in " ident "[" ident "]" " {" graphStmt* "}" : graphStmt
syntax ident "[" ident "]" " := " ident ";" : graphStmt
syntax ident " := " "[" ident "]" ";" : graphStmt
syntax "while " ident " is " "not " "empty " "{" graphStmt* "}" : graphStmt
syntax ident " := " "dequeue(" ident ")" ";" : graphStmt
syntax "if " "not " ident "[" ident "]" " {" graphStmt* "}" : graphStmt
syntax "enqueue(" ident "," ident ")" ";" : graphStmt
syntax "return " ident ";" : graphStmt

private def same (a b : TSyntax `ident) : MacroM Unit :=
  unless a.getId == b.getId do
    Macro.throwErrorAt a s!"expected `{b.getId}`, found `{a.getId}`"

private def fresh (name : TSyntax `ident) (bound : Array (TSyntax `ident)) : MacroM Unit := do
  for b in bound do
    if name.getId == b.getId then
      Macro.throwErrorAt name s!"name `{name.getId}` is already bound"

private def planSeq (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  xs.foldrM (fun x rest => `(Plan.seq $x $rest)) (← `(Plan.skip))

/-- Parse the neighbor body as mark-before-enqueue, validating all references. -/
private def neighborPlan (ss : Array (TSyntax `graphStmt)) (flags v queue : TSyntax `ident) :
    MacroM (TSyntax `term) := do
  let mut result := #[]
  for stmt in ss do
    match stmt with
    | `(graphStmt| if not $f:ident[$x:ident] {
        $f':ident[$x':ident] := true; enqueue($q:ident, $y:ident);
      }) =>
      same f flags; same x v; same f' flags; same x' v; same q queue; same y v
      result := result.push (← `(Plan.discover))
    | other =>
      Macro.throwErrorAt other "expected `if not visited[v] { visited[v] := true; enqueue(Q, v); }`"
  planSeq result

private def queuePlan (ss : Array (TSyntax `graphStmt))
    (adj flags queue : TSyntax `ident) : MacroM (TSyntax `term) := do
  let mut current : Option (TSyntax `ident) := none
  let mut result := #[]
  for stmt in ss do
    match stmt with
    | `(graphStmt| $u:ident := dequeue($q:ident);) =>
      same q queue
      fresh u #[adj, flags, queue]
      current := some u
      result := result.push (← `(Plan.pop))
    | `(graphStmt| for $v:ident in $a:ident[$u:ident] { $body:graphStmt* }) =>
      same a adj
      fresh v #[adj, flags, queue]
      match current with
      | none => Macro.throwErrorAt u "dequeue a vertex before traversing its adjacency list"
      | some bound => same u bound
      result := result.push (← `(Plan.neighbors $(← neighborPlan body flags v queue)))
    | other => Macro.throwErrorAt other "expected dequeue or adjacency traversal"
  planSeq result

syntax "graph_program " "(" ident "," ident "," ident ")"
  " returns " ident " {" graphStmt* "}" : term

macro_rules
  | `(graph_program ($vertices:ident, $adj:ident, $source:ident) returns $flags:ident {
      $ss:graphStmt*
    }) => do
    fresh adj #[vertices]
    fresh source #[vertices, adj]
    fresh flags #[vertices, adj, source]
    let mut result := #[]
    let mut queue : Option (TSyntax `ident) := none
    let mut i := 0
    let mut returned := false
    while i < ss.size do
      match ss[i]! with
      | `(graphStmt| for $v:ident in $vs:ident { $f:ident[$x:ident] := false; }) =>
        if queue.isSome then Macro.throwErrorAt ss[i]! "initialize before seeding the queue"
        fresh v #[vertices, adj, source, flags]
        same vs vertices; same f flags; same x v
        result := result.push (← `(Plan.clear))
      | `(graphStmt| $f:ident[$s:ident] := true;) =>
        same f flags; same s source
        if queue.isSome then Macro.throwErrorAt ss[i]! "the source can only seed the queue once"
        if i + 1 ≥ ss.size then Macro.throwErrorAt ss[i]! "expected `Q := [s];`"
        match ss[i + 1]! with
        | `(graphStmt| $q:ident := [$s':ident];) =>
          same s' source
          fresh q #[vertices, adj, source, flags]
          queue := some q
          result := result.push (← `(Plan.seed))
          i := i + 1
        | other => Macro.throwErrorAt other "expected `Q := [s];` after marking the source"
      | `(graphStmt| while $q:ident is not empty { $body:graphStmt* }) =>
        match queue with
        | none => Macro.throwErrorAt q "initialize the queue before using it"
        | some bound =>
          same q bound
          result := result.push (← `(Plan.queueLoop $(← queuePlan body adj flags q)))
      | `(graphStmt| return $f:ident;) =>
        same f flags
        if i + 1 != ss.size then Macro.throwErrorAt ss[i]! "return must be the last statement"
        returned := true
      | other => Macro.throwErrorAt other "unsupported graph statement in this scope"
      i := i + 1
    unless returned do Macro.throwError "expected an explicit `return visited;`"
    `(Program.mk $(quote vertices.getId.toString) $(quote adj.getId.toString)
      $(quote source.getId.toString) $(quote flags.getId.toString) $(← planSeq result))

/-- Actual syntax: input names, a returned value, and the textbook BFS body. -/
def bfs : Program := graph_program (V, adjacency, s) returns visited {
  for v in V { visited[v] := false; }
  visited[s] := true;
  Q := [s];
  while Q is not empty {
    u := dequeue(Q);
    for v in adjacency[u] {
      if not visited[v] {
        visited[v] := true;
        enqueue(Q, v);
      }
    }
  }
  return visited;
}

/-- The paper program is exactly the previously verified RAM algorithm. -/
theorem bfs_compiles : bfs.compile = bfsCode := rfl

end AlgoLib.Experimental.RAM.BFS.Paper
