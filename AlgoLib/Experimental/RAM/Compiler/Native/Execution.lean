/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Compiler.Native.Compiler

/-!
# Executing certified native programs

An independent source termination proof supplies the target runner's certificate.
Execution needs no fuel and does not evaluate the source semantics at runtime.
`run_eq` transports any source result and exact native cost to the executable.
This is the backend interface; logical credit contracts are supplied by the
ownership and refinement layer above it.
-/
namespace AlgoLib.Experimental.RAM.Native

/-- Source termination transports through the native compiler. -/
theorem terminates (c : Cmd) (s : Store) (h : ∃ k t, Eval c s k t) :
    Integer.Terminates c.compile (encode s) := by
  obtain ⟨k, t, he⟩ := h
  obtain ⟨u, hx, _⟩ := he.compile (encode s) (observe_encode s)
  exact ⟨k, u, hx⟩

/-- Run actual compiled Int-RAM and observe its store. -/
def run (c : Cmd) (s : Store) (h : ∃ k t, Eval c s k t) : Nat × Store :=
  let result := Integer.run c.compile (encode s) (terminates c s h)
  (result.1, observe result.2)

theorem run_eq {c : Cmd} {s t : Store} {k : Nat} (he : Eval c s k t)
    (h : ∃ j u, Eval c s j u) : run c s h = (k, t) := by
  obtain ⟨u, hx, ho⟩ := he.compile (encode s) (observe_encode s)
  simp only [run, Integer.run_eq hx, ho]

/-- A backend method packages source termination once for all valid inputs. -/
structure Method (Input : Type*) where
  body : Cmd
  input : Input → Store
  terminates : ∀ x, ∃ k t, Eval body (input x) k t

def Method.run {I : Type*} (p : Method I) (x : I) : Nat × Store :=
  Native.run p.body (p.input x) (p.terminates x)

theorem Method.run_eq {I : Type*} (p : Method I) (x : I) {k : Nat} {t : Store}
    (h : Eval p.body (p.input x) k t) : p.run x = (k, t) := Native.run_eq h _

end AlgoLib.Experimental.RAM.Native
