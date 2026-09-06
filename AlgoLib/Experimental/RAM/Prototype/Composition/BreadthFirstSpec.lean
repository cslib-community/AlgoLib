/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirstProgram

/-!
# Generated BreadthFirst obligation API

This module freezes the source propositions and caches routine proofs. The program
and backend can be imported without running this generation step. Student proofs
import this API; they do not regenerate it.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst

open Frontend BFSFacts

obligation_lemmas Frontier for "initialize" => [seed]
obligation_lemmas Frontier for "preserve" => [process_head]
obligation_lemmas Frontier for "exit" => [finish_bitmap]
obligation_lemmas work for "account" => [work_le_total, process_head, scan_work]
obligation_lemmas QueueOK for "preserve" => [queue_enqueue]

generate_obligations bfs

end AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
