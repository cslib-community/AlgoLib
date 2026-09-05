/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Demo

/-!
# Verified adjacency-list BFS on the RAM

See `BFS/README.md` for the paper-style walkthrough and `BFS/Demo.lean` for
fuel-free execution. `BFS.Input.correct` combines machine execution, exact
reachability, and a linear time bound; `BFS.Input.connected_iff` characterizes
connectedness using a single search.
-/
