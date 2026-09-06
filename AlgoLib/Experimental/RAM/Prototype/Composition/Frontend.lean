/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Frontend.Method

/-!
# Owned mutable frontend: stable import

The implementation is split into Syntax, Resources, Expressions, Statements, and
Method. The public syntax, generated declarations, and `Frontend.declareMethod`
entry point are unchanged. Algorithm authors should import LogicalFrontend; these
modules organize the elaborator and do not introduce another language or semantics.
-/
