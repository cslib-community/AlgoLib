/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Library.Queue
import AlgoLib.Experimental.RAM.Library.Stack
import AlgoLib.Experimental.RAM.Library.Buffer
import AlgoLib.Experimental.RAM.Library.GraphCursor
import AlgoLib.Experimental.RAM.Library.Graph.GraphBridge

/-!
# Library: supported public entry point

Import this module for the documented library API. Layer-aligned exported
names are the preferred spelling for new clients; the original names remain valid
compatibility spellings. Exports refer to the same definitions and checked proofs,
not copied implementations. See Library/README.md and docs/PUBLIC-API.md.
-/

namespace AlgoLib.Experimental.RAM.Library.Queue
export AlgoLib.Experimental.RAM.Prototype.Composition.Queue.API (initializeQueue enqueue dequeue)
end AlgoLib.Experimental.RAM.Library.Queue

namespace AlgoLib.Experimental.RAM.Library.Queue
export AlgoLib.Experimental.RAM.Prototype.Composition.Queue (nonempty)
end AlgoLib.Experimental.RAM.Library.Queue

namespace AlgoLib.Experimental.RAM.Library.Stack
export AlgoLib.Experimental.RAM.Prototype.Composition.Stack.API (push clear)
end AlgoLib.Experimental.RAM.Library.Stack

namespace AlgoLib.Experimental.RAM.Library.Buffer
export AlgoLib.Experimental.RAM.Prototype.Composition.Buffer.API (append appendFrom clear)
end AlgoLib.Experimental.RAM.Library.Buffer

namespace AlgoLib.Experimental.RAM.Library.GraphCursor
export AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursor.API (neighbors nextNeighbor)
end AlgoLib.Experimental.RAM.Library.GraphCursor

namespace AlgoLib.Experimental.RAM.Library.Graph
export AlgoLib.Experimental.RAM.BFS (Adjacency Represents Reachable Connected)
end AlgoLib.Experimental.RAM.Library.Graph
