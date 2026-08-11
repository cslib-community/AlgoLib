Remarks on the Current State of GraphLib

GraphLib is still under active development. Some parts of the library are incomplete, temporary, or in transition. When inferring GraphLib style, please distinguish established conventions from temporary implementation compromises.

In particular:

GraphLib/Graph/Degree.lean is currently incomplete. Unless the task explicitly concerns degree-related material, you may ignore this file when performing style audits, refactors, or consistency checks.

def neighborSet and noncomputable def degree of GraphLib/Theory/Structures/SimpleGraph_only/Girth.lean logically belong in GraphLib/Graph/Degree.lean. They are currently placed in Girth.lean only as a temporary workaround, because Degree.lean is being worked on by a collaborator.

Do not treat this placement as a style precedent. In particular, do not infer from this example that degree-related lemmas should live in Girth.lean, or that higher-level theory files should contain basic graph-degree API.

GraphLib/Theory/Structures/VertexSeq/CommonPrefix.lean contains no `VertexSeq` material at all: it declares `List.commonPrefix` and two `List` lemmas, and nothing else. It sits under `VertexSeq/` only because the library has no general-purpose List/utility module yet; `SimpleCycle` is currently its only client. This placement is a temporary workaround, not a style precedent — do not infer from it that `List` API belongs under `Structures/`, and do not re-file it until a utility module exists.

The `Snoc` class/notation is a collaborator legacy artifact. Unless a task explicitly concerns `Snoc`, ignore it during style audits, refactors, or consistency checks; do not propose namespacing or redesign changes for it.

The folder GraphAlgorithms is the old version of GraphLib, ignore it unless explicitly required by me.
