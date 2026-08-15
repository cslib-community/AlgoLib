# GraphLib foundation status

**Updated:** 2026-08-15

**Current phase:** Phase 9 — `COMPLETE`

**Exit condition satisfied:** Yes

## Completed

- Added `Graph/Constructions.lean` with the selected Phase 9 constructors for all four graph types:
  empty and edgeless graphs, general graphs from bundled-edge or bundled-arc sets and singletons,
  simple single-edge or single-arc graphs, and simple complete graphs. Their API includes carrier,
  incidence, adjacency, equality, and finiteness simp lemmas and instances.
- Finalized declaration-free `Graph`, `Walk`, `Connectivity`, and `Weight` umbrellas. The root
  `GraphLib` imports exactly those stable foundation umbrellas, while `GraphLib.All` adds the stable
  data-structure and validated theory leaves.
- Added the root `GraphLibTest` umbrella and `Foundation/Constructions.lean`, including tests for
  generated endpoint carriers, reuse of bundled tags without identity loss, adjacency behavior,
  constructor equalities, and finite carriers.
- Removed 37 obsolete declaration-free theory forwarding modules and 10 stale empty algorithm or
  future-theory umbrellas. Mature walk, Girth, and Moore-bound modules remain at their canonical
  paths and compile through the final umbrellas.

## Deviations and deferred items

- No earlier-phase repair or Phase 9 API deviation was needed. The broader constructor catalog
  listed as deferred by the plan remains deferred.
- `DataStructures/InverseAckermann/Nivasch.lean` remains an unfinished research module with its two
  pre-existing `sorry` declarations and is explicitly outside the stable production surface;
  `GraphLib.All` includes the sorry-free `InverseAckermann.Basic` leaf only. The contraction-oriented
  `Theory/Minors/Basic.lean` placeholder and `DataStructures/UnionFind/Blueprint.lean` also remain
  outside that surface, as required by the plan.
- `Prototypes/RepresentationStress.lean` is a non-production research client of obsolete APIs. It
  was not migrated because the phase forbids unrelated research-file changes.
- Existing unrelated linter warnings remain. Phase 9 added no production `sorry`.

## Validation

- `lake build GraphLib GraphLib.All GraphLibTest GraphLibTest.ImportAll
  GraphLib.Walk.InSimpleGraph GraphLib.Walk.InSimpleDiGraph GraphLib.Theory.Girth
  GraphLib.Theory.MooreBound GraphLib.Graph.Basic GraphLib.Graph.Adjacency GraphLib.Graph.Finite
  GraphLib.Graph.Constructions GraphLib.Weight.Basic GraphLib.Weight.Walk GraphLib.Weight.Network`:
  success (1182 jobs).
- A direct `lake build` of all 76 stable production and test module targets succeeded (1182 jobs).
- Naming and scope searches found no forbidden legacy names, forwarding imports, implicit simple to
  general coercions, or contraction modules in the stable source and test surfaces. The stable
  production surface is free of `sorry`, and `git diff --check` passes.

## Next action

The nine-phase graph-foundation construction is complete. Keep future work on deferred research or
new algorithms separate from the stable umbrella surface unless it first satisfies production
quality and no-`sorry` requirements.
