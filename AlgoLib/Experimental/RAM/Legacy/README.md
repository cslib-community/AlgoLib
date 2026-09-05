# Earlier demonstrations, explicitly opt-in

The files here preserve the earlier typed-source demonstrations and their regression coverage. They are not imported by `AlgoLib.Experimental.RAM`, and they are not the canonical sorting or BFS files.

Use [Programs/Sorting.lean](../Programs/Sorting.lean) and [Programs/Connectivity.lean](../Programs/Connectivity.lean) for the current method/VC workflow. Import `Legacy.InsertionSort`, `Legacy.BFS`, or `Legacy.LanguageExamples` explicitly only when comparing older refinement-based demonstrations. Their Lean namespace is `AlgoLib.Experimental.RAM.Legacy`.

The actual reusable low-level proofs needed by the new public library are in `Backend/Certificates`; legacy demos are not dependencies of the new programs.
