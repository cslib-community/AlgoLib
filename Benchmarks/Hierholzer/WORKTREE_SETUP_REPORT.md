# Hierholzer benchmark worktree setup report

## Frozen benchmark base

- `BENCHMARK_BASE`: `1b5c9f94e7cc660df254626555463ab8b2da791c`
- Subject: `Freeze Hierholzer Common benchmark infrastructure`
- Parent: `3a842eeb02c32af5ba6e45ba1a5ced7e9778bcfa`
- Local branches containing the base: `upstream-main`,
  `benchmark/hierholzer-graphlib`, and `benchmark/hierholzer-mathlib`
- Remote status: the base is local-only; `upstream-main` is one commit ahead of
  `origin/upstream-main`, and neither benchmark branch has an upstream

The base contains `HIERHOLZER_BENCHMARK_PROTOCOL.md`, the complete frozen Common tree, and a freeze
report ending in `COMMON_FREEZE_READY`.

## Worktrees

| Experiment | Branch | Worktree | HEAD |
| --- | --- | --- | --- |
| GraphLib | `benchmark/hierholzer-graphlib` | `/Users/yzll/GraphAlgorithms_hierholzer_graphlib` | `1b5c9f94e7cc660df254626555463ab8b2da791c` |
| Mathlib | `benchmark/hierholzer-mathlib` | `/Users/yzll/GraphAlgorithms_hierholzer_mathlib` | `1b5c9f94e7cc660df254626555463ab8b2da791c` |

Both tracked working trees are clean. Their only ignored setup path is their own `.lake/`. Neither
worktree contains a GraphLib-side or Mathlib-side Hierholzer experiment directory or implementation.

## Toolchain and dependencies

- Lean: `4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)
- Lake: `5.0.0-src+3dc1a08`
- Mathlib: `d802ffd29db1f5dc5a29206b1a8af62bfcc234a3` (clean in both worktrees)
- CSLib: `608cbe1b629a276abd3f2081f9b42dc766d8fd78` (clean in both worktrees)

The tracked `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are byte-identical in both
worktrees. Each worktree has a physically separate `.lake` tree and separate root build directory;
no writable build directory is shared.

## Frozen Common verification

- Manifest validation: passed for all four Lean files in both worktrees
- Manifest file SHA-256:
  `624489ddf4f8b69e31c434fdef1bab44a6447ace777670f9b62fae54020f1910`
- Cross-worktree source comparison: byte-identical
- `lake build Cslib.Algorithms.Lean.TimeM`: passed in both worktrees (457 jobs)
- Isolated clean-object compilation of Cost, Tour, umbrella, and Tests: passed in both worktrees
- Direct `lake env lean` elaboration of Cost, Tour, umbrella, and Tests: passed in both worktrees

## Final status

Both worktrees are ready for concurrent independent blind benchmark sessions.

`HIERHOLZER_WORKTREES_READY`
