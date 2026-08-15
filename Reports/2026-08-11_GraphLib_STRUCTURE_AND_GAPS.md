# GraphLib 文件结构、职责与基础缺口盘点

> 盘点日期：2026-08-11  
> 盘点范围：`GraphLib/`、根入口 `GraphLib.lean`、构建配置及直接相关的仓库说明。按仓库规则，不分析旧版 `GraphAlgorithms/`。

## 1. 结论摘要

GraphLib 当前更像一个“若干成熟主干 + 大量路线图占位 + 少数失效草稿”并存的开发仓库，而不是一个已经形成统一公共入口的 package。

最成熟的部分是：

- 四类基础图结构：无向/有向、一般/简单图；
- 邻接、诱导子图、有限简单图的 `Finset` 视图；
- 与图无关的 `VertexSeq`，以及 `SimpleWalk`、`SimplePath`、`SimpleCycle`；
- simple graph / simple digraph 中序列和游走的 realized-in API；
- 二分图、girth，以及 odd/even Moore bound；
- 标准 inverse Ackermann 函数及其 primitive recursive 证明。

最明显的短板不是单纯“文件为空”，而是以下四类问题叠加：

1. **公共导出链没有反映实际成果。** 根入口 `GraphLib.lean` 没有导出大部分已完成模块，包括 `Adjacency`、`Finite`、`VertexSeq`、walk/path/cycle、girth 和 Moore bound。
2. **默认构建不能覆盖全部源码。** `lake build` 成功，但三个未被入口引用的文件独立编译失败：`Graph/Degree.lean`、`Graph/Graphs.lean`、`Theory/Structures/Basic.lean`。
3. **核心算法区基本为空。** BFS/DFS、最短路、MST、flow、SCC 都只有说明性占位文件；Union–Find 是带 `sorry` 的大纲，不是完成实现。
4. **模块归属仍在过渡。** degree API 暂存在 `Girth.lean`，通用 `List.commonPrefix` 暂存在 `VertexSeq/`，二分图放在 `Structures/SimpleGraph_only/` 而正式 `Coloring/` 为空，tree/connectivity 也有重复或临时定义。

因此，下一阶段最值得优先做的不是继续横向增加高阶主题，而是先完成：**全源码可构建、统一入口、degree/有限可计算图 API、general/directed walk-path-cycle、connectivity，以及可复用的算法输入与正确性/复杂度框架。**

## 2. 盘点口径与验证结果

### 2.1 仓库与工具链

- package 名称与版本：`GraphLib 0.1.0`；
- Lean：`v4.30.0-rc2`；
- 主要依赖：Mathlib、CSlib、Batteries、checkdecls；
- `GraphLib/` 下共有 **61 个 `.lean` 文件、25 个目录、约 9,722 行 Lean 源码**；
- 没有发现独立的 `test/`、`tests/`、`example/` 或 `examples/` 目录。

### 2.2 实际构建状态

本次执行了以下检查：

- `lake build`：**成功**，但只覆盖 `GraphLib.lean` 的依赖闭包；构建日志仍显示 Union–Find blueprint 中有 9 个使用 `sorry` 的 declaration。
- 单独构建下列现有主干：**成功**：
  - `Graph.Adjacency`、`Graph.Finite`、`Graph.Subgraph`；
  - `Structures.InSimpleGraph`、`Structures.InSimpleDiGraph`；
  - `Structures.SimpleGraph_only.MooreBound`；
  - `InverseAckermann.Nivasch`（可构建，但有 2 个 `sorry`）；
  - `Walk`、`Forest`、`Tree`、`Eulerian`、`Hamiltonian`。
- 单独检查以下未接入模块：**失败**：
  - `Graph/Degree.lean`：有未完成 notation、缺失类型、7 处 `sorry` 等；
  - `Graph/Graphs.lean`：只有没有类型和定义体的 `def` 名称；
  - `Theory/Structures/Basic.lean`：旧草稿，包含互相冲突的表示方案、未知标识符和大量错误。

这意味着当前的“默认 build 绿色”不能解释为“`GraphLib/` 下所有文件都可用”。CI 中的 build job 也主要运行默认构建，因而同样可能漏掉孤立模块。

### 2.3 状态标记

后文使用以下状态：

| 标记 | 含义 |
|---|---|
| ✅ | 有实质实现，独立或经依赖链验证可构建 |
| 🟡 | 可构建，但只有早期定义、API 很薄或尚未接入公共入口 |
| 🟠 | 可构建的 WIP，仍含 `sorry`、fallback 或占位结论 |
| ⚪ | 仅注释/模块说明的占位文件 |
| ❌ | 当前独立编译失败，不能视为 package 的有效模块 |
| 📦 | umbrella/aggregator，本身原则上不定义内容 |

## 3. 当前实际架构

### 3.1 核心依赖主干

```text
Graph.Basic
├── Graph.Adjacency
│   ├── InSimpleGraph ── SimpleGraph-only: Bipartite ── Girth ── MooreBound
│   └── InSimpleDiGraph
├── Graph.Subgraph ────── realized-in 的 generated-subgraph / monotonicity API
└── Graph.Finite

VertexSeq
└── SimpleWalk
    └── SimplePath
        └── SimpleCycle

InverseAckermann.Basic
├── InverseAckermann.Nivasch
└── UnionFind.Blueprint
```

`InSimpleGraph` 是连接两个主干的桥：一边是 graph-agnostic 的序列/游走/路/圈，另一边是 `SimpleGraph.Adj` 和 `subgraphOf`。

### 3.2 根入口的实际问题

`GraphLib.lean` 当前直接导入：

- `Graph.Basic`；
- theory/algorithm 的若干 `Basic` 占位文件；
- `Matching.Basic`；
- `UnionFind.Blueprint`。

由此产生三个问题：

1. `import GraphLib` 后，用户拿不到大部分已经完成的 graph API；
2. blueprint 和高层空壳进入默认入口，成熟的 structures 反而不进入；
3. `Algorithms/GraphTraversal/Basic.lean` 连默认入口都未导入，而含义重复的 `Algorithms/Search/Basic.lean` 被导入。

此外，README 的 layout 仍写作 `GraphLib/Basic/`，实际目录已经是 `GraphLib/Graph/`，文档与源码结构不同步。

## 4. 逐目录、逐文件职责

### 4.1 根入口

| 文件 | 当前/预期职责 | 状态与备注 |
|---|---|---|
| `GraphLib.lean` | package 顶层公共入口，理应统一 re-export 稳定模块 | 📦 当前导出失衡：导出了多个空壳与 Union–Find blueprint，却漏掉大部分已完成模块 |

### 4.2 `GraphLib/Graph/`：基础图对象与低层 API

| 文件 | 当前/预期职责 | 状态与备注 |
|---|---|---|
| `Basic.lean` | 定义 `Edge`、`Arc`、`Graph`、`SimpleGraph`、`DiGraph`、`SimpleDiGraph`；提供 `V(G)`/`E(G)`、incidence、loopless 和 simple→general forgetful map | ✅ 真正的底座；四类图都显式携带 vertex/edge `Set` |
| `Adjacency.lean` | 为四类图定义 `Adj`；无向对称性、simple 类型的端点不等、邻接端点属于 vertex set | ✅ 内容集中且职责清楚，但未由根入口导出 |
| `Finite.lean` | 有限 `SimpleGraph`/`SimpleDiGraph` 的 vertex/edge `Finset`、可计算版本、边数上界和 finiteness 实例 | ✅ 已较完整；当前只覆盖 simple 类型。一般带标签图若只假设有限顶点并不能推出有限边，后续需明确额外假设/表示 |
| `Subgraph.lean` | 四类图的 `subgraphOf`、induced subgraph 以及 `G[S]` notation | ✅ 有基本定义；尚缺关系代数和大量 simp/mono API |
| `Degree.lean` | 预期统一承载 neighbor/incidence set/finset、degree、min/max/avg degree 及 notation | ❌ 当前不能编译；多个 `Finset` 仍是 `sorry`，部分名为 `*Finset` 的定义实际返回 `Set`，notation 没有右侧，`inc` 的类型未完成 |
| `Graphs.lean` | 预期定义常用图族与图运算：complete、cycle、path、star、wheel、grid、hypercube、Kneser、complete bipartite、Petersen、product、sum、complement、Cayley 等 | ❌ 只有 16 个无类型/无定义体的 `def` 名称，当前不是有效 Lean 模块 |

这一层尚未出现统一的空图/单点图、增删点边、图并交、relabel/map、directed reverse、simple/underlying graph 等基础构造 API。

### 4.3 `GraphLib/Theory/`：数学理论总目录

| 文件 | 当前/预期职责 | 状态与备注 |
|---|---|---|
| `Basic.lean` | 预期成为 theory umbrella，汇总 walks、trees、connectivity、spectral、matching、coloring、minors、embeddings | ⚪ 当前只有说明，没有任何 import；名为 aggregator 但并未 aggregate |
| `Matching/Basic.lean` | Matching、cover、augmenting path、Berge/Hall/König/Tutte 等理论入口 | 🟡 目前仅有一般 `Graph` 上的 `Matching` 结构及 `size`；其余明确留待未来 |
| `Coloring/Basic.lean` | 顶点/边 proper coloring、chromatic number 和基本上下界 | ⚪ 空；现有二分图 two-coloring 反而在 `Structures/SimpleGraph_only/Bipartite.lean` |
| `Connectivity/Basic.lean` | 连通分量、cuts、vertex/edge connectivity | ⚪ 明确声明尚未实现 |
| `Trees/Basic.lean` | tree/forest 主理论与 Cayley 定理入口 | ⚪ 空；另有 `Structures/Forest.lean` 和 `Structures/Tree.lean` 的早期定义，目录职责尚未统一 |
| `Spectral/Basic.lean` | Laplacian、Cheeger inequalities、expansion/expander | ⚪ 空 |
| `Minors/Basic.lean` | 点/边 contraction、minor、topological minor | ⚪ 空 |
| `Embeddings/Basic.lean` | graph embedding、planarity、Euler formula、Kuratowski、higher genus | ⚪ 空 |

### 4.4 `Theory/Structures/`：序列、游走、路、圈及其图内实现

#### 4.4.1 总体文件

| 文件 | 当前/预期职责 | 状态与备注 |
|---|---|---|
| `Basic.lean` | 看起来曾试图一次性定义 graph-agnostic walk/path/cycle | ❌ 742 行旧草稿；并列放了多套互斥表示、重复结构和 `sorry`，独立编译出现大量错误。实际新实现已拆到 `VertexSeq/*`、`SimpleWalk.lean` 等，应视为待清理的历史文件 |
| `VertexSeq.lean` | `VertexSeq/*` umbrella，只负责 re-export 九个子模块 | ✅📦 设计和依赖图写得清楚；下游应导入此文件 |
| `Walk.lean` | 带显式 edge label 的一般 `Walk α ε`；访问器、membership、map/fold、谓词、索引及生成 `Graph`/`DiGraph` | ✅ 内容很多，但它描述的是 edge-interleaved 数据；尚无“这些边确实属于某个图且端点一致”的 `InGraph` 层 |
| `SimpleWalk.lean` | `VertexSeq` + nonstalling；提升 append/glue/reverse/erase 等操作，并生成 simple graph/digraph | ✅ simple walk 的核心实现 |
| `SimplePath.lean` | `SimpleWalk` + nodup；构造、拼接、截取、反转等 | ✅ simple path 核心实现 |
| `SimpleCycle.lean` | 长度至少 3 的 closed simple walk，内部为 path；提供 closing、两路成圈、reroot/reverse 及 edge/arc 性质 | ✅ 实现较成熟，是后续 girth/Moore 的关键依赖 |
| `InSimpleGraph.lean` | simple graph realized-in umbrella | ✅📦 汇总四个子模块 |
| `InSimpleDiGraph.lean` | simple digraph 中 `VertexSeq`/`SimpleWalk` 的 realized-in、arc characterization、操作闭包与 subgraph bridge | ✅ 单文件实现较完整；尚没有专门的 directed path/cycle subtype |
| `InGraph.lean` | 预期连接一般 `Walk α ε` 与 `Graph α ε`，验证 edge membership、label 和 endpoints | ⚪ 仅版权头；这是 general multigraph 理论无法继续发展的关键空缺 |
| `Path.lean` | 预期定义一般带边 path | ⚪ 空 |
| `Trail.lean` | 预期定义不重复边的 trail | ⚪ 空；Eulerian 理论尤其需要它 |
| `Cycle.lean` | 预期定义一般带边 cycle | ⚪ 空 |
| `Forest.lean` | 目前定义 `SimpleGraph.Contains` 和无圈谓词 `IsForest` | 🟡 可构建但只有定义；与新 `IsSimpleWalkIn`/`IsAcyclic` API 重复，应统一后再扩展 |
| `Tree.lean` | 目前以 `IsForest ∧ IsConnected` 定义 tree，并在本文件临时定义 connected | 🟡 可构建但只有定义；connected 更应来自 `Theory/Connectivity`，且仍使用旧 `Contains` |
| `Eulerian.lean` | 一般图和 simple graph 的 Eulerian walk/circuit 谓词 | 🟡 只有定义，没有 Euler 判定定理、存在性、构造或与 trail 的系统连接 |
| `Hamiltonian.lean` | 一般图和 simple graph 的 Hamiltonian walk/cycle 谓词 | 🟡 只有定义，没有基本推论、充分条件或构造 API |

#### 4.4.2 `VertexSeq/`：与图无关的非空顶点序列

这一组是当前最清晰的内部子系统。`VertexSeq`、`SimpleWalk`、`SimplePath`、`SimpleCycle` 按仓库规则故意位于 root namespace，而不是 `GraphLib` namespace；这不是遗漏。

| 文件 | 职责 | 状态 |
|---|---|---|
| `Basic.lean` | `VertexSeq` carrier、`Snoc`、length/head/tail/toList、membership/subset、dropHead/dropTail | ✅ |
| `Predicates.lean` | `nodup`、`nonstalling`、`closed` 及 endpoint-drop 保持性 | ✅ |
| `Append.lean` | append、reverse 及长度/端点/结合律/保持性 | ✅ |
| `MapZip.lean` | map、foldl/foldr、zip、any/all、Functor 及保持性 | ✅；部分操作目前尚无库内 client |
| `Subseq.lean` | prefixUntil、suffixFrom、take/dropWhile、splitAt 及长度/包含/保持性 | ✅ |
| `Erase.lean` | loopErase、cycleErase，分别产出 nonstalling/nodup 序列 | ✅ |
| `Edges.lean` | 从序列提取无向 `edges : List (Sym2 α)` 和有向 `arcs : List (α × α)`，保留顺序与重数 | ✅ |
| `Index.lean` | `GetElem` 与 insert | ✅；insert 尚无 lemmas/client |
| `CommonPrefix.lean` | `List.commonPrefix` 和 splitting lemmas，用于两条路径分歧点 | ✅ 但完全不是 `VertexSeq` 内容；这是缺少通用 utility 模块导致的临时放置 |

#### 4.4.3 `InSimpleGraph/`：simple graph 内的 realized-in API

| 文件 | 职责 | 状态 |
|---|---|---|
| `VertexSeq.lean` | `SimpleGraph.IsVertexSeqIn`；构造刻画、vertex/edge membership、各序列操作闭包、`iff_edges` | ✅ |
| `Walk.lean` | `IsSimpleWalkIn`；提升 VertexSeq API，连接 `toSimpleGraph` 与 `subgraphOf` | ✅ |
| `Path.lean` | `IsSimplePathIn`；相邻新点延长 path，以及 path 长度不超过图顶点数 | ✅ |
| `Cycle.lean` | `IsSimpleCycleIn`、`HasSimpleCycle`、`IsAcyclic`；由 closing/two paths 造圈、长度界、subgraph 单调性 | ✅ |
| 上层 `InSimpleGraph.lean` | re-export 以上四层 | ✅📦 |

#### 4.4.4 `SimpleGraph_only/`：当前只针对 simple graph 的专项理论

| 文件 | 职责 | 状态与备注 |
|---|---|---|
| `Bipartite.lean` | proper Bool two-coloring、`IsBipartite`，证明 closed walk/cycle 长度为偶数 | ✅；理论上更接近 `Theory/Coloring` |
| `Girth.lean` | `girth : ℕ∞`、上下界刻画、acyclic 等价、最短圈达到、degree≥2 推出有圈、bipartite girth 偶性 | ✅；暂时重复定义 `SimpleGraph.neighborSet`/`degree`，待迁入修好的 `Graph/Degree.lean` |
| `MooreBound.lean` | Moore bound umbrella | ✅📦 |
| `MooreBound/Counting.lean` | 两个与图无关的有限集合计数 lemma | ✅；属于可复用通用工具，未必应长期放在 graph theory 子目录 |
| `MooreBound/Core.lean` | fresh neighbors、短圈矛盾、rooted/half layer 共用核心 lemma | ✅；文件开头还有 3 个临时 degree helper，最终应迁到 `Graph/Degree.lean` |
| `MooreBound/RootedLayers.lean` | 从单个 root 生长的 BFS-like layers，用于 odd-girth bound | ✅ |
| `MooreBound/HalfLayers.lean` | 围绕中心边两端的 avoiding rooted layers，用于 even-girth bound | ✅ |
| `MooreBound/Bounds.lean` | 最终的 odd/even Moore bound 定理 | ✅ |

Moore bound 是目前仓库里最接近“定义—辅助层—主定理”完整闭环的高层理论模块。

### 4.5 `GraphLib/Algorithms/`：算法及正确性/复杂度证明

| 文件 | 预期职责 | 状态与备注 |
|---|---|---|
| `Basic.lean` | algorithms umbrella | ⚪ 只有说明，没有 import |
| `GraphTraversal/Basic.lean` | BFS、DFS | ⚪ 空，且未被 `GraphLib.lean` 导入 |
| `Search/Basic.lean` | BFS、DFS | ⚪ 与 `GraphTraversal` 职责重复；应先决定保留哪个模块名 |
| `ShortestPath/Basic.lean` | Dijkstra、Bellman–Ford、Floyd–Warshall | ⚪ 空 |
| `MST/Basic.lean` | Kruskal、Prim、Borůvka | ⚪ 空 |
| `Flow/Basic.lean` | Ford–Fulkerson、Edmonds–Karp、Push–Relabel、near-linear max flow | ⚪ 空 |
| `SCC/Basic.lean` | Tarjan、Kosaraju | ⚪ 空 |

算法部分的根本障碍不只是算法文件为空：当前 graph 表示以 `Set` 为主，尚无统一的**有限可执行表示、邻接枚举接口、权重/容量层、算法状态不变量、返回证书和成本模型**。这些基础如果不先定下来，各算法容易各自发明一套输入和复杂度语义。

### 4.6 `GraphLib/DataStructures/`：算法支撑数据结构

| 文件 | 当前/预期职责 | 状态与备注 |
|---|---|---|
| `InverseAckermann/Basic.lean` | Mathlib Ackermann 对角线、标准 inverse Ackermann、截断可计算版本及 primitive recursive 证明 | ✅ 完成度高；不是 graph theory 本体，但为 Union–Find 复杂度服务 |
| `InverseAckermann/Nivasch.lean` | 不直接引用 Ackermann 的 Nivasch hierarchy 与 inverse 定义，并与标准版本比较 | 🟠 定义可构建；bounded search 可能 fallback 到 0，两个关键比较定理仍为 `sorry` |
| `UnionFind/Blueprint.lean` | 基于 Batteries 的 Union–Find 正确性、rank invariant、potential、amortized complexity 全路线图 | 🟠 846 行 blueprint；部分基础正确性已有证明，但 rank/potential/complexity 仍有多个 `sorry`，最终总成本定理目前只是 `True` |

Union–Find 既是通用数据结构，又是 Kruskal 等图算法的基础，因此放在 `DataStructures/` 合理；但 `Blueprint.lean` 不宜作为顶层 `import GraphLib` 默认暴露的稳定 API。

## 5. “和 graph 无关”的内容及建议归属

| 内容 | 当前原因 | 建议 |
|---|---|---|
| `InverseAckermann/*` | Union–Find amortized complexity | 保留在 `DataStructures/`，但与 graph theory 导出层解耦 |
| `UnionFind/Blueprint.lean` | MST 等算法会使用 | 保留为开发模块；完成后拆成 `Basic`、`Correctness`、`RankBounds`、`Potential`、`Complexity`，blueprint 不进稳定入口 |
| `List.commonPrefix` | `SimpleCycle.ofTwoPaths` 的工具 | 新建通用 `GraphLib/Util/List.lean` 或类似模块后迁移 |
| Moore bound 的两个 `Set` 计数 lemmas | 高层证明首先需要 | 若出现第二个 client，迁到 `GraphLib/Util/Set/Card.lean`；在此之前可暂留并明确 internal |
| legacy `Snoc` class | 早期协作者遗留，当前 sequence notation 使用 | 按仓库规则不做无关重构；只需避免继续扩散 |
| 三个 `.DS_Store` | macOS 元数据 | 从源码树删除并确保 `.gitignore` 覆盖 |

这里需要区分“与图无关但为图算法服务的通用基础”与“无意进入仓库的杂项”。前四类可以保留，只需建立更清晰的 utility/data-structure 边界；`.DS_Store` 则应清理。

## 6. 当前缺失的基础能力

以下按依赖阻塞程度排序，而不是按主题吸引力排序。

### P0：先让 package 边界可信

1. **建立真正的 umbrella 导出链。**
   - `Theory/Basic.lean`、`Algorithms/Basic.lean` 要么真正 import 子模块，要么改名避免假装 aggregator；
   - 新建/整理 `Graph/Basic` 以上的 graph umbrella；
   - `GraphLib.lean` 只导出相对稳定、可构建的 API；
   - blueprint/WIP 模块不应混入默认入口。

2. **让 CI 覆盖全部 `.lean` 文件。**
   - 当前至少三个源码文件在默认 build 之外失败；
   - 可增加一个 import-all 检查目标，或显式构建所有 library modules；
   - 将“允许 `sorry` 的开发模块”和“稳定无 `sorry` 的模块”分层检查。

3. **处置失效草稿。**
   - `Theory/Structures/Basic.lean` 与新架构重复，建议删除、移入明确的 archive，或彻底改成 umbrella；
   - `Graph/Graphs.lean` 应在第一个有效构造实现前不要放无定义体的 `def`；
   - `Graph/Degree.lean` 是应优先修复的活跃文件，而不是简单删除。

4. **补最小测试与使用示例。**
   - 至少加入 construction、adjacency、induced subgraph、walk realization、girth/Moore bound 的 compile-time examples；
   - 对 executable algorithm 则需要小图上的 `#eval`/回归测试与 theorem-level correctness 测试。

### P1：图论与算法都会依赖的低层基础

1. **完成并统一 degree API。**
   - 修复四类图的 neighbor/incidence set/finset；
   - 明确有限性/decidability 参数；
   - 完成 degree、in/out degree、min/max/average degree 与 notation；
   - 加入 handshake lemma、degree sum、邻接与 neighbor membership 的 simp API；
   - 将 `Girth.lean` 和 `MooreBound/Core.lean` 中的临时定义/lemmas 迁回。

2. **补标准图构造和图运算。**
   - empty、singleton、complete、path、cycle、star、complete bipartite；
   - add/delete vertex/edge、union/intersection、complement；
   - relabel/map、directed reverse、underlying/forgetful conversions；
   - 每项都应带 `V`/`E`/`Adj` 的 simp lemmas，而不只是一个 constructor。

3. **扩充 subgraph API。**
   - `refl`、`trans`、必要的 antisymmetry/extensionality；
   - induced subgraph 的 vertex/edge membership、幂等性、嵌套/单调性；
   - spanning subgraph、edge-induced subgraph，以及 embeddings/minors 需要的 maps。

4. **建立有限可计算图接口。**
   - 区分数学 `Set` 模型与 executable representation；
   - 统一 vertex enumeration、out-neighbor enumeration、edge lookup 的接口；
   - 给出 mathematical graph 与 executable graph 之间的 refinement/correctness bridge；
   - 这是 BFS、Dijkstra、SCC、MST、flow 真正可实现和谈复杂度的前提。

5. **补权重、容量与成本模型。**
   - weighted edges、nonnegative weights、capacity/flow network；
   - algorithm output certificate 与 correctness predicate；
   - 明确运行时间按何种操作/数据结构计数，避免只证明功能正确但无法陈述复杂度。

### P1：补齐 walk/path/cycle 与 connectivity 主干

1. **一般图的 realized-in 层。** 完成 `InGraph.lean`，验证 `Walk α ε` 中的每个 edge label 属于图且 endpoints 与相邻 vertices 一致；随后才能可靠定义一般 graph 的 path/trail/cycle。
2. **实现 `Path.lean`、`Trail.lean`、`Cycle.lean`。** 当前 simple graph 路线较完整，但 multigraph/Eulerian 所需的 edge-distinct trail 仍缺失。
3. **完成 directed path/cycle。** `InSimpleDiGraph` 已有不错的序列层，但没有专门的 `SimpleDiPath`/`SimpleDiCycle` 或等价 bundled API。
4. **实现 connectivity 核心。** reachability、connected、components、component quotient、cuts、bridges、articulation vertices、vertex/edge connectivity。
5. **统一 forest/tree。** 用 `IsAcyclic` 和正式 connectivity API 重写当前 `Contains`/`IsForest`/`IsConnected` 临时定义，并补基本等价刻画（唯一路、`|E|=|V|-1`、删边断开等）。

### P2：在基础稳定后展开的主题

1. **算法：** 先统一 `Search` 与 `GraphTraversal` 命名，再依次实现 BFS/DFS → SCC/shortest path → MST → flow；每个算法包括规范、实现、正确性、终止性与成本。
2. **Union–Find：** 将 blueprint 拆文件、消除 `sorry`、给出非占位总成本定理，然后供 Kruskal 使用。
3. **Matching：** 先补 matching membership/maximal/maximum/perfect、augmenting path 和 augment 操作，再进入 Berge、Hall、König。
4. **Coloring：** 将二分图 API 与正式 coloring hierarchy 对齐，再补 chromatic number、greedy bounds、edge coloring。
5. **Eulerian/Hamiltonian：** 从“只有谓词”推进到基本 characterization 与构造定理。
6. **Minors/Embeddings/Spectral：** 这些依赖更多图 maps、contraction、linear algebra 与 finiteness 基础，适合后置。

## 7. 建议的近期落地顺序

一个风险较低、能快速改善 package 可用性的顺序是：

1. 修 CI/import-all，并清理三个编译失败的孤立草稿；
2. 重做 `GraphLib.lean` 与各层 umbrella，使现有成熟模块可被正常导入；
3. 完成 `Graph/Degree.lean`，迁回 girth/Moore 中的临时代码；
4. 补 empty/singleton/complete/path/cycle 等标准构造和基础 subgraph lemmas；
5. 建 executable finite graph interface；
6. 完成 `InGraph` + general path/trail/cycle；
7. 完成 connectivity，并统一 forest/tree；
8. 以 BFS/DFS 作为第一个端到端算法，验证“输入表示—实现—正确性—复杂度”整条路线；
9. 在同一框架上推进 SCC、shortest path、MST，并同步收敛 Union–Find。

## 8. 总体评价

GraphLib 已经有一条质量不错的理论纵线：

```text
VertexSeq → SimpleWalk → SimplePath → SimpleCycle
          → realized in SimpleGraph → girth → Moore bound
```

这条纵线说明核心设计并非停留在概念阶段，尤其 umbrella 拆分、graph-agnostic sequence 与 realized-in predicate 的分层是合理的。当前主要问题是这条成熟纵线没有成为 package 的公共主干，同时周围还保留了旧草稿、空路线图和尚未统一的模块归属。

若先把“所有文件可构建、入口真实、degree/finite-computable/connectivity 主干齐全”做好，再扩展算法与高阶理论，GraphLib 会从“多个局部成果的施工现场”较快收敛为一个可持续扩展的 graph package。
