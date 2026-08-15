# GraphLib 初始架构与 API 设计提案

> 日期：2026-08-14  
> 性质：架构蓝图，不包含 Lean 实现  
> 依据：项目锁定的 Mathlib `d802ffd29db1f5dc5a29206b1a8af62bfcc234a3`、当前 GraphLib 源码及其真实下游用法、代表性 TCS 算法场景、截至 2026-08-13 的 Mathlib master 与公开实验性设计。

## 执行摘要

建议把 GraphLib 建成一个“**两种常用简单图 + 两种保留边身份的一般图**”的 TCS 图基础库，而不是追求四种图的形式对称：

- `SimpleGraph` 与 `SimpleDiGraph` 是大多数图论、BFS/DFS、可达性、SCC 和不涉及平行边身份的算法的首选对象。
- `Graph` 与 `DiGraph` 是需要 loop、平行边、逐边权重、MST 选边、容量、费用、残量边或 Euler trail 时的身份敏感对象；它们的底层 API 必须可靠，但不必复制所有 simple-graph 理论。
- 保留并扩展当前已经被 girth/Moore bound 验证的架构：`VertexSeq`、`SimpleWalk`、`SimplePath`、`SimpleCycle` 是图无关数据，`G.Is…In` 单独表达这些数据在图中被实现。
- 立即修正一般图的边语义：类型参数 `ε` 应是**实际边身份**，`E(G) : Set ε` 必须保留身份。端点集合不能再冒充 `E(G)`。一般无向图公开 `IsLink/Inc/Adj`，一般有向图公开 `IsArc/Inc/Adj`。
- induced subgraph、删点和删边保持 ambient 顶点/边类型不变；relabel、contraction、vertex splitting 才是明确的 type-changing 操作，并应带显式映射和运输定理。
- 权重、费用和容量是附着在已有边身份上的独立数据，不进入图结构，也不产生 `WeightedGraph`、`CapacitatedDiGraph` 等组合爆炸。
- 数学有限性与可执行表示分层。`Set` 图提供定理语义；算法依赖一个可计算的有限邻接/边枚举视图及其 refinement 定理，不假装从 `[Finite V(G)]` 就能执行。
- 当前不引入统一四图的公开 `GraphLike` 层。Mathlib 的相关提案尚未合并且存在竞争方案；GraphLib 只共享真正稳定的小接口和命名。

这套方案有一个有意的 breaking change：重做一般 `Graph/DiGraph` 的边表示。现在做的迁移成本远低于在 flow、MST 和 general walk 落地后再修复。

---

## 1. 设计目标

### 1.1 目标

1. **以 TCS 算法证明为中心。** API 应自然表达 BFS/DFS、可达性、SCC、最短路、MST、flow/cut、删点删边、收缩和动态变换，而不只服务静态图论定理。
2. **纸面图论接近 Lean 表达。** 常见陈述使用 ambient `α`、`V(G)`、`E(G)`、`G.Adj u v`、`G.deleteVerts S`，避免把每个顶点都包装为 `V(G)` subtype。
3. **边身份不丢失。** 一般图中平行边必须可以被分别删除、赋权、放入路径、选入树或承载流。
4. **组合对象可独立操纵。** 路径的 reverse、prefix、suffix、erase、map 等操作不应因换图或换子图产生大量 endpoint cast。
5. **同 ambient 类型的局部变换保持同类型。** induced、spanning restriction、删点、删边及反复动态更新都返回原图类型参数。
6. **有限数学与可执行算法有清楚桥梁。** 数学层不被数组/哈希表表示污染；执行层又不依赖 classical choice 生成的 `Finset`。
7. **在数学含义相同处接近 Mathlib。** 优先采用 `Adj`、`IsLink`、`Inc`、`neighborSet`、`incidenceSet`、`degree`、`Reachable`、`Connected`、`IsAcyclic`、`Hom/Embedding/Iso` 等已验证词汇。
8. **依赖图可分阶段、可并行施工。** 基础表示、walk 数据、变换、有限视图、connectivity、weights 应有明确边界。

### 1.2 非目标

- 本轮不实现任何 Lean 声明或算法。
- 不在基础图层解决完整的复杂度记账、RAM 模型、持久化数据结构或动态算法框架。
- 不把所有 Mathlib `SimpleGraph` 定理复制进 GraphLib。
- 不为四种图强制完整 API parity。
- 不预先统一 hypergraph、quiver、incidence geometry、loop 的两个 half-edge 等更一般对象。
- 不把非负性、加法、线性序等算法假设塞进 weight/capacity 的表示。

---

## 2. Mathlib 基础评估

### 2.1 锁定版本与实际范围

项目的 `lake-manifest.json` 锁定 Mathlib commit [`d802ffd29d`](https://github.com/leanprover-community/mathlib4/commit/d802ffd29db1f5dc5a29206b1a8af62bfcc234a3)（2026-05-13），Lean 为 `v4.30.0-rc2`。`lakefile.toml` 的版本意图和 manifest 中 `inputRev = "master"` 并不完全一致；在架构实施前应先固定依赖策略，避免一次 `lake update` 悄悄更换基础 API。

锁定版本明显偏重 simple graph：`Mathlib/Combinatorics/SimpleGraph/` 有完整 walk、connectivity、finite、degree、maps、subgraph 和大量理论；`Graph/` 只有新的 multigraph 基础、subgraph、delete、map、lattice；`Digraph/` 基本还是关系。这一事实本身就是“不追求四路对称”的证据。

### 2.2 `SimpleGraph`：应复用的成熟词汇和 API 形状

相关基础文件：

- `Mathlib/Combinatorics/SimpleGraph/Basic.lean`
- `Finite.lean`、`DegreeSum.lean`、`Dart.lean`
- `Walk/Basic.lean`、`Walk/Operations.lean`、`Walk/Maps.lean`
- `Paths.lean`、`Trails.lean`
- `Subgraph.lean`、`Maps.lean`、`DeleteEdges.lean`、`Operations.lean`
- `Connectivity/Connected.lean`、`Connectivity/Finite.lean`
- `Acyclic.lean`

值得采用的内容：

- `Adj`、`adj_comm`、`neighborSet`、`neighborFinset`、`incidenceSet`、`incidenceFinset`、`degree`、`minDegree/maxDegree` 的命名与 Set/Finset 双层接口。
- `mem_*`、`coe_*`、map/induce/delete 的 simp 定理，以及 `sum_degrees_eq_twice_card_edges` 这类基础计数结果。
- walk 的操作清单：`append/concat/reverse`、`take/drop`、support/edges/darts、bypass/toPath、map/transfer。
- `Reachable := Nonempty Walk`、`Preconnected`、`Connected`、`ConnectedComponent`、`IsAcyclic`、`IsTree` 等标准语义。
- `Hom`、`Embedding`、`Iso` 的区分，以及 map 在保持 path 时需要 injectivity 这一事实。

不应照搬的表示特有机制：

- Mathlib `SimpleGraph` 把整个类型当作顶点宇宙；GraphLib 显式 `V(G)` 的选择对删点与算法不变量更合适。
- `SimpleGraph.Walk` 同时被 graph 和两个端点索引，导致 `copy`、端点相等证明、`HEq` 和大量 transport API。GraphLib 当前 graph-independent 数据 + realized predicate 已经展示了更低摩擦的替代方案。
- Mathlib 的 dependent `SimpleGraph.Subgraph G` 需要 `coe`、`spanningCoe`、`coeInduceIso` 等大量桥接。GraphLib 应继续让子图是与原图同型的 graph value。
- `SimpleGraph.induce s : SimpleGraph s` 的 subtype 版本不适合作为 GraphLib 的默认 induced operation。

### 2.3 新 `Graph α β`：特别重要的稳定先例

锁定版本的 `Mathlib/Combinatorics/Graph/Basic.lean` 已把一般无向多重图定义为：显式顶点集、**真正的边身份集** `E(G) : Set β` 和 `IsLink e x y`。它派生 `Inc`、`Adj`、`incidenceSet`、loop predicates 和 `Compatible`。

其 `Subgraph.lean`、`Delete.lean`、`Maps.lean` 已验证以下设计：

- 子图仍是 `Graph α β`，用 `H ≤ G`；
- `≤s` 表示 spanning subgraph，`≤i` 表示 induced subgraph；
- `restrict/deleteEdges/induce/deleteVerts` 保持 ambient 类型；
- vertex map 保留 edge identity，顶点合并可产生 loop；
- 同一 edge identity 在两图中的 incidence 若可能不同，union/intersection 需要兼容性概念。

GraphLib 当前总体方向与此接近，但其 `E(G)` 对一般图返回端点像，反而抹掉 `β` 身份。这一点应向 Mathlib 的稳定经验靠拢。

### 2.4 `Digraph` 的局限

锁定版本的 `Mathlib/Combinatorics/Digraph/Basic.lean` 是关系 `V → V → Prop`，允许 self-loop，形成 complete Boolean algebra；没有显式 `V(G)`、平行边身份、directed walk、in/out degree、SCC、reverse 或 deletion。它只能作为 simple relational digraph 的词汇参考，不能承担 GraphLib 的身份敏感 `DiGraph α ε`。

### 2.5 当前 master 与实验方向

审计时 Mathlib master 为 [`e310d5e001`](https://github.com/leanprover-community/mathlib4/commit/e310d5e001a2ec728600676771bcb803855a1854)。pin 之后已经合并的相关变化包括 [`Graph.Simple`](https://github.com/leanprover-community/mathlib4/blob/e310d5e001a2ec728600676771bcb803855a1854/Mathlib/Combinatorics/Graph/Simple.lean)：它引入 `Graph.Loopless`、`Graph.Simple`，以及一般图和顶点 subtype 上 Mathlib `SimpleGraph` 的桥接。这说明“显式 vertex set 的一般图 + adapter”是现实方向，也再次暴露 subtype bridge 的成本。

目前没有合并的 `Mathlib/Combinatorics/GraphLike`。公开但仍实验性的方向至少有：

- dart-first [`#36743`](https://github.com/leanprover-community/mathlib4/pull/36743) 及 unified walk [`#36756`](https://github.com/leanprover-community/mathlib4/pull/36756)；
- 另一套 `IsSource/IsTarget/IsLink` 草案 [`#39586`](https://github.com/leanprover-community/mathlib4/pull/39586)；
- incidence-first `HyperGraphLike/GraphLike` 与 `WalkData + IsValid` [`#40204`](https://github.com/leanprover-community/mathlib4/pull/40204)。

这些方案仍竞争，部分依赖链 open/blocked；不能作为 GraphLib 当前规范。不过 `WalkData + validity` 的分层与 GraphLib 已验证的路线相容，是继续保持该分层的额外支持。GraphLib 现在不应追随某一草案建立大型公共 typeclass。

### 2.6 Mathlib 的关键空白

即使按 current master 看，仍没有一套同时覆盖以下内容的稳定基础：显式边身份的有向多重图、directed/general unified walks、contraction、vertex splitting、统一 weight/cost/capacity 和 executable refinement。因此这些必须由 GraphLib 根据 TCS 客户端自行设计。

---

## 3. 当前 GraphLib 评估

### 3.1 应保留：已有下游验证的主干

1. **显式顶点集合的总体方向。** 四种图都显式携带 `vertexSet`，使删点、空图、动态图状态与 ambient `α` 上的陈述自然。
2. **具体而小的 `Adj` API。** `Graph/Adjacency.lean` 对四种图分别定义 `Adj`，简单清楚；无需为了四个短定义建立抽象层。
3. **`VertexSeq → SimpleWalk → SimplePath → SimpleCycle`。** 这条链有稳定的 length/head/tail/support、append/glue/reverse、prefix/suffix、erase、edge/arc 操作。尤其必须保持：
   - `length` 是边数；
   - `append` 保留两个连接端点，`glue` 合并相等端点；
   - undirected `SimpleCycle` 最短长度为 3；
   - 这些类型保留 root namespace 和当前 subtype/definitional-equality 链。
4. **组合数据与 realized predicate 分离。** `SimpleGraph.IsVertexSeqIn`、`IsSimpleWalkIn`、`IsSimplePathIn`、`IsSimpleCycleIn` 已提供操作闭包、edge characterization、generated-graph/subgraph bridge 和 supergraph monotonicity。
5. **girth 与 Moore bound 的实际验证。** `SimpleCycle.ofTwoPaths`、图内两路成圈、最短圈、rooted/half layer 等证明反复消费上述接口。这比未被使用的“漂亮抽象”更有说服力。
6. **`InSimpleDiGraph` 的方向性处理。** 它正确地没有声称 reverse 后仍在同一有向图；这应扩展为 `G.reverse` 中的运输定理。

### 3.2 应重构：合理但尚未稳定的部分

1. **一般图的边模型。** 当前 `Graph α β` 的 `edgeSet` 是 `Set (Edge α β)`，而 `E(G)` 是端点像 `Set (Sym2 α)`；`DiGraph` 同理。这让平行边在 `E(G)` 中折叠，且 `subgraphOf` 不得不绕开公共 notation 使用字段。应在基础层一次性修正。
2. **一般 `Walk α ε`。** edge-interleaved 数据形状可保留，但 `ε` 应明确为 edge identity；补 `Graph.IsWalkIn`/`DiGraph.IsWalkIn`。任意 raw walk 不再直接生成一个以同一 `ε` 为身份的 graph，因为同一 identity 可能在 raw 数据中被赋予不一致端点；应改成 occurrence-index generated graph，或只从 realized walk 生成 ambient subgraph。
3. **`Finite.lean`。** simple 两类的 Set/Finset 桥可保留；一般图必须另假设 actual edge set finite。算法不可直接消费 noncomputable finsets。
4. **`Subgraph.lean`。** 当前只有定义，应补 partial-order、spanning/induced predicates、simp、mono、ext 和变换闭包，再把 deletion 独立成文件。
5. **`InSimpleDiGraph.lean`。** 随着 directed path/cycle/reverse 增长应适度拆分，但不为形式对称预先复制所有 simple-undirected 文件。

### 3.3 应删除或替换

- `Graph/Graphs.lean`：16 个无类型/定义体 placeholder；以小而有效的 `Constructions.lean` 取代。
- `Theory/Structures/Basic.lean`：包含多套冲突表示的失效历史草稿；删除，不作为 umbrella。
- `Graph/Degree.lean` 当前版本：不是增量修补对象，应按本提案重写。现有错误包括未完成 notation、`*Finset` 实际返回 `Set`、`Set.ncard` 在 infinite 情形静默为 0 等。
- `Forest.lean` 中重复的 `Contains`、`Tree.lean` 中本地 `IsConnected`：迁移到正式 realized/connectivity API 后删除。
- `Search/Basic.lean` 与 `GraphTraversal/Basic.lean` 的重复占位：保留一个 `Algorithms/Traversal/` 路径。
- `.DS_Store` 与不进入公共入口的无效 umbrella。

### 3.4 下游暴露的基础 API 缺口

- `Girth.lean` 临时定义 `neighborSet/degree`；Moore core 又局部证明 neighbor subset、最小度选新邻点等。这些应进入 `Neighborhood/Degree`。
- rooted/half layers 多次手工做“向 realized path 末端追加 fresh adjacent vertex”。基础 path realization API 应返回具体 extension 及其 head/tail/support 定理，而不只返回存在性。
- realized monotonicity 直接拆 `subgraphOf` 的 pair 字段，说明 subgraph namespace 缺少命名 API。
- 全库缺少 delete、relabel、reverse graph、contraction、weights/capacities 和可执行邻接枚举。
- Eulerian/Hamiltonian 目前只比较 edge/vertex 覆盖，没有先要求 walk realized；这些只能视为早期草稿。

---

## 4. 核心设计决策

### 4.1 四种图的角色

#### 决策

- `SimpleGraph α`、`SimpleDiGraph α`：**主图类型**。为 adjacency、subgraph、transformations、finite、degree、walk/path/cycle、connectivity 提供完整基础 API；大多数算法首先针对它们陈述。
- `Graph α ε`、`DiGraph α ε`：**身份敏感图类型**。为 actual-edge incidence、删除、有限枚举、edge-aware walks、weights、MST、flow 等提供完整底层 API；高阶 simple-graph theory 不要求 parity。

#### 依据

- Mathlib 的成熟度本来就高度不对称。
- 当前 GraphLib 的有效下游几乎全部走 simple 主链。
- MST、flow、残量网络和 Euler trail 又确实不能丢边身份，因此 general 类型不能只是临时转换目标。

### 4.2 一般图的基础表示：`ε` 就是边身份

#### 决策

一般无向图采用与 Mathlib `Graph` 同形的语义核心：

```lean
-- 伪签名；字段细节可按 Mathlib 的已验证公理组织
structure Graph (α ε : Type*) where
  vertexSet : Set α
  edgeSet   : Set ε
  IsLink    : ε → α → α → Prop
  -- IsLink 对端点对称、每条边只有一个无序端点对、
  -- edge membership 与存在端点等价、端点属于 vertexSet
```

一般有向图采用对应的有向版本：

```lean
structure DiGraph (α ε : Type*) where
  vertexSet : Set α
  edgeSet   : Set ε
  IsArc     : ε → α → α → Prop
  -- 每条边只有一个有序 (source,target)，
  -- edge membership 与存在 source/target 等价，端点属于 vertexSet
```

公共接口为：

```lean
E(G) : Set ε
G.IsLink e u v       -- undirected general
G.IsArc  e u v       -- directed general
G.Inc e v
G.Adj u v
```

`β/ε` 不再叫“普通 label”；它是 edge identifier。其他 label、weight、cost、capacity 是 `ε → X` 的外部数据。

#### 为什么不保留当前 `Edge α β`/`Arc α β`

- 当前 `E(G)` 折叠平行边，与逐边删除/赋权冲突。
- vertex relabel 会改变 bundled edge value，导致本可保持的 weight/capacity 也必须搬运。
- 同一 `β` 可以配不同端点，因而它其实不是稳定身份。

#### 与 Mathlib 的关系

这是对 Mathlib 稳定 `Graph α β` 的**语义适配**。暂不直接 type-alias Mathlib：GraphLib 还需要成对的 explicit-vertex simple/direct types、自己的 namespace 和 directed identity graph；但公共术语与 adapter 应保持接近。

### 4.3 simple graph 表示

继续保留：

```lean
SimpleGraph α   -- V : Set α, E : Set (Sym2 α), loopless
SimpleDiGraph α -- V : Set α, E : Set (α × α), loopless
```

这里边身份就是端点对；这是 simple 情形的正确含义。`E(G)` 在四种图上都统一表示“实际边 carrier 的集合”，只是 carrier 分别为 `Sym2 α`、`α × α`、`ε`、`ε`。

### 4.4 只建立小型共享接口，不建立公共 GraphLike 宇宙

保留轻量的 `HasVertexSet`/`HasEdgeSet` 以支持 `V(G)`/`E(G)`，并让 `HasEdgeSet` 的输出是 actual-edge set。除此之外：

- `Adj`、subgraph、degree 等可在同一文件中对四类型分别实现；
- 只用 private helper 消除机械证明重复；
- 可执行层单独定义一个真正有客户端的 `FiniteAdjView`/`FiniteEdgeView`；
- 不建立 `Directed`、`Loopless`、`NoParallelEdge` 等大型 typeclass hierarchy。

原因是四种表示的真实差异大于可省下的少量重复，Mathlib GraphLike 方向也尚未稳定。

### 4.5 目录按概念组织，必要时按表示拆分

采用 hybrid，但第一层以概念为主：`Graph/`、`Walk/`、`Connectivity/`、`Weight/`、`Executable/`。一个基础概念若四种图都只有短定义，就放同一文件；只有当 dependency、证明规模或表示确实分叉时才拆 simple/general 或 directed/undirected。

因此不采用四份平行的 `SimpleGraph/Degree.lean`、`DiGraph/Degree.lean` 树。那会制造“应该 parity”的错误预期，并让用户难找“degree 到底在哪”。

### 4.6 graph-independent walks 与 realized-in 层

保留当前策略并推广：

- `VertexSeq α`：非空顶点序列。
- `SimpleWalk α`：nonstalling vertex sequence。
- `SimplePath α`：顶点不重复的 simple walk。
- `SimpleCycle α`：无向 convention，长度至少 3。
- 新增 `SimpleDiCycle α`：有向 simple cycle，simple digraph 无 loop，故允许长度 2。
- `Walk α ε`：图无关的 vertex/edge identity 交错序列。
- `Trail α ε`：edge identity 不重复。
- `Path α ε`：vertex 不重复。
- `Circuit α ε`：非空 closed trail。
- `Cycle α ε`：closed walk，除重复的首尾外顶点不重复，并且边不重复。一般无向/有向图允许 loop cycle（长度 1）；一般无向图的两条平行边允许长度 2 cycle。这样 Eulerian、girth 和 multigraph cycle 的语义不冲突。

realization 分开：

```lean
G.IsSimpleWalkIn w      -- SimpleGraph / SimpleDiGraph
G.IsWalkIn w            -- Graph / DiGraph，检查 edge identity 与端点
```

`Reachable` 用 existential path 定义。只有需要一等 certificate 的结果结构才 bundle `p` 和 `Is…In p`；不把 graph/indexed endpoints 固化进 path carrier。

对一般 raw `Walk α ε`，不保留当前无条件 `toGraph : Graph α ε`。替代为：

- `w.occurrenceGraph`：用 step occurrence 作为 edge identity，永远定义良好；
- `h.spannedSubgraph`：若 `h : G.IsWalkIn w`，在 ambient `G` 中取实际所用边和顶点组成的子图。

这避免同一 raw `ε` 在多个 step 被赋予冲突端点。

### 4.7 子图和同类型变换

四种图都提供同名基础概念：

```lean
H ≤ G                     -- subgraph
H ≤s G                    -- spanning subgraph
H ≤i G                    -- induced subgraph
G.induce S
G.restrictEdges F         -- 保留 V(G)，只留 F ∩ E(G)
G.deleteEdges F
G.deleteVerts S
G.edgeGenerated F         -- 只保留 F 的边及其实际端点
```

语义约定：

- `induce S` 的 vertex set 是 `S ∩ V(G)`，保持当前 GraphLib 的宽容输入；
- `deleteVerts S = induce (V(G) \ S)`；
- `restrictEdges F` 是 spanning restriction；
- `edgeGenerated F` 的 vertex set 只是 retained edges 的端点，不能与 spanning restriction 混名；
- 单点/单边版本只是 Set singleton 的 convenience wrapper。

simple 两类的 union/intersection 可以按 vertex/edge set 构造。general 两类只有在共有 edge identities 的 endpoints/incidence 兼容时提供 union/intersection；在固定 ambient `G` 的 subgraphs 之间兼容性自动成立。不要给不兼容 general graphs 定义误导性的任意 union。

### 4.8 map、relabel、reverse 与 canonical conversions

区分：

1. `mapVertices (f : α → γ)`：允许非单射，用于 contraction 的 primitive。general 图保留 edge identities；simple 图丢弃由合并产生的 loops。
2. `relabelVertices (e : α ≃ γ)`：同构式 transport；必须有 `id/comp/symm`、Adj、subgraph、walk 和 weight 定理。
3. general graph 的 `relabelEdges (e : ε ≃ δ)` 及同时 relabel vertices/edges 的组合版本。
4. `reverse` 仅对 directed 两类：保持 vertex/edge identities，交换 source/target，满足 involution。

canonical conversions：

- `SimpleGraph.toGraph : Graph α (Sym2 α)`；
- `SimpleDiGraph.toDiGraph : DiGraph α (α × α)`；
- `Graph.underlyingSimple`、`DiGraph.underlyingSimple`：丢 loop、合并平行边，必须是显式命名的有损函数，不设 coercion；
- `DiGraph.forgetDirection : Graph α ε` 保留 edge identity；
- `SimpleDiGraph.forgetDirection : SimpleGraph α` 合并 antiparallel arcs；
- 从 undirected graph 选 orientation 不是 canonical conversion，必须要求额外 orientation 数据。

移除目前 simple→general 的隐式 `Coe`；丢失/改变表示的转换不应在 elaboration 中悄悄发生。

### 4.9 contraction

contraction 本质上改变 vertex type，不伪装为同 ambient 操作：

```lean
G.contractSet S : Graph (Contract α S) ε
G.contractSet S : SimpleGraph (Contract α S)
contractMap S : α → Contract α S
```

`Contract α S` 是把 `S` 中顶点识别成一个点的 quotient-like carrier。general 图保留因此产生的 loops 和所有 edge identities；simple 图删除 loops 并自然合并重复 endpoint edges。提供：

- vertex/edge membership 与 `contractMap` 的 simp API；
- `mapVertices` characterization；
- 对 `S = ∅`、singleton、nested/disjoint contractions 的基础定理；
- subgraph 与 weights transport。

非单射 map 不保持 `SimplePath`：路径可能 stall 或重复。因此只承诺先得到 mapped `VertexSeq/Walk`，再经 `loopErase/cycleErase` 得到 path。API 不制造假的 direct path transport。

### 4.10 vertex splitting

初始版本只承诺 TCS 中最清楚、最有客户的 directed split：把 `v` 替换为 `v_in`、`v_out`，原入边接到 `v_in`，原出边从 `v_out` 发出，并加入 connector arc。结果 edge carrier 必须能容纳新边，例如 `Sum ε Unit`，并返回 old-vertex/old-edge injection 和 connector 的刻画定理。

```lean
G.splitVertex v : DiGraph (SplitVertex α v) (Sum ε Unit)
```

这足以表达 vertex-capacity reduction。任意 incident-edge partition、多份 clone、undirected split 暂不抽象成一个万能 `SplitSpec`；等第二个真实客户端出现再推广。

### 4.11 adjacency、incidence、neighborhood 与 degree

接口分层：

- `Adjacency.lean`：`Adj` 及 endpoint membership、symmetry/irreflexivity。
- `Incidence.lean`：actual-edge `IsLink/IsArc/Inc`、`incidenceSet`、directed `in/outIncidenceSet`、loopSet；simple 图也给 incidence views。
- `Neighborhood.lean`：`neighborSet`、directed `in/outNeighborSet` 及 membership simp。
- `Finite.lean`：Set 到 Finset 的数学桥。
- `Degree.lean`：局部度与 extremal degree。
- `DegreeSum.lean`：handshake/in-out sum/average。

重要约定：

- `neighborSet` 是邻点集合；general graph 的 parallel edges 不增加其大小。
- general `degree` 数实际边重数；无向 loop 按标准 convention 贡献 2，因此不能简单等于 `incidenceSet.ncard`，应是 `incidenceSet.ncard + loopSet.ncard` 或等价的 dart count。
- directed loop 对 in-degree 和 out-degree 各贡献 1。
- 不再定义一个在 infinite set 上悄悄返回 0 的 `degree : ℕ`。初始 API 采用：

```lean
degree (G) (v) [Finite (G.incidenceSet v)] : ℕ
outDegree / inDegree ...
```

  若以后 infinite graph 客户需要，再加 `eDegree : ℕ∞ := Set.encard ...`，不提前让两套 API扩散。
- finite nonempty graphs 上提供 `minDegree/maxDegree : ℕ`；`maxDegree` 可对空图约定 0，`minDegree` 与 `averageDegree` 要求 vertex nonempty。`averageDegree` 值域用 `ℚ`，不错误地取整为 `ℕ`。

### 4.12 有限数学图与 executable view

数学层：

- simple 两类：`Finite V(G)` 推出 `Finite E(G)`；
- general 两类：分别要求 `Finite V(G)` 和 `Finite E(G)`，因为有限顶点可有无限平行边；
- 提供 noncomputable `vertexFinset/edgeFinset/neighborFinset/incidenceFinset` 与精确 membership/coercion lemmas。

执行层另设：

```lean
structure FiniteAdjView (G) where
  vertices : Finset α
  succ     : α → Finset α
  mem_vertices_iff : v ∈ vertices ↔ v ∈ V(G)
  mem_succ_iff     : u ∈ succ v ↔ G.Adj v u
```

身份敏感算法另用：

```lean
structure FiniteEdgeView (G : DiGraph α ε) extends FiniteAdjView G where
  edges    : Finset ε
  outEdges : α → Finset ε
  -- 精确对应 E(G)、IsArc
```

这些 view 是数据，不是从 `Finite` 命题 classical choice 出来的对象。未来 adjacency list/array/hash implementation 只需实现 view/refinement；数学 correctness theorem 仍陈述在原 `G` 上。

### 4.13 weights、costs、capacities

用 total ambient function 作为低摩擦数据，值只在 actual edges 上有语义：

```lean
Graph.EdgeWeight       (G : Graph α ε) W := ε → W
DiGraph.EdgeWeight     (G : DiGraph α ε) W := ε → W
SimpleGraph.EdgeWeight (G : SimpleGraph α) W := Sym2 α → W
SimpleDiGraph.EdgeWeight ...              := (α × α) → W
```

`EdgeCost`、`Capacity` 是语义 alias/薄 wrapper，不生成新的 graph type。另有 `VertexWeight := α → W`。等价性/外延只要求在 `E(G)` 或 `V(G)` 上 `EqOn`。

- induced/delete/restrict 保持 ambient carrier，原函数可直接复用；
- general vertex relabel/reverse 保持 edge identity，weight/capacity definitionally 不变；
- edge relabel 和 simple vertex relabel 提供显式 `transport`；
- `walkWeight`/`pathWeight` 才要求可加结构；Dijkstra 的非负与 order 假设放在算法定理；
- MST 的 `SpanningTree` 保存 actual edge subgraph；
- flow network 以 `DiGraph` 为核心，因为 residual network 即使从 simple digraph 开始也可能需要区分 antiparallel/residual arcs。

示意：

```lean
structure Network (G : DiGraph α ε) (R : Type*) where
  source sink : α
  source_mem : source ∈ V(G)
  sink_mem   : sink ∈ V(G)
  ne         : source ≠ sink
  capacity   : ε → R

def Flow (N : Network G R) := ε → R
def Flow.Feasible ... : Prop := ... -- capacity bounds + conservation
```

`[AddCommMonoid R]`、order、finite sums 等只出现在 `Feasible`/定理所在 section，不是 `Network` 的结构参数要求。

### 4.14 重要决策的证据汇总

| 决策 | Mathlib 先例 | 当前 GraphLib 证据 | TCS 压力测试 | 最终选择 |
|---|---|---|---|---|
| simple 类型为主 | `SimpleGraph` 有成熟且广泛的下游，general/digraph 明显更薄 | 完整成果集中在 simple walk→Moore 链 | BFS、SCC、普通 shortest path 不需 edge identity | simple 两类完整；general 两类底层完整、高阶理论薄 |
| `E(G)` 保留 actual identity | Mathlib `Graph.E(G) : Set β` | 当前 `E(G)` endpoint image 与 `subgraphOf` 字段语义冲突 | 平行边删除、MST、flow、cost 必须逐边 | general `ε` 是 identity；端点像另命名 |
| graph-independent walk data | Mathlib walk 操作成熟，但 indexed carrier 产生大量 transfer/copy API；实验 #40204 也转向 data+validity | 当前 path/cycle/girth/Moore 已验证这一分层 | reverse、relabel、subgraph certificate 可避免端点 cast | 保留 carrier + `Is…In`，扩展至 general/directed |
| induced 保持 ambient type | 新 Mathlib `Graph` 的 delete/induce 采用同型值；旧 `SimpleGraph.Subgraph` 展示 subtype 成本 | 当前 `induce` 已是同型且被 realization 使用 | 反复删点、SCC 子问题不能层层 subtype | induced/delete/restrict 同类型；contract/split 才换型 |
| 不建 GraphLike 大层 | Mathlib 尚有多套 open/draft 竞争方案 | 四个短 `Adj` 定义很清楚，没有真实 generic client | 强行统一不能解决 edge identity、directed reverse 差异 | 只保留 `V/E` 小接口和 executable views |
| 权重外置 | Mathlib 没有统一稳定 wrapper | 当前图结构尚无 weight 客户可约束设计 | 同一图可能同时有 weight/cost/capacity；算法假设不同 | total edge functions + transport，不乘图类型 |
| finite/executable 分层 | Mathlib finite connectivity 从数学有限性构造 decidability，但不是具体数据结构 | 当前 `Finite.lean` 同时有 noncomputable/compute 变体却无算法客户 | BFS 必须实际枚举 successor；general 还需枚举 actual edges | 数学 Finset API + 独立 `Finite*View` refinement |
| degree 只在有限局部取 `ℕ` | Mathlib stable `degree` 需要 neighbor-set `Fintype` | 当前 `Set.ncard` 会把 infinite 静默成 0；Girth 只用 finite 场景 | handshake/Moore 需要真实计数，不能接受假 0 | finite-local Nat degree；无限 extended degree 后置 |
| contraction 明确换型 | Mathlib vertex `map` 允许非单射并可产生 loop | 当前 `SimplePath.map` 已要求 injective | 收缩天然识别顶点，path 可能 stall/repeat | quotient-like carrier + provenance map + erase |
| directed split 先行 | Mathlib 无稳定 API | 当前无客户端约束任意 split | flow 的 vertex-capacity reduction 给出明确 two-way 需求 | 先做 `v_in/v_out`，万能 split spec 后置 |

---

## 5. 建议的目录 / module tree

```text
GraphLib/
├── Graph/
│   ├── Basic.lean
│   ├── Adjacency.lean
│   ├── Incidence.lean
│   ├── Neighborhood.lean
│   ├── Subgraph.lean
│   ├── Delete.lean
│   ├── Map.lean
│   ├── Reverse.lean
│   ├── Finite.lean
│   ├── Degree.lean
│   ├── DegreeSum.lean
│   ├── Contraction.lean
│   ├── VertexSplit.lean
│   └── Constructions.lean
├── Walk/
│   ├── VertexSeq.lean
│   ├── VertexSeq/
│   │   ├── Basic.lean
│   │   ├── Predicates.lean
│   │   ├── Append.lean
│   │   ├── Subseq.lean
│   │   ├── Erase.lean
│   │   ├── Edges.lean
│   │   ├── MapZip.lean
│   │   └── Index.lean
│   ├── SimpleWalk.lean
│   ├── SimplePath.lean
│   ├── SimpleCycle.lean
│   ├── SimpleDiCycle.lean
│   ├── Walk.lean
│   ├── PathTrailCycle.lean
│   ├── InSimpleGraph.lean
│   ├── InSimpleGraph/{VertexSeq,Walk,Path,Cycle}.lean
│   ├── InSimpleDiGraph.lean
│   ├── InGraph.lean
│   └── InDiGraph.lean
├── Connectivity/
│   ├── Reachability.lean
│   ├── Connected.lean
│   ├── StronglyConnected.lean
│   └── Acyclic.lean
├── Weight/
│   ├── Basic.lean
│   ├── Walk.lean
│   └── Network.lean
├── Executable/
│   ├── FiniteView.lean
│   └── Refinement.lean
├── Interop/
│   └── Mathlib.lean
├── Theory/
│   ├── Girth.lean
│   ├── MooreBound/...
│   ├── Coloring/Bipartite.lean
│   ├── Trees/Basic.lean
│   ├── Matching/...
│   └── ...                         -- 高层理论，不属于 foundation
├── Algorithms/
│   ├── Traversal/...
│   ├── SCC/...
│   ├── ShortestPath/...
│   ├── MST/...
│   └── Flow/...
└── Util/
    └── List.lean
```

说明：

- `Walk/` 是基础而不是高层 `Theory/Structures/`。
- 现有 `VertexSeq` 子文件大小和 dependency 边界已经合理，不合并。
- `InSimpleDiGraph` 先保持一文件；只有规模或依赖真实增长时再按 Walk/Path/Cycle 拆。
- `Contraction` 与 `VertexSplit` 独立，是因为它们改变 carrier 且依赖 maps；不是为四图对称而拆。
- `Constructions.lean` 初期只放 empty、singleton、complete、path/cycle/star/complete bipartite 等有实现和 simp API 的构造，不恢复 placeholder 清单。

---

## 6. 文件逐项职责

### 6.1 `Graph/`

| 文件 | 适用图型 | 主要定义/API | 依赖与客户 |
|---|---|---|---|
| `Basic.lean` | 四种 | 四结构；`V/E` actual-set notation；general `IsLink/IsArc` 的结构公理；extensionality；loopless；simple→general 与 underlying-simple 的命名转换 | 全库底座；应尽量只依赖 `Set/Sym2` |
| `Adjacency.lean` | 四种 | `Adj`；无向 `symm/adj_comm`；simple `ne`；端点 membership；conversion lemmas | walks、coloring、connectivity、views |
| `Incidence.lean` | 四种，general 为主 | `Inc`、`incidenceSet`、`loopSet`；directed `out/inIncidenceSet`；simple incidence；edge/vertex membership；`IsLink/IsArc` uniqueness 与 endpoint API | degree、Eulerian、weights、finite edge view |
| `Neighborhood.lean` | 四种 | neighbor / in-neighbor / out-neighbor Set；`mem_* ↔ Adj`；subset `V(G)`；map/subgraph monotonicity | degree、Moore、BFS/SCC |
| `Subgraph.lean` | 四种 | `≤` partial order；`≤s`、`≤i`；`induce`；`restrictEdges`、`edgeGenerated` 的关系性质；ext/compatibility；Adj/Inc mono/congr；induce simp/idempotence/nesting | realized monotonicity、connectivity、MST、deletion |
| `Delete.lean` | 四种 | `deleteEdges/deleteVerts` 及 singleton wrappers；membership/Adj/Inc simp；empty/union/commutation laws；subgraph facts | dynamic algorithms、cuts、minors |
| `Map.lean` | 四种 | `mapVertices`；`relabelVertices`；general `relabelEdges`；`Hom/Embedding/Iso` 的最小必要层；id/comp；subgraph/Adj/Inc transport | contraction、weights、path transport、interop |
| `Reverse.lean` | 两种 directed | graph reverse；edge/source/target/Adj simp；involution；subgraph/delete/induce/relabel commute | reverse path、SCC、residual networks |
| `Finite.lean` | 四种 | noncomputable vertex/actual-edge Finset；simple 的 `Finite V → Finite E`；general 分别要求；neighbor/incidence finset；membership/coercion/card bridges | degree、finite connectivity、数学计数 |
| `Degree.lean` | 四种 | finite-local `degree`、in/out degree；parallel/loop convention；min/max degree；regularity predicates；neighbor/incidence equivalences | girth/Moore、MST bounds、graph theory |
| `DegreeSum.lean` | 四种，simple + general undirected优先 | handshake；directed sum-in=sum-out=`|E|`；average degree（非空 finite）；必要的 weighted sum variants后置 | Moore、density、flow sanity |
| `Contraction.lean` | 四种，general/simple undirected优先 | `Contract α S`、`contractMap`、`contractSet/contractEdge`；membership、loops、map characterization、subgraph/weight transport | minors、MST exchange、dynamic algorithms |
| `VertexSplit.lean` | `DiGraph` 首先，`SimpleDiGraph` wrapper | two-way directed split；新 vertex/edge carriers；old-edge injection、connector、Adj/Inc characterization；reverse/weight hooks | vertex-capacity reduction、flow |
| `Constructions.lean` | simple 两类优先 | empty/no-edge、singleton、complete、path、cycle、star、complete bipartite；每个都有 V/E/Adj simp 与 finiteness | examples、tests、basic theory |

### 6.2 `Walk/`

| 文件 | 主要责任 | 重要 API / 客户 |
|---|---|---|
| `VertexSeq*` | 原样保留成熟的非空序列、predicates、append/reverse、subsequence、erase、edge/arc list、map/index | 所有 vertex-only walks；Moore；BFS path certificates |
| `SimpleWalk.lean` | nonstalling subtype及操作 | 保持现有 defeq、append/glue、reverse、erase、map |
| `SimplePath.lean` | vertex-nodup subtype | extension constructor、prefix/suffix、map injective、loop erase；补具体 fresh-tail extension API |
| `SimpleCycle.lean` | undirected cycle，长度至少 3 | interior、reverse/reroot、ofPathClosing/ofTwoPaths；保持 Moore 客户 |
| `SimpleDiCycle.lean` | directed cycle，允许长度 2 | rotation；reverse 只作为进入 reversed graph 的数据，不声称同图 realization |
| `Walk.lean` | edge-identity-aware raw alternating data | 保留当前 visitor/edge list/operations；明确 `ε` 为 identity；`occurrenceGraph` 替代歧义 `toGraph` |
| `PathTrailCycle.lean` | general raw walk 上的 predicates/subtypes | `Trail/Path/Circuit/Cycle`；edge/vertex nodup、closed、loop conventions；不依赖 graph |
| `InSimpleGraph*` | simple-undirected realization | 保留所有当前 validated API；补 delete/induce/relabel transport与 path extension |
| `InSimpleDiGraph.lean` | simple-directed realization | vertex sequence/walk/path/cycle；direction-preserving operations；`G.reverse` transport |
| `InGraph.lean` | general undirected realization | `IsWalkIn` 逐步检查 actual `e` 的 `IsLink`；edge membership；reverse；trail/path/cycle；`spannedSubgraph` |
| `InDiGraph.lean` | general directed realization | `IsWalkIn` 检查 `IsArc e u v`；reverse graph transport；in/out endpoints；flow-path 客户 |

`List.commonPrefix` 移到 `Util/List.lean`；它不是 `VertexSeq` API。

### 6.3 `Connectivity/`

| 文件 | 适用图型 | 内容 |
|---|---|---|
| `Reachability.lean` | 四种 | existential path 定义；refl（需 vertex membership）、step、trans；undirected symm；directed reverse；等价于 adjacency reflexive-transitive closure；subgraph/map/delete lemmas |
| `Connected.lean` | 无向两种，simple 优先 | `Preconnected/Connected`、components、connected component support、induced component、finite decidability接口；quotient 只在内部对 `V(G)` subtype 使用 |
| `StronglyConnected.lean` | directed 两种 | mutual reachability、SCC sets/partition、condensation 的规范层；不实现算法 |
| `Acyclic.lean` | simple 两类优先，general 按 cycle semantics | `IsAcyclic`；forest/tree；唯一简单路等基础 bridge；重写现有 Forest/Tree |

### 6.4 `Weight/`

| 文件 | 内容 | 客户 |
|---|---|---|
| `Basic.lean` | edge/vertex data、weight/cost/capacity aliases；`EqOn` ext；restrict/relabel/reverse/contract transport | 所有加权算法 |
| `Walk.lean` | edge-aware `walkWeight/pathWeight`；simple vertex-pair path weight；map/reverse/append formulas；只在这里引入 fold/additive assumptions | shortest path、negative cycle、MST path arguments |
| `Network.lean` | `Network`、`Flow`、`Feasible`、cut capacity 的规范对象；不实现 max-flow algorithm | Flow 算法与 min-cut theory |

### 6.5 `Executable/`

| 文件 | 内容 | 边界 |
|---|---|---|
| `FiniteView.lean` | `FiniteAdjView`、`FiniteEdgeView`；undirected/directed successors；actual out-edge enumeration | 是算法输入 contract，不规定数组/哈希实现 |
| `Refinement.lean` | concrete repr 到数学 graph/view 的 correctness relation；从 view 得 membership、finite、decidable facts | 不在此设计 runtime accounting |

### 6.6 `Interop/`

`Interop/Mathlib.lean` 是可选的薄边界，不进入最小 `Graph.Basic` 依赖：

- identity-sensitive undirected `Graph α ε` 与 Mathlib `Graph α ε` 的双向转换/等价；
- `SimpleGraph α` 到 Mathlib `SimpleGraph V(G)` 的 adapter，以及通过 `Subtype.val` 回到 ambient `α` 的定理；
- `SimpleDiGraph` 到 Mathlib relational `Digraph α` 时，把 `V(G)` 外 adjacency 定为 false，并明确该转换丢失 explicit vertex-set 表示；
- 转换上的 `Adj/IsLink/Inc`, subgraph 和 finite facts；
- 不提供会隐藏 subtype 或信息丢失的 coercion。

这一文件允许复用 Mathlib 高层定理，又不让 Mathlib 的 representation 反向决定 GraphLib 的日常 API。

---

## 7. API 覆盖矩阵

图例：**全** = 基础与常用 lemma 完整；**薄** = 有可靠定义/transport，但不追求全部高阶理论；**共享/派生** = 主要从另一接口得到；**后置** = 初始 foundation 不承诺。

| API 家族 | `SimpleGraph` | `SimpleDiGraph` | `Graph` | `DiGraph` |
|---|---|---|---|---|
| adjacency | 全 | 全 | 全 | 全 |
| actual-edge incidence | 全/派生 | 全/派生 | 全 | 全 |
| neighbor sets | 全 | 全（in/out） | 全 | 全（in/out） |
| degree | 全 | 全（in/out） | 全，含 parallel/loop | 全（in/out） |
| subgraph order | 全 | 全 | 全 | 全 |
| induced / spanning | 全 | 全 | 全 | 全 |
| vertex / edge deletion | 全 | 全 | 全 | 全 |
| union / intersection | 全 | 全 | 兼容图/共同 ambient 内全 | 兼容图/共同 ambient 内全 |
| relabel / vertex map | 全 | 全 | 全 | 全 |
| reverse graph | 不适用；walk reverse 全 | 全 | 不适用；walk reverse 全 | 全 |
| contraction | 全 | 薄 | 全 | 薄 |
| vertex splitting | 后置 | 薄 wrapper | 后置 | 全（directed two-way） |
| finite mathematical API | 全；`Finite V` 推边有限 | 全；同左 | 全；V/E 分别有限 | 全；V/E 分别有限 |
| executable view | 全 adjacency view | 全 adjacency view | 全 edge view | 全 edge view |
| walk/path/cycle | 全 vertex-only | 全 vertex-only，独立 DiCycle | 基础完整、edge-aware | 基础完整、edge-aware |
| reachability | 全 | 全 | 全/薄定理 | 全/薄定理 |
| connected components | 全 | 不适用 | 薄 | 不适用 |
| SCC | 不适用 | 全规范层 | 不适用 | 全规范层 |
| acyclicity/tree theory | 全 | 基础 | 薄/后置高级理论 | 薄/后置高级理论 |
| weights/costs | 全 | 全 | 全 | 全 |
| capacities/flow | 不适用 | 经 `toDiGraph`/wrapper | 不适用 | 全 |
| MST instance | 全 | 不适用 | 全 | 不适用 |

“general reachability 薄定理”不表示定义不完整，而是不会立即复制 simple graph 全部 finite/connectivity theory。

---

## 8. Mathlib reuse / adapt / diverge / skip 表

| 概念 | 分类 | 选择与理由 |
|---|---|---|
| `Adj`、neighbor/incidence naming | **Adapt** | 采用名称与 theorem shape；适配 explicit `V(G)` 和四种本地表示 |
| 一般 `Graph α ε` 的 edge identity + `IsLink` | **Adapt** | 采用 Mathlib 稳定语义；保留 GraphLib namespace/配套 directed type |
| `V(G)` / `E(G)` | **Adapt** | 保留 notation，但 `E` 一律是真实边集；修正当前 endpoint-image 含义 |
| simple `neighborSet/Finset/degree` | **Adapt** | 吸收 Set/Finset 桥；degree 避免 infinite `ncard=0` |
| `Inc`、`IsLink`、loop predicates | **Adapt** | 与 Mathlib 术语对齐；当前 closure theorem `incidence` 改名为 endpoint membership 类 lemma |
| handshake / degree sum | **Adapt** | 采用 theorem interface；general loop 明确计 2 |
| graph-indexed `SimpleGraph.Walk u v` | **Intentionally diverge** | 保留 graph-independent data + realization，避免端点/cross-graph transport 债务 |
| walk 操作与 `IsTrail/IsPath/IsCycle` 词汇 | **Adapt** | 操作清单与命名复用，carrier 不照搬 |
| dependent `SimpleGraph.Subgraph G` | **Intentionally diverge** | 同 ambient graph value 更适合反复删除和算法状态 |
| `H ≤ G`、`≤s`、`≤i` | **Adapt** | 采用成熟 notation/structure；四本地图型各自实例 |
| `induce/deleteVerts/deleteEdges/restrict` | **Adapt** | 保持 ambient type；GraphLib `induce` 输入外部点时取交集的现语义可保留并写清 |
| `Hom/Embedding/Iso` | **Adapt** | 只建真实客户需要的薄层，不复制全部 relation morphism hierarchy |
| Mathlib `Digraph V = V → V → Prop` | **Skip/postpone direct reuse** | 不支持 explicit V 或 edge identity；仅提供未来 adapter |
| Mathlib standard constructors | **Adapt selectively** | 名称相同时对齐；只实现近期客户，不抄完整目录 |
| Mathlib GraphLike / unified walk PR | **Skip/postpone** | 未合并且方案竞争；只保留 data+validity 的兼容思想 |
| Mathlib `Graph.Simple` adapter | **Reuse directly where possible** | 等升级 pin 后用 adapter，不让它决定本地核心表示 |
| contraction / vertex split | **Intentionally diverge / own API** | Mathlib 稳定层无对应；按 TCS 使用和低 cast 原则设计 |
| weighted graph wrappers | **Intentionally diverge** | 用外部 edge data 避免图类型组合爆炸 |

主要有意分歧都来自 GraphLib 的 explicit vertex-set、动态操作和算法 certificate 目标，而不是另造词汇。

---

## 9. 当前 GraphLib 迁移计划

### 9.1 第一批：breaking foundation migration

| 当前文件/声明 | 迁移 |
|---|---|
| `Graph/Basic.lean` 的 `Edge/Arc`、general `edgeSet`、`HasEdgeSet` | 重做 general graph 为 actual `ε` edge set + `IsLink/IsArc`；`E(G)` 改为 actual edges；移除或仅临时 deprecated `Edge/Arc` shim |
| `SimpleGraph.toGraph`、`SimpleDiGraph.toDiGraph` coercion | 保留显式函数，移除隐式 `Coe`；新增有损 underlying-simple 命名函数 |
| `Graph/Adjacency.lean` | simple 定义大体保留；general 改由 `∃ e, IsLink/IsArc`；保持现有 `Adj.*_mem` API |
| `Graph/Subgraph.lean` | 在新表示上改为 `≤` partial order，补 `≤s/≤i`；将 delete 移到 `Delete.lean` |
| `Graph/Finite.lean` | 保留 simple 证明与 API 形状；所有 `edgeFinset` 指 actual edges；加 general 的独立 edge finiteness版本 |

这批应在其他 general graph 客户继续增长前完成。迁移期不要同时维护“endpoint E”与“identity E”两个公共 notation；端点像使用明确名称 `edgeEnds`/`arcEnds`。

### 9.2 第二批：保留成熟 walk 主链并搬目录

- `Theory/Structures/VertexSeq*` → `Walk/VertexSeq*`，声明 namespace 不变。
- `SimpleWalk.lean`、`SimplePath.lean`、`SimpleCycle.lean` → `Walk/`，定义和 defeq 尽量不变。
- `InSimpleGraph/*` → `Walk/InSimpleGraph/*`；保留 `iff_edges`、generated subgraph、erase、mono 和两路成圈 API。
- `InSimpleDiGraph.lean` → `Walk/InSimpleDiGraph.lean`；后续再补 path/cycle/reverse graph。
- `VertexSeq/CommonPrefix.lean` 的 List 内容 → `Util/List.lean`，原 import 可保留一版 deprecated forwarding module。
- 当前 `Walk.lean` → 新 `Walk/Walk.lean`，把 edge 参数语义改为 identity；删除或更换歧义 `toGraph/toDiGraph`。
- 填充现有空 `InGraph.lean`，新增 `InDiGraph.lean`；`Path/Trail/Cycle` 合并成一个真实 dependency 单元 `PathTrailCycle.lean`，避免四个空壳。

### 9.3 第三批：基础缺口

- 完全重写 `Graph/Degree.lean`，拆成 `Incidence`、`Neighborhood`、`Degree`、`DegreeSum`。
- 将 `Girth.lean` 的临时 `neighborSet/degree` 以及 Moore core 的三条基础 helper 迁回；尽量保持 simple degree 的定义展开和现有证明易重写。
- 新建 `Delete/Map/Reverse`，随后才实现 `Contraction/VertexSplit`。
- 删除 `Graph/Graphs.lean`，在 `Constructions.lean` 中逐个加入有完整 API 的构造。

### 9.4 第四批：重写高层旧定义

- 删除失效 `Theory/Structures/Basic.lean`。
- `Forest.lean`/`Tree.lean` 迁到 `Connectivity/Acyclic.lean` 与 `Theory/Trees/Basic.lean`，使用正式 `IsAcyclic/Connected`。
- `Eulerian.lean` 移到 general realized trail API 之上，predicate 必须含 `G.IsWalkIn w`；simple 版本可 derived。
- `Hamiltonian.lean` 同样先要求 realization，再谈 vertex coverage。
- `SimpleGraph_only/Bipartite.lean` → `Theory/Coloring/Bipartite.lean`。
- `Girth.lean`、`MooreBound/*` 只更新 imports/API，定理结构应保持。

### 9.5 package 与施工卫生

- `GraphLib.lean` 只导出可构建、相对稳定的 foundation/theory；不再导出 `UnionFind.Blueprint`。
- 各 `Basic.lean` 要么真的是 umbrella，要么改名；不能只有说明却让用户误以为已导出。
- CI 加 import-all 或逐 module 编译，避免默认入口掩盖失败文件。
- `Algorithms/Search` 与 `GraphTraversal` 合并为 `Algorithms/Traversal`。
- README 的目录说明更新。
- `UnionFind.Blueprint` 保持开发模块，完成后再拆 correctness/complexity 并加入稳定入口。

---

## 10. 依赖与施工顺序

以下顺序让后续 coding agent 几乎只需解决 Lean 工程问题，并允许括号内项目并行：

1. **冻结语义。** 确认本提案的 breaking edge-identity 决策、命名和 Mathlib pin；建立 import-all CI。
2. **重做 `Graph/Basic`.** 四图、actual `E(G)`、`IsLink/IsArc`、ext、显式 conversions。
3. **基础关系。** `Adjacency` 与 `Incidence`。（同时可无图依赖地搬迁 `VertexSeq/SimpleWalk/SimplePath/SimpleCycle`。）
4. **子图骨架。** `Subgraph` partial order、spanning、induced、compatibility。
5. **基础变换。** `Delete`、`Map`、`Reverse`。（三者可在 shared lemmas 稳定后并行。）
6. **组合与 realization。** 新 general `Walk`、`PathTrailCycle`、`InGraph/InDiGraph`；迁移 simple realized 层。
7. **邻域与有限数学。** `Neighborhood`、重做 `Finite`。
8. **度与计数。** `Degree`、`DegreeSum`；迁回 Girth/Moore helpers，并回归构建这条验证链。
9. **connectivity 规范层。** `Reachability` → `Connected/StronglyConnected` → `Acyclic/Tree`。
10. **附着数据。** `Weight/Basic` → `Weight/Walk` → `Network`。
11. **type-changing transformations.** `Contraction`，然后 directed `VertexSplit`。
12. **executable bridge.** `FiniteView` 与最少 concrete refinement；以 BFS skeleton 做编译级验证，但此阶段不必完成复杂度框架。
13. **恢复高层理论与算法。** Girth/Moore、BFS/DFS、SCC、shortest path、MST、flow；最后才扩展 constructors 和四图薄层覆盖。

每个阶段的退出条件：所有源码在 import-all 中编译；稳定模块无 `sorry`；至少有一个小的 compile-time usage test；umbrella 与文档同步。

---

## 11. 架构验收测试

这些是 API-level 场景，不要求现在实现完整算法。

### 11.1 induced subgraph 无 cast

```lean
variable (G : SimpleGraph α) (S : Set α) (u v : α)
#check G.induce S                         -- SimpleGraph α
#check (G.induce S).Adj u v
#check G.deleteVerts S                    -- SimpleGraph α
```

证明 `(G.induce S).Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S` 不应出现 `Subtype.val` 或 `cast`。

### 11.2 反复删除的集合律

```lean
(G.deleteVerts S).deleteVerts T = G.deleteVerts (S ∪ T)
(G.deleteEdges F).deleteEdges K = G.deleteEdges (F ∪ K)
```

对 general graph，`F/K : Set ε` 能精确区分平行边。

### 11.3 平行边赋权与 MST

给 `G : Graph α ε` 两条同端点边 `e₁ ≠ e₂`，可以表达：

```lean
e₁ ∈ E(G) ∧ e₂ ∈ E(G)
w e₁ < w e₂
G.deleteEdges {e₂}
IsMST w T
```

整个陈述不能把二者折叠成同一个 `Sym2 α`。

### 11.4 directed path reverse

```lean
h : G.IsWalkIn p
h.reverse : G.reverse.IsWalkIn p.reverse
```

general `DiGraph` 中 `p.reverse` 保持每个 edge identity；simple digraph 中使用反向 endpoint pairs。不能错误得到 `G.IsWalkIn p.reverse`。

### 11.5 BFS / DFS 输入桥

```lean
A : FiniteAdjView G
r := bfs A s
r.seen t ↔ G.Reachable s t
```

算法循环只枚举 `A.vertices` 与 `A.succ v`；correctness theorem 返回 ambient `α` 上的 realized `SimplePath` certificate，无嵌套 vertex subtype。

### 11.6 SCC 规范

```lean
G.StronglyConnected u v ↔ G.Reachable u v ∧ G.Reachable v u
```

`G.reverse` 下 SCC 不变；condensation 的 vertex carrier 可以是 SCC quotient/set，但普通 reachability statement 仍用 ambient vertices。

### 11.7 contraction 后修复路径

```lean
h : G.IsSimplePathIn p
p.vertices.map (contractMap S)       -- 总能表达
...cycleErase / loopErase...         -- 得到合法简路
```

API 不要求证明 `contractMap` injective，也不充斥等式 cast。

### 11.8 vertex splitting 与容量

对 `N : Network G R`、内部顶点 `v`，能构造 `G.splitVertex v`，原入边/出边 identity 通过 injection 保持，connector 获得 vertex capacity；守恒定理可以分别在 `v_in/v_out` 陈述。

### 11.9 weight transport

- 同 ambient induced/delete：原 `w` 直接复用；
- general `G.reverse`、vertex relabel：edge weight definitionally 不变；
- edge relabel/simple vertex relabel：一条显式 `transport`；
- `pathWeight` 对 append 是和，对 reverse 在相应 transported weight 下相等。

### 11.10 residual network

从 simple input 转入 identity-sensitive `DiGraph` 后，原 arc、反向 residual arc、已有 antiparallel arc 可同时存在并被分别赋 capacity/cost。若这个场景仍发生 identity collision，则基础设计不合格。

### 11.11 当前回归链

迁移后以下链应完整无 `sorry` 编译，且公开定理只做局部名称调整：

```text
VertexSeq → SimpleWalk → SimplePath → SimpleCycle
→ InSimpleGraph → Girth → MooreBound (odd/even)
```

这是第一优先级回归测试。

---

## 12. 暂缓决定的问题

1. **统一 GraphLike / incidence hierarchy。** 等 Mathlib 方向稳定或 GraphLib 出现至少三个真正共享客户端后再评估。
2. **loop 的两个可区分 half-incidences。** 当前 degree 可用 `incidence + loopSet` 正确计数；只有 non-backtracking、embedding 或 incidence-level walk 真正需要时才引入 dart/incidence identity。
3. **general graph 是否直接 alias Mathlib `Graph`.** 当前建议语义适配并提供 adapter；待 namespace、CSLib upstream 和 directed counterpart 稳定后再决定直接复用。
4. **arbitrary vertex splitting。** 初始只做 directed in/out split；incident-edge arbitrary partition、k-way split 后置。
5. **contraction 的完整代数律和 minor hierarchy。** 先做 `contractSet/contractEdge` 与必要 transport，再由 minors 客户驱动。
6. **无限度的 `ℕ∞` API。** 等 infinite graph 下游出现再加；初始避免 `Nat ncard` 的错误总化。
7. **weighted-data 的 bundled wrapper。** 先用 total functions + namespace API；若多份数据组合和 instance inference 反复造成痛点再 bundle。
8. **最短路数值抽象。** `ENNReal`、`WithTop`、ordered additive monoid、negative cycle 等由具体算法决定，不进基础 representation。
9. **完整 executable representation 与复杂度模型。** 现在只定 view/refinement 边界；array layout、hash assumptions、operation costs 后置。
10. **component quotient 的公开 carrier。** 普通 API 先以 `Set α` 为主；需要 canonical quotient 的高阶理论可内部使用 `V(G)` subtype。
11. **`GraphLib` 还是 `Cslib` namespace。** 当前 CSLib pin/main 没有既有 graph foundation，但 upstream 前必须统一；这不应阻塞本地数学架构。
12. **与实验 GraphLike 的 adapter。** 只在相关 Mathlib PR 合并后实现，不为 open draft 提前锁定 representation。

---

## 最终建议

下一 coding 阶段不应从 BFS 或 degree 的局部补丁开始，而应先完成一个短而决定性的 foundation slice：

```text
actual edge identity Basic
→ Adjacency/Incidence
→ Subgraph/Delete/Map/Reverse
→ general realized Walk
→ Finite/Neighborhood/Degree
```

同时原样保护 simple walk—cycle—Moore 回归链。完成这条 slice 后，BFS、SCC、weighted shortest path、MST 和 flow 将共享同一组清楚的数学对象，而不必各自重新发明“边是什么”“子图是否换类型”“权重索引什么”和“算法如何枚举邻居”。
