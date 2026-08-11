# 证明简化行动指南（给 agent）

面向对象：被指派去缩短 `GraphLib/Theory/Structures/` 下某个 `.lean` 文件中证明的
自动化 agent。本文自成一体，读完即可动手，不需要其它文档。

**任务**：语句集合完全不变，只让证明体变短。
**成功标准（按优先级）**：① 全链 `lake build` 干净（0 error、0 新增 warning）；
② 更短；③ 仍然可读——人能看出数学结构在哪一步；④ 编译不明显变慢。
只满足 ② 而牺牲其余的改动是**失败**的改动。

目标不是「所有证明变成一行 `grind`」，而是：**人负责证明的算法结构和关键不变量，
`simp` 负责归一化，`grind` 负责局部逻辑闭包。**

---

## 1. 硬性约束

违反任意一条，改动作废：

1. **不改语句。** 不得修改任何 lemma/def 的语句、名字、参数、隐式性、类型类假设。
   `git diff` 中除文档注释外只应出现证明体的变化。
2. **不动 `@[simp]` / `@[grind]` 属性。** 它们是全局的。**真实教训**：给
   `VertexSeq.length_le_one_of_closing_edge_mem'` 加 `@[grind →]` 之后，`grind` 会在
   **每一处 `Sym2` 成员关系**上实例化它并钻进 `Quot`/`Sym2.Rel` 内部，把毫不相关的
   `SimpleCycle.arcs_nodup` 当场弄挂。**想加属性 → 写进报告，交人类决定。**
3. **不改 `abbrev` 为 `def`。** `abbrev` 自带 `@[reducible]`，大量 `rfl` 证明和 defeq
   elaboration 靠它工作。（本项目已经在 `SimpleWalk`/`SimplePath`/`SimpleCycle` 里用
   `attribute [simp, grind] ...` 让 simp/grind 能穿透这些 accessor —— 已完成，别再动。）
4. **不留 `sorry`/`admit`/`native_decide`；不提高 `maxHeartbeats`/`maxRecDepth`。**
   需要提高上限才过 = 你走的是搜索爆炸那条路，换思路。
5. **不确定就保留原证明。** 一个 20 行的正确证明永远优于一个你没验证过的 3 行证明。
6. **新增辅助引理**：只有在任务明确允许时才加；加则**不带属性**，放在被引用处之前，
   并在报告里单列。

---

## 2. 工作循环

### 2.1 准备

```bash
lake build          # 一次；之后单文件检查才快
```

### 2.2 选目标

**只处理证明体 ≥ 6 行的证明**，或有下列气味的：`simp only [...]` 长列表、多层嵌套
`have ... := by ...`、手写 `List.getElem_append_left` 这类底层引理、明显在重复某条已有
引理。已经是 `fun_induction ... <;> grind` 或单行 `grind` 的**一律跳过**。

先列出候选清单和原行数，最后要写进报告。

### 2.3 单条引理隔离迭代

不要每改一行就重编整个文件。把目标引理复制到 scratch 文件单独迭代（一条 3–8 秒，
整文件约 10 秒）：

```lean
import GraphLib.Theory.Structures.VertexSeq.Subseq   -- 目标所在模块

variable {α : Type*}
namespace VertexSeq

-- ⚠️ 目标引理自带 @[grind]/@[simp] 时必须先摘掉属性，
-- 否则 grind 会用「它自己」把目标关掉，得到假通过。
attribute [-grind] nodup_splitAt

@[grind] lemma nodup_splitAt_试 ... := by
  ...

end VertexSeq
```

```bash
lake env lean /abs/path/T1.lean     # 必须在项目根目录下运行
```

**隔离迭代的两个必踩坑：**

- **scratch 环境比真实位置「富」。** scratch import 的是整条链，环境里有一堆原文件在
  那个位置**还看不到**的 `@[grind]` 引理，`grind` 会顺手用掉。真实教训：`nodup_zip` 在
  scratch 里一行通过，贴回 `MapZip.lean` 就失败——因为 scratch 多 import 了
  `Edges`/`Subseq`。**每条改完必须贴回原文件重编。**
- 新证明不能引用原文件中位于目标**之后**的引理（循环依赖），贴回去才会暴露。

### 2.4 预算

每条引理**最多 4 次实质不同的尝试**（换 `grind [...]` 里一两个名字不算「实质不同」）
或 10 分钟，先到者为准。到点未过 → **恢复原证明**，报告里写一行失败原因。

不要陷入「再往 `grind [...]` 里加个引理试试」的死循环——这是本任务最大的时间黑洞。
每次失败先回到第 3 节判断缺的是哪一类结构。

### 2.5 收尾

```bash
lake env lean <目标文件>     # 0 error、0 新增 warning
lake build                   # 必须；见下面的验证陷阱
```

---

## 3. 决策树：拿到一个长证明先想什么

按顺序问，**不要跳过 (a) 和 (b)**。

### (a) 它是不是某条已有引理的推论？

**最大的简化从来不是调 `grind`，而是消除掉整个归纳。** 动手前先把本文件（和 import
的模块）的引理名扫一遍。

实例：`exists_prefixUntil_pred_eq_head_or_tail` 原本 37 行结构归纳。它要找的「第一个满足
`P` 且不是 head 的顶点」，恰好就是「把不满足该条件的顶点 drop 光之后剩下的 head」——而
`dropWhile` 的三条引理已经给出了全部性质。归纳整个消失，**37 → 6 行**：

```lean
  classical
  set p : α → Prop := fun z => ¬ (P z ∧ z ≠ q.head) with hp
  have h : ∃ z ∈ q.toList, ¬ p z := by grind
  refine ⟨_, dropWhile_subset q p h _ (head_mem _), ?_, ?_, ?_⟩ <;>
    grind [head_dropWhile_not, eq_head_dropWhile_or_pred_of_mem_prefixUntil]
```

（语句没有 `[DecidablePred P]`？用 `classical` 现取。witness 用 `_` 让 `refine` 推。）

### (b) 有没有「喂全定义」？

**在放弃、改用手写结构之前，务必先试一次**：把目标里**出现的每个定义**（`toList`、
`head`、`dropHead`、`reverse`、`arcs`…）加上**跨越那一层的核心 `List` 引理**
（`List.getElem_append_left`、`List.nodup_append`、`List.drop_append`…）一次性喂进
`grind [...]`，配 `induction w <;>`。

`grind` 不会去展开一个没被点名的定义，但只要点名了，它对 `getElem`/`drop`/`Nodup`
这类列表推理其实相当强：

```lean
-- 24 行手写 calc + 三个 getElem 下标证明 → 3 行
lemma head_dropHead_eq_getElem_one (w : VertexSeq α) (h : w.length ≠ 0) :
    w.dropHead.head = w.toList[1]'(by rw [length_toList]; omega) := by
  induction w <;>
    grind [toList, head, dropHead, length_toList, List.getElem_append_left,
      head_dropHead_cons, eq_singleton_of_length_zero]
```

同一手法：`dropTail_reverse` 12 → 2，`toList_suffixFrom_eq_drop` 30 → 2，
`length_le_one_of_closing_edge_mem` 14 → 1。
**「先加结构」的直觉经常是错的——先加定义。**

### (c) 归纳原理和递归函数对得上吗？

对 `prefixUntil`/`suffixFrom`/`splitAt`/`dropWhile`/`zip` 这类**带条件、带依赖证明参数**
的递归函数，用 `fun_induction f w v h <;> grind`，不要用 `induction w generalizing v`。
前者按函数方程分支，分支条件和归纳假设已经是 `grind` 想要的形状。

### (d) 结论是 `∃`，不同情形要不同 witness 吗？

`grind` 不做算法性选择。人写 `by_cases` + 显式 witness，剩下的成员关系、否定存在式、
递归展开交给 `grind`。

### (e) 全称假设是不是没被 E-matching 实例化？

有 `hL : ∀ p ∈ L, p ⊆ w` 但 `grind` 推不出 `p ⊆ w`——先问：上下文里真的有 `p ∈ L` 这个
ground term 吗？没有的话 `grind` 不会为了触发 `hL` 而主动去证 `p ∈ p :: ps`。直接喂实例：

```lean
grind [splitAt.appendToLast, mem_cons, hL p (by simp)]
```

**不要靠反复加 `List.mem_cons` 解决**——缺的不是定理，是具体实例。

### (f) 需要跨抽象层的桥梁不变量吗？

不要让 `grind` 自己把两条高阶性质拼起来，人写一条有名字的 `have` 拼好再交给它。
`nodup_splitAt`（26 → 7）：

```lean
  | cons q x ih =>
      have havoid : ∀ s ∈ q.splitAt v, x ∉ s := fun s hs hsx =>
        hw.2 (splitAt_subset q v s hs x hsx)
      have hkey := nodup_appendToLast (q.splitAt v) x (ih hw.1) havoid
      grind
```

关键是 `hkey`：把引理**在需要的那组参数上实例化好**。（`x = v` 分支里 `splitAt` 展开出的
是 `appendToLast _ v`，但 `grind` 的同余闭包会把它和 `appendToLast _ x` 认同，
**不需要**先 `by_cases` + `subst`。）

### (g) 同一个事实算了几遍？

长证明里最常见的肥肉。`divergenceVertex_core` 里「路径的末顶点 = 顶点表最后一个元素」
被推了 4 遍；抽成两条共享 `have` 后，三段各塌成 2–3 行（**71 → 52**）。

### (h) 两段代码是不是同构的？

`p` 和 `q` 的对称样板、`edges`/`arcs` 的对称样板——抽成一条通用引理，调用处各变一行。
例：`hd₁`/`hd₂` 那 8 行 → `VertexSeq.head_dropHead_of_toList_eq_cons_cons`（6 行）+ 两个
一行调用。**注意约束 6：新增引理要先获批。**

---

## 4. `grind` 使用细则

- **递进顺序**：裸 `grind` → `grind [一两条接口引理]` → 「喂全定义」(3b) → 再考虑加结构。
- **不要放已带 `@[grind]` 的引理进 `grind [...]`**，编译器会报 `parameter is redundant`。
  写之前先 `grep '@\[grind' <file>`。
- **`grind!` 不是默认的下一步。** 它更激进地展开生成项；在量词与递归定义交织的场合只会
  把搜索空间放得更大。
- **一次 `grind` 只跨一个抽象层。** 同时要它理解递归定义 + 列表实现 + 子集量词 + 存在
  见证 + 归纳假设，即使侥幸通过也很脆。
- **分工**：`simp [定义, 分支条件] at h` 做确定性归一化；`grind [少量接口引理]` 做逻辑闭包。
- **找不到引理名**：`exact?` / `simp?`。别凭记忆猜（`List.head_cons_tail` 其实叫
  `List.cons_head_tail`）。

---

## 5. 读 `grind` 的失败信息

失败时会打印 `[grind] Goal diagnostics`（`[facts] Asserted facts` + `[eqc] True propositions`）。
三种症状，处方**相反**，别诊断错：

| 症状 | 诊断 | 处方 |
|---|---|---|
| 需要的命题**完全不在** facts 里 | 缺展开/缺引理/缺量词实例 | **加**：定义、接口引理，或具体实例 `h a (by simp)` |
| 需要的信息**都在** facts 里但没连起来 | 缺中间不变量 | 加一个有名字的 `have`（3f） |
| facts 极长、大量无关构造子拆分、或 `maximum term generation` | **搜索爆炸** | **减**：缩短 `grind` 列表，停止展开强定义，手写关键桥梁 |

第三种最容易被误诊成第一种。判断标志：错误里冒出**你根本没在用的引理**的实例，或出现
`w_1 w_2 w_3 v_1 v_2 ...` 一长串 skolem 变量——那是它在瞎拆，**这时加引理只会更糟**。

---

## 6. 验证陷阱（吃过亏，务必遵守）

1. **`lake env lean <file>` 读的是 import 的 `.olean`。** 只要你改过**上游源文件**，就必须
   先 `lake build`，否则你是在一个**过期环境**里测试，「通过」是假的。
2. **`lake` 的错误格式是 `error: path.lean:12:3: ...`**（`error:` 在**前面**）。用
   `grep '\.lean:[0-9]*:[0-9]*: error'` 会**漏掉全部 lake 错误**，得到假的「零损坏」。
   正确：`lake build ... 2>&1 | grep '^error: '`。
3. 每个文件收尾必须跑一次**全链** `lake build`（含下游模块），不能只看单文件。

---

## 7. 已知的墙：`grind` 过不去的三类

遇到这三类，**别浪费预算**，直接保留人写的结构：

1. **归纳假设的前提是一个 ∀。** `grind` 不会自己造出这个前提喂给 `ih`。
   （`VertexSeq.nodup_append`：`ih` 需要「更小的 q 上的不交性」，试过 4 种写法全失败，
   必须人写 `have hkey := ih hq.1 (fun x hx hq' => hdisj x hx (by grind))`。）
2. **需要跨层桥梁不变量。**（`nodup_splitAt`，见 3f。）
3. **`Sym2` / `Quot` 内部。** `Sym2.eq_swap` 是置换型重写规则，喂给 `grind` 只会让它绕圈。
   必须先 `rw [h, Sym2.eq_swap] at ha` 把项摆成引理要的形状，再按名字应用。

---

## 8. 类型论/tactic 层面的硬障碍（不是样板，别删）

- **`omega` 与 `let` 不对付。** `let lp := p.vertices.toList` 之后，`have : 0 < lp.length`
  与目标里被 zeta 展开的 `p.vertices.toList.length` 在 `omega` 眼里是**两个原子**。
  → 别写 `lp[lp.length - 1]'(by omega)`（会失败），让 `getElem` 用默认的 `get_elem_tactic`
  （它先跑 `simp`）反而能过。
- **`simp` 改写不进依赖证明参数。** `p.vertices` 出现在 `suffixFrom p.vertices y hy` 里时
  改写不动（motive 问题），于是 `p.vertices.length` 与 `(↑↑p).length` 分裂成两个原子。
  → **凡是要喂给 `omega` 的局部 `have`，类型统一写成底层 `VertexSeq` 形式**
  （`have hle : P.length ≤ p'.length := ...` 这样显式标注）。
- **不能从 `∃` eliminate 到 `Type`**（`propRecLargeElim`）。产出数据的 `def`（如
  `buildOfTwoPaths` 返回一个装着 `SimpleCycle` 的结构）里，那些「重述 spec 的完整类型 +
  `by obtain ...; simpa`」的 `have` 块**是唯一的合法写法**，不是样板，删不得。
- **`change` 有时是承重墙。** 它把目标变成定义展开后的形状（如 `glue` 的 `if` 分支），
  后续 `rw` 才能匹配 pattern。删 `change` 会让 `rw` 找不到 pattern。

---

## 9. 性能红线

- 改之前先记 `time lake env lean <file>` 的基线。
- 单条证明编译时间不应超过原来的 2 倍；整文件不得慢 20% 以上。
- 一行 `grind` 跑 30 秒，比十行可读的结构化证明跑 2 秒**更差**。慢就拆成
  `simp [...]` + `grind [...]`，或把某个 `have` 补回去。

---

## 10. 报告格式

**覆盖率要求（不可省略）**：表里必须列出该文件**每一条 ≥6 行的证明**，每条都要有明确
结局——「已缩短」「尝试 N 次失败，原因 X」「跳过，原因 Y」。**不允许静默跳过任何一条，
更不允许静默跳过整个文件。**（真实教训：一次施工里 `Edges.lean`（322 行）和 `MapZip.lean`
被整个跳过且报告只字未提，而事后发现 `Edges` 里最长的两条各自一行 `grind` 就能过。）

| lemma | 原行数 | 新行数 | 关键手法 | 备注 |
|---|---:|---:|---|---|
| `nodup_splitAt` | 26 | 7 | 桥梁 `have` (3f) | |
| `toList_suffixFrom_eq_drop` | 30 | 2 | 喂全定义 (3b) | |
| `nodup_append` | 11 | 11 | — | 4 次尝试失败：IH 前提是 ∀（第 7 节第 1 类） |

**剩余长证明清单（不可省略）**：改完后**仍然 ≥6 行**的证明，按行数降序，每条一句话说明
**为什么它必须这么长**。这是人类判断「还值不值得再来一轮」的唯一依据，比缩短了多少行更
重要。

外加：基线/改后编译时间；**给人类的建议**（例如「建议给 `X` 加 `@[grind]`」「建议新增
辅助引理 `Y`」）——建议归建议，不要自己动手（约束 2、6）。

---

## 11. 反模式清单

出现即视为跑偏，立即停下：

- 往 `grind [...]` 里枚举所有看起来相关的引理，撞运气；
- 用 `grind!` / 提高 heartbeats 让一个爆炸的搜索勉强通过；
- 为了行数，把可读的结构化证明压成一个跑很慢、别人看不懂的单行 `grind`；
- 悄悄放宽 lemma 语句（加 `DecidableEq`、加额外假设）来让证明好写；
- 在 scratch 里验证通过就当完成，没有贴回原文件 + `lake build`；
- 改了 `@[simp]` / `@[grind]` 属性，或把 `abbrev` 改成 `def`；
- 用错误的 grep 模式看 `lake build` 输出，得到假的「零错误」；
- 在一条引理上耗超预算，还不肯回退。
