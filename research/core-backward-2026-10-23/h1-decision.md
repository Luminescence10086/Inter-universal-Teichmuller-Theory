# H1 决策：环境范畴与商层级

日期：2026-10-23。状态：**决策记录**（原文层面），非 Lean、非 fact-tree。依据
`research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt`（SHA256 `70a618ad…b715`）与
`handoffs/core-backward-2026-10-23/M1/`。本文件同时**更正**两处先前说法（M1 的一条发现、与设计稿 §1′(a)(b)）。

## 结论一：环境范畴存在，且原文已声明

先前（M1 发现 #1，及设计稿 §1′(b)）说"16 个节点画成同一类、而同一环境范畴服务两排这一点原文未声明"。**这一条不成立。**
原文 9287–9296 明说：

> "in summary, the F⊩▶×μ-prime-strips n,mF⊩▶×μ_LGP, n,mF⊩▶×μ_lgp that appear in the Θ×μ_LGP-,
> Θ×μ_lgp-links of Definition 3.8(iii), were constructed from the F⊩▶×μ-prime-strip n,mF⊩▶×μ_env and
> related to this F⊩▶×μ-prime-strip n,mF⊩▶×μ_env via the lower horizontal arrows of the above commutative
> diagram"

且 8560、8587 反复称这些对象为"the F⊩▶×μ-prime-strips that appear in the Θ×μ_LGP-link"。
**故环境范畴 = `F⊩▶×μ-prime-strips`，原文声明过，不需要另立范畴。**

两排的差别只是 theater 索引：下排 `(n,m)`，上排 `(n,◦)`；而 9265–9266 说明 `n,◦` 是
`n,◦HT^{D-Θ±ellNF}`（Proposition 3.10(i)）的缩写，即**整条纵线**。第一条竖箭的余域"includes an argument
`†D>`"（9267–9269）也是这个缩写的组成部分。

**仍未定的（保留 `UNRESOLVED`）**：`(n,◦)` 到底是"一个由整条纵线构成的对象"，还是"一个以 m 为参数的族"。
原文用缩写，不区分这两种读法。形式化时必须显式选一种（W1 的索引槽），并证明读数与所选读法无关；不能默认。

## 结论二：商是范畴层的"形式商"，不是集合层等价关系

原文 8607–8629 是完整的对照句，先前只引了半句，容易读反。其结构是：

> "just as the tensor-power-twist indeterminacies of (sQ3) … and the indeterminacy with respect to …
> arbitrary iterates of the log-link of (sQ4) may be understood as **"formal, or stack-theoretic/
> diagram-theoretic, quotients" [i.e., as opposed to "coarse/set-theoretic quotients" given by
> set-theoretic invariants such as the log-volume — cf. (Ob9-1)]**, the pair consisting of
> (⊼fQ₁) such a category of "local-global ⊼-collections" and (⊼fQ₂) the analogous category of
> "local-global collections" … may also be regarded as the **"formal, or stack-theoretic, quotient"**
> corresponding to the operation of considering **"⊼fQ₂ modulo ⊼fQ₁"**."

由此得到三条不可混用的层级事实：

1. **形式商的对象是两个范畴之间的商操作**：`⊼fQ₂`（普通 local-global collections）**modulo** `⊼fQ₁`
   （其 ⊼-版本，即带 structure poly-morphism 的 collections）。它不是"在一个集合上取等价类"。
2. **log-volume 被原文明确列为"coarse/set-theoretic"影子**。也就是说：要标量化，必然经过一次粗化；
   这正是 iQ5 之后"只剩数值"的结构性原因。
3. **`⊼lc₁` 的 structure poly-morphism 本身仍是集合层的**：8566–8571 把它定义为
   `Aut(det^{⊗M}(φ(P_B)))`-orbit of a linear morphism（local Frobenioid 里的一个 Hom-集）。集合层的 orbit 是
   **这一层的正确构造**，不是错误；错的是把它当作整个商。

把这三条合起来，先前"M1 说集合层 orbit 与 stack 商不符"的说法需要精确化：**两层都存在，且是不同层的对象**——
集合层 orbit 是 `⊼fQ₁` 内部的对象定义，形式商是 `⊼fQ₂ modulo ⊼fQ₁` 这个范畴层操作。设计稿 §1′(a) 把它们并列成
"哪个才是对的"，是个假二分；真正的要求是**两层都要有，且不能在层间偷换**。

## 对联合见证类型（W1–W6）的约束

| 槽 | 据此定下的约束 |
|---|---|
| W1 索引 | 必须显式选定 `(n,◦)` 的读法（单对象 / 族），并证明读数与选择无关；这是新增的证明义务 |
| W2 | 两层都要：`⊼fQ₁` 侧的 orbit 对象（集合层，`Aut(det^{⊗M}(φ(P_B)))`-orbit）**与** `⊼fQ₂` 侧未 ⊼-化的 collection，以及包含 `⊼fQ₁ ⊆ ⊼fQ₂` |
| W3 | 不是"沿 orbit 不变"，而是**沿 `⊼fQ₂ modulo ⊼fQ₁` 这个形式商不变**；且必须标明：一旦取 log-volume，就已经落到 coarse 层，不可再声称保留了形式商的关系 |
| W5 | 读数分两层：形式商层面的"读数相容"，与 coarse 层的数值。`vQ = q₀` 只能是在 coarse 层陈述的等式，不得反推形式商层的同一性 |
| W6 | `realisation` 只给 coarse 层的落点条件（M3：F3 对 11 项全 false），与形式商无关 |

一句话总结 H1：**环境范畴不用另找；要修的是商的两层结构——`⊼fQ₁` 里的 orbit 与 `⊼fQ₂ modulo ⊼fQ₁` 的形式商
必须都在，且 `log-volume` 一出现就意味着已经粗化。**

## 下一步（K4）

M3 已确定 11 个接口没有一个要求"合法执行"。K4 要补的是**执行来源**：一个对象，其存在性附带"由某个具名算法
执行得到"的证明，而不是"落在某个 hull 里"。K4 与 H1 的接口是：执行来源只作用于 `⊼fQ₂` 侧（未 ⊼-化）的对象；
`⊼fQ₁` 的 orbit 是它的结构，不是它的来源。
