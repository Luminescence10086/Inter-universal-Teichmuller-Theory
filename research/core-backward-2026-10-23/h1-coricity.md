# H1 附：vertical coricity 给出的同构类

日期：2026-10-23。状态：**来源结论**，非 Lean、非 fact-tree。补齐 `h1-decision.md` §结论一′ 留下的第一项开口
（"vertical coricity 具体给出哪一类同构"），并顺带回答第二项（"是否隐藏一个选择"）。

## 结论

**同构类是 full poly-isomorphism，而 poly-isomorphism 是"同构的轨道"。因此 `(n,◦)` 由整条纵线确定时
不需要挑选任何一个同构——没有隐藏的选择。**

## 原文依据（逐条带行号）

1. **Theorem 1.5(i)（垂直共核性）**，txt 2881–2889：

   > "The vertical arrows of the Gaussian log-theta-lattice induce **full poly-isomorphisms** between the
   > respective associated D-Θ±ellNF-Hodge theaters … → `n,mHT^{D-Θ±ellNF}` ∼→ `n,m+1HT^{D-Θ±ellNF}` ∼→ …
   > [cf. Proposition 1.3, (ii)]. Here, **n ∈ Z is held fixed, while m ∈ Z is allowed to vary**."

   即：方向是 n 固定、m 变化；联系它们的不是某个同构，而是 **full poly-isomorphism**。

2. **poly-isomorphism 的定义**，txt 2005–2007：

   > "a poly-isomorphism [i.e., **an orbit of isomorphisms** with respect to the independent actions of
   > {±1} on each of the direct factors that occur in the construction of [AbsTopIII], Proposition 5.8, (v)]"

   所以 poly-isomorphism **不是**"某个被选中的同构"，而是**一族同构的轨道**；"full" 指该轨道不再受额外限制，
   即全部结构相容同构。**存在一个 poly-isomorphism 不需要选择**——轨道是典范给出的。

3. **Remark 3.8.2（把上述结果搬到 LGP/lgp 情形）**，txt 6930–6939：

   > "One verifies immediately that the main results obtained so far concerning Gaussian log-theta-lattices —
   > namely, Theorem 1.5, Proposition 2.1, Corollary 2.3 … and Proposition 3.5 — generalize immediately
   > [indeed, "formally"] to the case of LGP- or lgp-Gaussian log-theta-lattices. Indeed, the substantive
   > content of these results concerns portions of the log-theta-lattices involved that are **substantively
   > unaffected** by the transition from "Gaussian" to "LGP- or lgp-Gaussian"."

   这正是 8869–8873 定义 `n,◦HT` 时引用的依据：垂直共核性在 LGP 情形"形式上"照搬。

## 对 W1 的两处修正

**(a) 不变性的对象是"轨道"，不是"某个同构"。** 原先写"读数必须与所选同构无关"仍然偏弱：正确要求是读数在
**整个 poly-isomorphism 轨道上为常数**（等价地：对一切相容自同构不变）。玩具里 `hasSum_perm` 证的是"对任意
重排不变"，即在一个置换群轨道上为常数——正是这个形状，只是把"相容自同构"换成了"重排"。

**(b) 先前的"是否隐藏一个选择"这一顾虑解除。** poly-isomorphism 是轨道，取轨道不需要选代表；因此把 `(n,◦)`
说成"由纵线确定、只到同构为止"并不隐含额外数据。真正需要的仍是 (a) 的不变性证明，而不是"选一个代表再验证"。

## 附：落到 `F⊢×μ`-prime-strips 后，轨道**不是** full

上面说"读数须在整条轨道上为常数"，但**轨道的实际大小要分两层看**，否则会把义务写强。原文
txt 2983–2995（Theorem 1.5(iii) 的 bi-coric 段）明确：

> "… the collection of isomorphisms that constitute the poly-isomorphisms of F⊢×μ-prime-strips of the
> **first line** of the display is, in general, **strictly smaller** than the collection of isomorphisms
> that constitute the poly-isomorphisms of F⊢×μ-prime-strips of the **second line** … [cf. the existence
> of non-scheme-theoretic automorphisms of absolute Galois groups of MLF's …]; the poly-isomorphisms of
> F⊢×μ-prime-strips of the **second line** are **not full**."

其中第一行是垂直方向的链 `F⊢×μ_△(n,mD≻) → F⊢×μ_△(n,m+1D≻) → …`，第二行是水平方向的链
`F⊢×μ_△(n,mD⊢△) → F⊢×μ_△(n+1,mD⊢△) → …`（2962–2982 的 display）。据此：

1. **Hodge theater 层**：垂直箭头是 **full** poly-isomorphisms（Theorem 1.5(i)，2881–2889）。
2. **诱导到 `F⊢×μ`-prime-strips 层**：得到的 poly-isomorphisms **不是 full**；而且垂直那一条还**严格小于**
   水平那一条。不是 full 的原因被点名了：[IUTchII] Remark 1.8.1（原文还给了一条旁证：MLF 的绝对 Galois 群
   存在非概型自同构，见 [AbsTopIII] §I3）。

**对 W1 的净效果**：不变性义务是在**这条具体的、较小的轨道**上取值恒定，而不是在"全部相容同构"上。
这比先前写法**更容易**满足，也说明"读数沿 full poly-isomorphism 不变"是**过强**的表述、不应采用。
若后续把 W1 的玩具升级到真实对象，须先固定是哪一层（Hodge theater 还是 `F⊢×μ`-prime-strip），
因为两层的轨道不同。

## 仍然不做的（诚实边界）

- 本文件读了 IUT III 的 `Theorem 1.5(i)`、`(iii)` 的 bi-coric display 与轨道大小的比较（2962–2995）、
  `Remark 3.8.2`、`Remark 3.8.3`、`Proposition 3.9` 附近，以及 poly-isomorphism 的定义处（2005–2007）。
  **未读**：[AbsTopIII] Proposition 5.8(v)（`{±1}` 作用的来源，本卷只引用）；[IUTchII] Remark 1.8.1
  （"第二行不是 full"的依据所在）；也未核 `Ψcns` 的那组同构（[IUTchII] Corollary 4.5(ii)）在
  `(n,◦)` 对象上如何逐步落地。
- "full" 的"全部相容同构"是**文本用词的自然读法**（与 2005–2007 的"轨道"定义合起来），本卷没有单独给
  "full" 下定义式；若后续需要，应回到 [AbsTopIII] 或 IUT I 的定义处核对，而不是把本文件的转写当定义。
- 上述任何一条都不构成对 `(n,◦)` 存在性的新证明；本文件只确定"确定到哪一类同构为止"，并把它转成 W1 的义务形状。
