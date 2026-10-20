# 第三轮语义审计：G03 的最小真实局部接口

日期：2026-10-16（Asia/Shanghai）。研究对象：第二轮的 M4/M5/T5。状态：**来源审计与未形式化假说**；没有修改 Lean 文件或验证器，没有把本报告的数学解释纳入 fact-tree。

## 1. 相比第二轮的新发现

本轮读到比“可能像”这个短语更明确的原始结构：

- **Ism 有强定义。** IUT II Example 1.8(iv), p.39：它是 G-equivariant ind-topological module automorphisms；对每一个 open subgroup H≤G，保持由 O×(G)^H 的像给出的 lattice。
- **Kummer 族确有 orbit 定义。** IUT II Definition 4.9(i), p.154：×μ-Kummer structure 是 Ism-orbit；也用所有 H 对应 lattices 的数据刻画该 orbit。不能把这些原文表述成“完全没有定义允许族”。
- **Ind3 不应硬塞进群作用。** IUT III Theorem 3.11(ii), p.156 把它描述为随 vertical parameter m 变化的 upper-semi-compatible inclusions/surjections。G03 需要的只是某一具体 Kummer 像后的一条 Ind1/Ind2 路径，不必先证明 Ind1/2/3 的完整群作用闭包。
- **保 p 的整数幂格层与保精细 valuation 是不同命题。** 对有限 log-lattice 的保持可以导出整数幂层保持；进一步联系 ord_p 需要 lattice 与估值球的对应。小分歧情形只能据此得到相应的粗整数层不变量，不能自动得到 ord_p 逐值相等。

原来源链接：[IUT II](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf)，[AbsTop III](https://www.kurims.kyoto-u.ac.jp/~motizuki/Topics%20in%20Absolute%20Anabelian%20Geometry%20III.pdf)。上述是对已读文字的定位，不是本项目认证这些理论正确。

## 2. 本轮新增缓存、版本和实际阅读

新增到 research/round3-source-cache/：

| 文件 | 首面版本 | 页数 | SHA256 |
|---|---|---:|---|
| iut-II-official-retrieved-2026-10-16.pdf | December 2020 | 174 | 180bfa6aaddc4ae37af37acaad51f61e0a47b33b8255ad3169e28a970ae39b7c |
| abstop-III-official-retrieved-2026-10-16.pdf | November 2015 | 164 | e8115df30a86dea26e2ebf60cb333558ff28fe3e4d57017a80421787b53421a9 |

已用 pypdf 提取全文为缓存文本，实际精读范围：

- IUT II：Example 1.7 pp.32–35；Example 1.8 pp.36,39；Corollary 4.5 pp.131–132；Corollary 4.6 pp.137–139；Definition 4.9(i) p.154。
- AbsTop III：Proposition 5.7 pp.137–139；Proposition 5.8(i)–(iii) pp.139–140；其后相关检索片段仅作定位，未重建证明。
- 复用第二轮固定字节的 IUT III：Definition 1.1 pp.26–28；Prop.1.2(vi) p.32；Remark 1.2.2 p.36；Prop.3.2 pp.97–99；Remark 3.9.5 pp.131,134,140–141；Thm.3.11 pp.153–159；Remark 3.11.1 pp.159–163；Cor.3.12 pp.173–175。
- 复用 IUT IV：Prop.1.2 p.10、Prop.1.4 p.13、Theorem 1.10 proof pp.26–28。
- 复用 Urahigashi tag v0.8.0 的固定原稿，重点 §4 Lemmas 3–4。
- 视觉核对 IUT II p.39 与 AbsTop III p.139，确认 Ism 的全称 H 量词及 reconstruction diagram。临时渲染图已删除。
- 没有运行下载内容的可执行代码。

所有原稿页码均为预印本印刷页码。本轮没有声称读完新增论文的全部证明。

## 3. Ism → 有限局部线性壳保持：M4 的真实接口

### 3.1 不应丢掉的 H 量词

令 G 为一个与有限扩张 k/Q_p 的 absolute Galois group 同构的群。按照 IUT II p.39，Ism(G) 的一个元素不只是 base field 上的一个矩阵；其控制的是整个 ind-module，以及所有 open H≤G 的相容 lattice。

建议的具体化义务（尚未形式化）：

```text
U(G)       : ind-topological G-module corresponding to O×μ(G)
for every open H ≤ G:
  V_H      := U(G)^H after logarithmic realization
  L_H      := image of O×(G)^H under quotient and log
for every s ∈ Ism(G):
  s(V_H) = V_H
  s(L_H) = L_H
```

这里必须区分“单位先取 H-invariants 再映到 quotient”和“quotient 的全部 H-invariants”。原定义指定的是前者的像，不能把二者不经证明地相等化。

取 H=G 后，候选有限实现应给：

```text
V_G ≃ k as topological additive groups
L_G ↔ log_p(O_k^×)
Ism(G) → {Q_p-linear equivalences T:k≃k | T(L_G)=L_G}.
```

从 continuous additive map 到 Q_p-linear map 还需要一个系数兼容引理：先得 Q-linearity，再由连续性与 Q 在 Q_p 中稠密扩展。不能仅因原文写“module”就省略这一步。

AbsTop III Proposition 5.8(i)–(iii) 给局部群论重建、log-shell 和 log-volume；原文特别区分可构造的加性/测度对象与不可由此直接恢复的 field structure。因此，比较得到的线性映射不应被无端升级成环或域自同构。

### 3.2 真实 Ism 与短文 A(k) 的量词方向

短文使用的 A(k) 是“所有保有限 log-lattice 的 Q_p-linear automorphisms”。本轮来源支持的候选方向为：

```text
actual finite restriction of Ism(G)  ⊆  A(k).
```

没有在本轮找到或证明反向扩张定理：

```text
every T ∈ A(k) extends to an element of Ism(G).
```

但 Urahigashi 的 non-containment 论证若真的对所有 T∈A(k) 成立，就不需要这个反向方向。反过来，构造一个 A(k) 的例子不能直接证明真实 Ism 中存在该例子。

### 3.3 Kummer 坐标图应写成什么

固定真实初始数据 D、column n、vertical position m、prime p、stage j，以及 local factor (i,v)。需要实际构造以下类型，而不只给一个名为 Kummer 的抽象等价：

```text
W_hol(m,i,v), W_an(i,v) : finite Q_p-vector spaces
L_hol(m,i,v) ⊆ W_hol(m,i,v)
L_an(i,v)   ⊆ W_an(i,v)

ι_hol : k_v ≃_Qp W_hol(m,i,v)
ι_an  : k_v ≃_Qp W_an(i,v)
κ_c   : W_hol(m,i,v) ≃_Qp W_an(i,v)
          for an ACTUAL admissible Kummer choice c

χ_c := ι_an⁻¹ ∘ κ_c ∘ ι_hol.
```

必须证明：

1. ι_hol、ι_an 把同一个具体有限 log-lattice 送到各自 L；
2. κ_c 保持相应 lattice；
3. 限制到不变量、Q-span 和 scalar extension 与 κ_c 相容；
4. 整个 packet map 是对这些局部 maps 逐因子 direct sum 后再 tensor 得到的；
5. 所有 choices 来自同一 Kummer structure / admissible family，且同步处理 splitting-monoid action。

III Prop.1.2(vi)、Prop.3.2 和 Thm.3.11(ii) 提供这些接口的重要原文依据；它们在当前工程里的具体 realization theorem 仍未建立。

## 4. M5/T5：允许族到底是不是作用闭包

### 4.1 有明确原文依据的三个层级

| 层级 | 原文依据 | 可以审计的结构 |
|---|---|---|
| Kummer unit data | II Def.4.9(i), p.154 | 一个 Ism-orbit，并以所有 H-lattices 的像刻画 |
| 固定 procession 的 Ind1/Ind2 | III Thm.3.11(i), p.154 | automorphisms of procession；每 factor、每 place-summand 的独立 Ism |
| 不同 radial presentations 之间 | II Example 1.7, pp.32–35 | groupoids、full essentially-surjective radial functor、lifting coric isomorphisms |

Example 1.7 的框架允许通过 fullness 提升 coric isomorphism，再作用于输出算法。它不是“同构存在所以数值相等”的原则；还必须给出具体 region-construction 的 functoriality 或等变性。

### 4.2 在本次读取段落中尚未找到的单一具体定义

III Cor.3.12 用 relevant Kummer isomorphisms 和 Ind1/2/3 定义 possible images 之并；Remark 3.9.5(Ob5) 用一族 possible regions 及其 hull 表达选择独立性。原文也大量陈述 stabilized/equivariant/functorial 性质。

但本次尚未抽取出一个完全具体的 dependent index type，**同时**列明：

```text
admissible c = (m, field/log coordinates, Kummer representatives,
                seed region, Ind1 representatives, Ind2 representatives,
                allowed Ind3 inclusions, synchronization data, ...)
out(c) ⊆ fixed P_j
U_j = ⋃_{c : admissible} out(c).
```

因此当前障碍不是“原文没有 orbit 观念”，而是尚未把所有兼容性放进一个可调用的具体 family，并证明作者使用的那条路径是这个 family 的成员。

### 4.3 不能把 Ind3 当作自动可逆的群作用

III Thm.3.11(ii), p.156 的 Ind3 包含随 m 变化的 inclusions/surjections。应使用有向关系、diagram 或 groupoid 加上非可逆 arrows，而不是假定三个 indeterminacies 的并是一个普通群。

如果需要一个较强的闭包定理，最低应写成：

```text
∀ c, Adm(c) →
  ∀ a, Allowed12(a,c) →
    ∃ c', Adm(c') ∧ T_a(out(c)) ⊆ out(c').
```

这里 a 只是实际 Ind1/Ind2 操作，T_a 作用于完整联合数据，Allowed12 不能直接取成全部 A(k) 矩阵。该式不要求 Ind3 可逆，也不要求一个固定 m 的区域经任意 vertical shift 后相等。

### 4.4 G03 实际只需要一个 witness，不需要全体闭包

为了支撑短文那个具体局部异议，M5/T5 可以进一步弱化。仅需：

```text
∃ m, ∃ c, Adm(c) ∧
∃ g ∈ seed(c),
  pr_u(κ_c(g)) = χ(x) ∧
∃ a, Allowed12(a,c) ∧ underlyingPermutation(a)=(2 3) ∧
∃ c', Adm(c') ∧
  T_a(κ_c(g)) ∈ out(c') ∧
  pr_v(T_a(κ_c(g))) = ψ(σ_*(χ(x))).
```

其中实际 χ、ψ 只需落入各有限 A(k_v)；若非包含对整个过度近似族成立，不需要实现每个矩阵。

这比“∀X∈U，∀σ，∀ψ，复合后仍在 U”弱得多，更适合作为下一阶段真实接口的第一个目标。若这条 witness 路径不允许，支持 IUT 的反驳应指出具体哪个 Adm/Allowed12 条件失败，以及原文依据。

## 5. 固定 packet 的线性壳保持与跨 tuple 重索引

固定 tuple v⃗ 的 Q_p-linear equivalence φ：

```text
φ : k_(v⃗) ≃_Qp k_(v⃗)
φ(L_(v⃗)) = L_(v⃗).
```

它不改变 tuple 的类型。与之不同，σ 的自然操作先是：

```text
σ_* : k_(u⃗) ≃_Qp k_(u⃗∘σ⁻¹)).
```

这只是 factor/place 配对的重新索引。source-place 跟随因子移动，不能只因 target slot 叫 j，就把原来的 q-source 改为该 slot 的新 place。

对于 actual Ind1 representative，需要证明：

```text
pr_(u⃗∘σ⁻¹) ∘ R_a =
  (⊗_i ψ_i) ∘ σ_* ∘ pr_u⃗.
```

同一个公式还要明确 ψ_i 的 domain/codomain 及其 lattice。若 prime-strip maps 保 place indexing，则每个被搬因子的 place 不变；stage j、active slot 和 theta-source place 是三个独立索引。

IUT III Remark 3.11.1(iv) 的 APT 警告对象是跨 arithmetic-holomorphic structures 的算法性传输。不能只引用“APT 不是 set-theoretic transport”便否定固定 coric packet 内由实际 procession automorphism 诱导的线性 factor permutation；也不能反过来凭一个形式上的 σ_* 就假定它已实现完整算法的实际输出。

## 6. 壳格保持、p^n 层与 valuation：精确区分

以下 LP0–LP4 均是待 Lean 检验命题／候选反例，不能在当前 fact-tree 里标作已认证。

### LP0：整数幂格层保持不需要 e 或 different

候选命题：

```text
V : Q_p-vector space
L ⊆ V : Z_p-submodule
T : V ≃_Qp V
T(L)=L
⇒ ∀ n∈Z, T(p^n · L)=p^n · L.
```

理由只用 Q_p-linearity、标量 p^n 非零及双射。这里的“层”是 L 生成的 p-adic lattice filtration，不是尚未定义的 field valuation filtration。

### LP1：从 LP0 到粗 valuation 层需要识别 L

在有限扩张 k/Q_p，规范 ord_p(p)=1，value group 为 (1/e)Z。若额外证明：

```text
p odd, e≤p−2
L=log_p(O_k^×)=m_k={z:ord_p(z)≥1/e},
```

则对非零 z，作者使用的候选判别为：

```text
z∈p^n L  ↔  n<ord_p(z)    (n∈Z).
```

这依赖离散 value group，不能对任意 real-valued filtration 照搬。由全部整数 n 的 membership profile，候选可恢复的是：

```text
ceil(ord_p(Tz)) = ceil(ord_p(z)).
```

它一般不恢复 ord_p(Tz)=ord_p(z)。若 e=1，valuation 已是整数，才可由这个特殊情形进一步取得精细等式。小分歧识别的原文来源是 IUT IV Prop.1.2(i), p.10。

### LP2：一个小分歧下精细 valuation 不保持的候选反例

取 k=Q_5(π)，π²=5；提出如下 Q_5-linear map：

```text
T(a+bπ) = 5b + (a/5)π.
T(π)=5; T(5)=π; T²=id.
```

在整数环的常用 basis (1,π) 下，m_k=Z_5π⊕Z_5·5。T 交换这个 lattice 的两个 generators，故候选地保 m_k 及每个 5^n m_k，但：

```text
ord_5(π)=1/2,  ord_5(Tπ)=1.
```

因为 e=2≤5−2，它也适用于“finite log-lattice preserving”这一有限条件。这个例子**没有**证明 T 能扩张为保持所有 open-H lattices 的真正 Ism(G) 元素；它只反驳从有限 lattice 条件直接推出精细 valuation 等式的推理。

### LP3：对任意 lattice，连 ceil(ord) 都不能免费取得

仍用 k=Q_5(π)。若仅知道某个 lattice L_N=Z_5·1⊕Z_5·5^Nπ 被保持，则交换其两个 generators 的线性 map 把 1 送到 5^Nπ。它保所有 5^nL_N，却可能改变 ceil(ord)。

这不是“真实 log_p(O_k^×) 在大分歧下必然如此”的反例；它表明若省去 lattice 与 valuation ball 的识别，逻辑上没有依据推出 ceil 层保持。真实大分歧情形须另行计算 log-image。

### LP4：一般情形应采用有误差的 lattice-gauge 比较

可用 IUT IV Prop.1.2 的 sandwich：

```text
p^a O_k ⊆ L ⊆ p^(−b) O_k
```

定义整数 lattice gauge ν_L(z)=max{n∈Z:z∈p^nL} 后，候选地 T 保 ν_L，而 ord_p(z) 与 ν_L(z) 仅受依赖 a,b 的区间控制。例如建议验证：

```text
ν_L(z)−b ≤ ord_p(z) < ν_L(z)+a+1.
```

这要求 L 为 full lattice、z≠0、fractional-ideal notation 已定义，以及 ν_L 的最大值存在。不能用它掩盖对这些条件的证明。

### different 出现在哪里

- LP0 不需要 ramification 或 different。
- LP1 需要 e 和具体 log-lattice 等式；不单靠 different。
- 从 tensor of integer rings 到其 normalization 的比较，以及固定 packet φ 的 hull/log-volume bound，才涉及 IUT IV Props.1.1–1.4 中的 d_I、a_I、b_I。
- 逐因子的 coarse valuation 控制与整个 tensor packet 的 arbitrary lattice automorphism 估计不能互换。

对 G03 的意义：上一轮短文使用的是 ceil 界及其后的一侧 valuation 上界，并没有在文字上声称 Ism 保精细 valuation。若实际 e≤p−2 和有限 realization 成立，这一 coarse 机制有明确需要证明的路线；不能用“线性映射可能改变 valuation”一句话就反驳它。

## 7. 最小真实接口：建议本轮后的拆分

建议分成以下独立定理，全部保留实际数据参数 D,n,m,p,j：

1. **finite_Ism_realization**：实际 Ism 对所有 H 的动作可限制到给定有限 invariant module，并在选定 log coordinates 下落入 A(k_v)。
2. **Kummer_tensor_realization**：实际 κ 的 packet map 在有限坐标中逐因子分解，保持相应 lattice。
3. **specific_seed_realization**：原 pilot-region 的一个实际元素给出短文所需纯张量 seed。
4. **specific_Ind1_lift**：σ=(2 3) 的 procession 自同构有一个实际 joint-data lift，并满足 projection transport equation。
5. **specific_output_membership**：该 lift 的输出属于 Cor.3.12 的原 possible-images family。
6. **small_ramification_log_lattice**：本例每个局部域的 log-image 与 valuation ball 的对应。
7. **coarse_valuation_bound**：实际有限 map 对该 seed 的 valuation 上界。
8. **normalization_hull_compatibility**：真实 hull 的积分结构实现为短文使用的 R̃-module。

前 1、2 项现在有更准确的一手来源；3–5 项仍是语义壁垒。有限 lattice 模型的 LP0–LP4 可帮助暴露偷换，但不能代替这些真实 realization。

## 8. 能支持 IUT 的具体条件与不能用的捷径

可检验的补救／反驳条件：

- 证明该具体 seed 不属于 actual pilot-region；
- 指出所有-H Kummer lattice compatibility 导致短文的 finite coordinate χ 形式不成立，并给出真实形式；
- 明确给出拒绝 σ=(2 3) 后该 seed-path 的 admissibility 条件，且与 procession automorphism 的原定义兼容；
- 若该路径确实存在，则扩大局部容器，重做 orbit/hull 与全局误差估计。

不能充当补救的说法：

- “Ism 叫 isometry，所以 ord 每一点都不变”；
- “p^nL 全部保持，所以所有 fractional valuation balls 都保持”；
- “不同 packet 抽象同构，所以可以保留目标 q-source”；
- “Ind3 是一个任意群作用”；
- “一个过度近似矩阵不一定来自 Ism，所以针对所有矩阵的非包含无效”；
- “原文有 orbit 一词，所以所需具体 joint-data witness 已经在当前 Lean 工程实现”。

结论状态：M4 得到更准确的来源接口；M5/T5 被缩减为一条具体 witness 的 admissibility/等变性目标。**G03 仍 open；没有认证原 IUT 的局部反例、Cor.3.12 的真伪、Theorem 1.10 的全局结论或 abc。**

