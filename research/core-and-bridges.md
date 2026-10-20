# IUT 工具链、交叉模型与语义桥接义务

检索日期：2026-10-16。文档状态：研究提案与来源索引；**不属于 fact-tree**。本文件没有宣称任何新数学结论已经成立，也没有进行 VS Code 零告警验收。下列“候选命题”须经 Lean 证明及用户要求的 VS Code 验收后才可转为事实节点。支持 IUT 的研究立场落实为尽力构造精确、可反驳、可修复的接口，不能代替证明。

## 1. 原文工具链及应避免的类型混淆

### I：初始 Θ-data 与 Hodge theaters

IUT I 从数域上的椭圆曲线、素数 ℓ≥5 及指定的局部赋值等数据出发，组织半图 anabelioid、Frobenioid、étale theta 等结构。Hodge theater 的不同副本各自保有环论；Θ-link 只粘合指定的 Frobenioid 部分，并不提供跨副本的环同构。不能因 theaters 作为对象同构，就认定特定 Θ-link 保加法。[IUT I，摘要、Definition 3.1、Definition 6.13](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf)

**接口建议（提案）**：以 `Theater i` 区分副本；乘法单子、值群、环分别成为带显式遗忘映射的数据类型。跨 Θ-link 只暴露已经证明存在的接口，禁止从单子映射自动提升为 `RingHom`。完整初始数据须逐项抄录 Definition 3.1；仅有“一个椭圆曲线加 ℓ”不够。

### II：求值、Kummer 理论与 multiradiality

IUT II 研究 theta 在扭点的 Hodge–Arakelov 式求值及其 Kummer 结构，构造 Θ-link 的新版本。`multiradial` 关注能否从另一算术全纯结构解释这些构造；不能直接改写成“任意换坐标不改变所有量”。[IUT II，摘要](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf)

**接口建议（提案）**：分开记录构造的输入类型、输出类型、允许的自同构、共轭不定性，以及每条自然性等式；只有原文所需箭头才允许参与交换图。

### III：log-link、非交换格与体积比较

log-theta-lattice 的横箭头是 Θ-link 版本，纵箭头是由局部对数构造的 log-link；全格不能先验视作交换方格。log-shell 将局部单位的对数信息组织成可比较结构。Theorem 3.11 的 multiradial 表示允许 Ind1–Ind3；Corollary 3.12 随后比较 pilot 的 log-volume。其 Θ 侧取可能像之并的 holomorphic hull，且原陈述允许扩展实数情形。[IUT III，摘要、Theorem 3.11、Corollary 3.12](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf)

**接口建议（提案）**：对数不是任意局部域乘法群到整个加法群的无损同构。须指定单位子群、核、标度、局部次数和壳的定义；实数体积的有限性不能藏进数据类型而不列为证明义务。

### IV：局部估计、全局高度及 abc

论文宣称的后续路径是：III Corollary 3.12 → IV Theorem 1.10 的数值估计 → IV Corollaries 2.2、2.3 的高度不等式，并经一般位置椭圆曲线与非临界 Belyi 映射的归约连接 abc。发表版为 PRIMS 57 (2021), 627–723；详细审计须固定版本，不能混用早期预印本编号。[发表记录](https://ems.press/journals/prims/articles/201528)，[RIMS 早期 IV 预印本，仅作历史文本](https://www.kurims.kyoto-u.ac.jp/preprint/file/RIMS1759.pdf)

**目标陈述候选**（标准整数 abc，仅定义目标，尚未在此证明）：对每个 ε>0，存在 C>0，使所有互素正整数 a、b、c 满足 a+b=c 时，有 `c ≤ C · rad(abc)^(1+ε)`。Lean 中须明确 `rad`、实数幂、正性、互素条件及量词顺序。有限例外、高度形式、整数形式之间的等价也须分别证明。

## 2. 候选研究方向：类型化 transport 与能力边界

以下全部属于尚待形式化的设计，不能作为已知定理调用。

**T1 候选命题**：若 `A,B` 为乘法单子，`f : A ≃* B`，则任意只用 `1`、乘法与相等构成的方程在 f 下保持；这一结论不包含加法保持。可用具体测试 `f : ℕ → ℕ, f(n)=n²`：检验其为乘法单子同态，并检验 `f(1+1) ≠ f(1)+f(1)`。

- 必要假设：输入表达式的语法明确限于乘法语言；具体反例使用 ℕ 的通常运算。平方映射仅作单子同态测试，不能误称 ℕ 上的自同构。
- 失败判据：任何证明暗中使用源和目标的加法可交换性于 f，或构造一个没有独立证明的 `RingHom`。
- 初始模型：副本由索引类型区分；语法解释器逐个构造证明 transport。
- IUT 语义桥接义务：逐一确定各版 Θ-link 实际提供的单子、Galois 作用及图表；把其保持性质映射到语法片段。平方例子既不是实际 Θ-link，也不具有 IUT 的 Kummer 刚性。

**T2 候选命题**：令 C 为群胚，`F : C ⥤ Type`，`I_c : F(c) → ℝ`。若对每个箭头 g 和 x，有 `I_d(F(g)(x))=I_c(x)`，则 I 在对象与元素构成的作用群胚的同构类上下降。

- 必要假设：明示所有允许的箭头及函子律；输出 ℝ 具有相等而非隐含的标度识别。
- 失败判据：一条 loop 改变 I；或只验证选定基点，却声称对全部副本成立。
- 初始模型：有限群作用在有限集合上；通过轨道计算寻找违例，再以 Lean 证明商提升。
- IUT 桥接义务：说明哪些 Ind1/Ind2 可由群作用表达，哪些 Ind3 更适合关系或包含而非可逆箭头；尤其不得把非可逆遗忘强行群胚化。

## 3. 候选研究方向：descent、信息丢失与可辨识性

**D1 候选命题**：对满射 `q : X → Y` 和函数 `f : X → Z`，存在 `g : Y → Z` 满足 `f=g∘q`，当且仅当 `∀x x', q x=q x' → f x=f x'`。

- 必要假设：q 满射；采用经典选择或显式给出代表元。必须在最终 `#print axioms` 中记录选择依赖。
- 失败判据：找到同一纤维中的 x、x'，它们的目标量不同。这只否定从 q 所保留数据唯一恢复 f，不能直接否定 IUT 存在另一个包含更多信息的构造。
- 初始模型：`X=Y×S`，q 遗忘 S；目标量同时依赖 S。将自动枚举得到的违例转写为 Lean 的存在性命题。
- IUT 桥接义务：给出真正的遗忘映射，证明其纤维恰好覆盖相应不定性；确定跨 theaters 可调用的是 f 本身、轨道量、区间还是集合值估计。没有真实数据接口便不能宣称此处证明了“信息丢失导致 IUT 失效”。

**D2 候选命题**：若恢复的目标不是单值 f 而是集合值 R(y)，且每个 x 满足 `f(x)∈R(q(x))`，那么任意对 `R(y)` 中所有元素成立的上界都约束 f(x)。

- 必要假设：确实证明真实像包含在 R 中，而非只证明 R 中有一个有利代表元；上界对全体像成立。
- 失败判据：对每个 x 分别选择不同“有利坐标”后，误用统一的全局坐标；或把 `∃r≤B` 换成 `∀r≤B`。
- 模型：有限集合包络与最坏情形估计；Lean 优先验证量词交换是否有效。
- IUT 桥接义务：R 应精确对应 Ind1–Ind3 的所有可能像，并证明 hull 的包含与有限性；这个步骤才可能为“遗忘后仍能有足够弱的数值控制”提供补救路线。

## 4. 候选研究方向：鲁棒包络、hull 与体积

**H1 候选命题**：令 `Cl : Set X → Set X` 为单调闭包算子，`S⊆T`，则 `Cl S⊆Cl T`；若 μ 为测度，则 `μ(Cl S)≤μ(Cl T)`。当两者测度均严格正且有限时，才继续比较实数对数。扩展实数的 0、∞ 边界另行处理。

- 必要假设：Cl 的单调性及 μ 的同一 ambient space、同一归一化。要声称最小 hull，还须给出允许 hull 的类与最小性。
- 失败判据：只知每个单独像体积相等，却推出并集的体积相等；忽略并集、闭包或分量组合导致的增大；以实数类型提前排除无限体积。
- 模型：有限盒、矩形包络、p 进格包络分层建立；先用有限计数测度检验逻辑，再引入 Haar 测度。
- IUT 桥接义务：将 Cl 具体实例化为论文的 holomorphic hull；证明 Ind 群作用的像包含、张量分解、packet 权重、维数归一化，以及 IV Step (v) 所需的真实局部包含。一般闭包单调性不能提供这些包含。

**H2 候选命题**：对有限指标集、正权重 `w_i` 满足 `∑w_i=1`，若每个 `L_i≤B_i`，则 `∑w_i L_i≤∑w_i B_i`。

- 必要假设：w_i 非负；同一指标集、每项有限、各项确实是相同定义的 log-volume。
- 失败判据：在求平均前后改变指标副本、局部次数或归一化；用 `log(∑w_i vol_i)` 偷换 `∑w_i log(vol_i)`。
- 模型：有理数与有限数组；精确算术而非浮点拟合。
- IUT 桥接义务：证明 procession 与 tensor-packet 的原始索引对应关系和平均公式。H2 本身只是算术模块，不能替代 III Corollary 3.12。

## 5. 候选研究方向：赋值标度与 Arakelov 归一化

**V1 候选命题**：对乘法群 G、加法交换群 Γ，若 `v(xy)=v(x)+v(y)`，则 `v(q^(j²))=j² • v(q)`（j 为自然数）。若 Γ=ℝ 且 λ>0，则 `v_λ(x)=λv(x)` 仍满足同一乘法到加法关系。

- 必要假设：q 非零（或直接令 q∈G）；乘法赋值与加法赋值的约定不可混用。
- 失败判据：仅由乘法关系便推出绝对数值上界；任意重标度仍符合全部前提却破坏结论。
- 模型：`G=ℤ` 的加法化模型或 Laurent 单项式；逐项追踪 q 到 `q^(j²)` 的权重。
- IUT 桥接义务：证明实际 Θ-link 的标度、根号 `1/(2ℓ)`、j 标签、局部对数底及全局单位由论文数据固定；若其他结构排除了自由重标度，须明示并证明。此模型不证明 IUT 真的允许任意标度。

**A1 候选命题**：令有限集合 W、V，`π:W→V`，权重 `a_w,b_v∈ℝ` 满足 `∀v, ∑_{π(w)=v} a_w=b_v`，局部量 `u_v∈ℝ`；则 `∑_w a_w u_(π(w))=∑_v b_v u_v`。

- 必要假设：有限性；权重等式；u 在扩张下的比较已经正确包含 e、f 或已归一化绝对值。不能仅凭符号“度数”推断等式。
- 失败判据：扩张次数 d 出现两次或漏一次；局部项归一化后不变而分母再乘 d；无穷素点的实/复权重遗漏。
- 模型：先以有理权重证明有限纤维求和恒等式，再接数域 place 的基变换。
- IUT 桥接义务：从局部次数公式与 product formula 构建实际权重，固定 arithmetic degree 的归一化，并证明非阿基米德和阿基米德项均匹配。此方向可审计 IV Definition 1.9 的公式，但不能在未实现数域实例时声称已验证它。

**A2 候选命题**：在固定的非阿基米德局部域 K 上，选定加法 Haar 测度 μ、有限维 K 空间的格 L，及 K 线性同构 T；候选缩放律为 `μ(T L)=|det T|_K·μ(L)`，随后在正有限条件下取 log。

- 必要假设：局部紧性、规范绝对值、可测格、同一测度、有限维、T 可逆；p 进 logarithm 的使用另设收敛域和核。
- 失败判据：把乘法群测度用于加法格；把异维空间的 determinant、不同归一化的 Haar 测度或不同局部域直接相等。
- 模型：`K=ℚ_p` 与坐标格 `ℤ_p^n`，先从对角缩放开始，再一般化到矩阵分解。
- IUT 桥接义务：识别 log-shell 的真实格、tensor-packet 对基域的维数，以及允许不定性对应的线性映射。一般 determinant 缩放律不蕴含多半径算法的存在。

## 6. 2026-10-16 可检索 Lean 源码：仅列候选，未验收

| 来源 | 本次实际核读及边界 | 可纳入 fact-tree？ |
| --- | --- | --- |
| [lana-agents/iut](https://github.com/lana-agents/iut) | 仓库 README 自称含 III 3.12 **变体**到 ABC 的条件推导；这是作者对源码的说明，不是本地复核结果。 | 否；未固定 commit、未编译、未在 VS Code 检查。 |
| [Statement.lean 原始源码](https://raw.githubusercontent.com/lana-agents/iut/main/Iut/Cor312/Statement.lean) | 本次读到 `Corollary312Variant` 为 `Prop` 定义，非证明；源码注释明确不等同于发表版 Corollary 3.12，区域构造及语义对应仍有边界。 | 否；有类型声明不等于有证明。 |
| [LANA-Project/iut4-sec1](https://github.com/LANA-Project/iut4-sec1)、[genl](https://github.com/LANA-Project/genl) | LANA 组织公开仓库，范围分别涉及 IV §1、一般位置归约。未审阅完整 import 闭包，不能据组织名称断言已获完整数学审查。 | 否。 |
| [PriestAmbrose/IUT-Corollary3_12-Lean](https://github.com/PriestAmbrose/IUT-Corollary3_12-Lean) | 仓库自述为 axioms-first skeleton。必须检查有无把关键缺口作为公理。 | 否。 |
| [seewoo5/lean-poly-abc](https://github.com/seewoo5/lean-poly-abc) | 多项式 Mason–Stothers 形式化候选；对象不是整数 abc。 | 否；可进一步固定版本并复核，但不能冒充整数 abc。 |

官方 [2026-04 preliminary formalization report](https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf) 讨论 skeleton 与 blackbox 接口。它说明存在正式化工作方向，不能据此宣布完成 IUT 的全细节 Lean 验证。

**候选源码接入程序**：固定 SHA、toolchain、lake-manifest；读取最终定理完整类型并核对其数学含义；重建 import 闭包；检查 `sorryAx`、自定义公理、`admit`、不可信求值捷径；对最终声明执行 `#print axioms`；核对每一个结构字段是否偷偷假设目标结果；命令行编译和 VS Code Problems 均零诊断；保存日志与文件哈希。只有这些完成且通过语义核对，才允许建立已验收节点。条件定理必须保留全部假设，不能把 `H → abc` 登记成 abc。

## 7. 优先顺序与尚未跨越的缺口

1. 在自建基础模型里证明 T1、D1、H1、H2、V1、A1；它们用于审计接口与寻找反例，不宣称完成原理论的局部实例。
2. 选择一个明确的原文局部对象，建立其类型、允许箭头、权重与 Haar 归一化；检验有限模型发现的问题能否真实实例化。
3. 单独追踪 III Theorem 3.11 → Corollary 3.12 和 IV Step (v) 的包含/量词/体积义务。若方向失败，记录失败的精确假设和反例；不得删除不利样本来提高拟合效果。
4. 对可复用公开源码，先做定理语义与依赖审计，再投入本地重建；所有文献叙述和猜想保持在 research 层。

当前未闭合义务：完整 IUT 初始数据编码；Hodge theaters 与各 link 的忠实模型；multiradial 算法及全部不定性的覆盖；真实 holomorphic hull 的有限性和局部包含；发表版 Corollary 3.12 与候选 Lean 变体的比较；到标准整数 abc 的无遗漏归约；VS Code 零告警验收。只要这些仍未解决，就不能声称已补救 IUT 全部争点或证明 abc。
