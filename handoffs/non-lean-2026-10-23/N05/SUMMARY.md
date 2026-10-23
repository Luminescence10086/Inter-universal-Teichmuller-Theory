# N05 允许变化究竟保持什么 —— 逐操作来源台账（静态）

任务卡 N05 ＋ 旧契约 `handoffs/core-integral-source-2026-10-23.md`；旧目录无既有交付（`Test-Path` 返回 MISSING），故整份重做，未补缺项。只写本目录；未运行 Lean/Lake/LSP，未取证编辑器。工作区 HEAD 568e4be…（任务表快照号 1a8515d8… 不是输入 pin）。

## 输入已核（无 INPUT_DRIFT）
- `research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt` = 70a618ad…4b715，与旧契约给定的 SHA256 逐字相同（11854 行 / 570037 B）。
- `reviews/core-round/external/iut` @ f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb，`git status --porcelain` 为空。
- `.../Iut/Concrete/LocalConstruct/IndAut.lean` 3d39b385…；直接依赖 `LogShell.lean` 35c6b206…、`Integral.lean` d8240f78…（共 2 个附加文件，未读 `ArchIndAut.lean`）。

## 逐操作结论（`evidence.csv` 11 行 = 7 条原文 + 4 条源码）
| 操作 | 被保持的对象（原文措辞） | 系数环 | 同格 | 逆向 | 有限商 |
|---|---|---|---|---|---|
| Ob1（p.131） | 无。明说 I_k「isnot, in general,stabilized by … byO×_k」 | O_k | NO | UNRESOLVED | UNRESOLVED |
| Ob2（p.131） | hull φ(P)∈H「stabilized by the natural action of O×_k」 | O×_k | UNRESOLVED | UNRESOLVED | UNRESOLVED |
| Ob7（p.135） | 无格。只要求经 hull 造出的对象可与余域 `F⊩▶×μ` 的局部/整体 Frobenioid 对象比较 | UNRESOLVED | UNRESOLVED | UNRESOLVED | UNRESOLVED |
| Ind1（p.154） | 无。仅 Aut(Prc(n,◦D⊢_T)) 诱导的 indeterminacy | UNRESOLVED | UNRESOLVED | UNRESOLVED | UNRESOLVED |
| Ind2（p.154） | 无。Ism／二阶 poly-automorphism 作用在 j+1 个张量因子的各直和项上 | UNRESOLVED | UNRESOLVED | UNRESOLVED | UNRESOLVED |
| Ind3（p.156） | (a) 的同构；只给「⊆」（V^non_Q）与「↠」（V^arc_Q） | UNRESOLVED | NO | NO | UNRESOLVED |
| 3.12.2(v)（p.194） | 无。region 只能在「indeterminacy with respect to O×-multiples」下接算术线丛范畴 | O× | NO | UNRESOLVED | UNRESOLVED |
| factorAut／tensorAut／latticeAut／indAut | ⊗_j 𝓘_{c j}（log-shell 张量），集合等式 | ℚ_p | YES | YES | UNRESOLVED |

## 不做的推断（红线）
- 不从「保持 log-shell」推「保持原始 holomorphic 整数格」：Lean 侧被保持的是 `tensorLogShell`，不是 order `R_I`（`Integral.lean:206-212`），也不是 `logShell` 𝓘_I（`LogShell.lean:322-324` 只有 ⊆；仅奇素数非分歧时相等，`466-477`）。
- 不从 ℚ_p-线性等价推 𝓞_v-环同构；不把 `indAut` 的分派定义当原文忠实性证明；(Ind3) 在 `indAut` 中无对应。
- `shared_finite_quotient` 全部 UNRESOLVED：所读原文与源码均无「共用同一个有限商」的陈述；唯一被命名的商是 Ob7 的 log-volume 商（非有限）。

## 引用规范
- 每格引文 ≤4 连续行；`source_quote` 逐字复制，仅把换行与连续空白折成单个空格；行区间见 `line_from`/`line_to`，PDF 页码见 `page`。PDF 文本层断词（theOk、deﬁned、sur-jections、I n( O b 6 )）保留原样。
- `same_lattice` = 引文是否断言被保持对象就是同一个格（双向集合等式）；`reverse_preserved` = 是否断言逆向；`shared_finite_quotient` = 是否断言诸变化共用一个有限商；未明说一律 UNRESOLVED。
- 行级 status ∈ SOURCE_FACT／PARTIAL_FACT／UNRESOLVED（PARTIAL_FACT = 该行五个字段中部分逐字有据、部分 UNRESOLVED）；`delivery.json` status = STATIC_COMPLETE。本件是来源索引，不是数学证明，也不是判定原始 IUT 有缺陷。
