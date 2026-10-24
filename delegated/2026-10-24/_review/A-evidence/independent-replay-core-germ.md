# 独立重放记录（v2，含原始产物）：core-kummer Boundary/ThetaGermTransport.lean

日期：2026-10-24。执行者：主线（非交付方）。
**v2 修订说明**：v1 只有叙述性数字，被独立审查官 A 判定为"用判交付方的同一把尺子不能放宽"。
本版补上原始产物、argv、机器回执与 import 新鲜度核验；同时**更正 v1 的一处错误**（见 §4）。

## 1. 目的

把审查官 A 对 `research/core-germ-2026-10-24/` 的质疑（5 份 0 字节日志、`lean-build.log` 只含 axioms、
退出码为自述 JSON）从"证据不足"推进到"结论可判"。**不是**要给主线开例外。

## 2. 命令与机器回执

```text
cwd:    D:\Inter-universal Teichmüller Theory\candidates\core-kummer
argv:   ["lake", "env", "lean", "--json", "-DwarningAsError=true", "Boundary/ThetaGermTransport.lean"]
exit:   0            （由外层 shell 的 $LASTEXITCODE 取得，非日志末行）
elapsed: 54.4 s      （Stopwatch 实测，非自述）
```

原始产物（**可复算**，与本文同目录）：

| 文件 | 字节 | sha256 |
|---|---|---|
| `replay-run/stdout.jsonl` | 5817 | `7c302fbf7f7404fa83a3c8c575003113032cae0cc5f833375b0d1d48555a2d4e` |
| `replay-run/stderr.txt` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`（空文件哈希） |
| `replay-run/exit.txt` | 2 | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |
| `replay-run/timing.txt` | 65 | `ec8b4647cbfdf93b99f967d48d01590e99b2c5804c2a96e316326a4929871e56` |
| `replay-run/argv.txt` | 146 | `38d1d40d779177d1bc0b5e16465ec9bed9b33675dd1a1b96a68e53dc787ca772` |

（`exit.txt` / `timing.txt` / `argv.txt` 是应独立审查官要求后补的：在此之前 `exit: 0` 与 `54.4 s`
只存在于 Markdown 正文，属纯叙述数字。现已落盘，最后两个叙述性数字消除。）

逐行解析 `stdout.jsonl`（18 行，全部可解析，0 行不可解析）：

```text
severity 计数: {"information": 18}
其中 depends-on-axioms 行: 18
severity="error" 计数:   0
severity="warning" 计数: 0
```

公理集合：18 条全为 `[propext, Classical.choice, Quot.sound]`，与交付方 `lean-build.log` 的 18 条**逐条同名同序对应**。

## 3. import 新鲜度核验（补上 A 指出的"旧 olean 欺骗"缺口）

`lean <file>` 只重新 elaborate 该文件，import 一律读现成 olean。故必须先核 import 是否陈旧：

| import 源文件 | 源 mtime | olean mtime | 是否新鲜 |
|---|---|---|---|
| `Boundary/ProjectiveComparison.lean` | 11:24:44 | 11:26:07 | **新鲜**（olean 晚于源） |
| `TateCurvesTheta/Kummer/ThetaGermCore.lean` | 11:41:36 | 11:45:13 | **新鲜** |

两条 import 的 olean 均晚于对应源文件，故本次重放读到的不是陈旧 olean。

**仍未设防的一点**（诚实记录）：本记录只核了这两个直接 import 的 mtime，没有递归核它们的传递 import。
`-DwarningAsError=true` 下 `severity="error"` 为 0，说明**本文件此刻能在此 import 集合下 elaborate**；
但若某个传递 import 的 olean 陈旧，本记录不能排除该情形（本案已核对的两跳未见异常）。

## 4. 对 v1 的更正

v1 写"58 条 information"，**错误**。实际是 **18 条**。原因是我当时把 PowerShell 输出的行数
（含 JSON 折行）当成了记录条数，且**没有留下原始产物**以至于无法自查。
这正是审查官坚持要原始产物的价值：一个纯叙述性记录可以同时错数字又不可复核。

## 5. 结论的准确边界

- **可以断言**：`Boundary/ThetaGermTransport.lean` 在本机当前工作区、当前 import 集下，
  以 `-DwarningAsError=true` 严格编译返回 0，18 条 `#print axioms` 全在
  `{propext, Classical.choice, Quot.sound}` 内。
- **不可以断言**：任何数学命题为真；编译通过与公理干净不是数学正确性。
- **不可以断言**：交付方那 4 份 port 模块的同类声明。它们仍是 0 字节日志、退出码无进程回执，
  **仍记 UNDECIDABLE**。
- 实际 VS Code 0 error / 0 warning 观察仍未做（README 明写本轮不重复，故不算缺陷，但也不算通过）。

## 6. 独立审查官 A 的第三方复核（§R3，追加记录）

审查官 A 未采信本文转述，自行重算并**追加了一步本文没做的更强核验**：

- `stdout.jsonl` 的 18 行 `pos.line` 恰好是 **237, 238, …, 254**，与源码 `#print axioms` 的 18 行
  **逐行全等**；`fileName` 唯一、`kind=[anonymous]`、`isSilent=false`；
  公理计数 `propext=18 / Classical.choice=18 / Quot.sound=18`，**无 sorryAx、无第四种**。
- A 的判断："这种行号级咬合伪造不出来——JSONL 是真 elaborator 输出。"

A 同时纠正了两个分寸问题，本文接受：

1. **不得与交付方证据合并**。本次重放证明的是"该文件此刻能编"，不能证明"交付方当时真编过"；
   `port-build-exits.json` 里那 3 条 `parent observed exec session …` 仍是自述。
   故：**主线 ThetaGermTransport 一条 = PASS（限定：本机当前 import 集 / 该 SHA / 白名单内）；
   4 个 port 模块与交付方退出码链 = 维持 UNDECIDABLE，二者不得合并。**
2. **"无原始产物"应判"不可判"而非"假"**。v1 的「58 条」错误恰好说明当时只能说不可判。
   本文已按此改写：v1 的状态是"不可判"，不是"错误结论"。

**4 份 0 字节 port 日志的协议落点**（A 与本文一致）：`UNDECIDABLE`，不是 FAIL，更不能算 PASS。
0 字节无法区分"真跑过且无输出"与"根本没跑"。协议上应**阻塞"4 个 port 模块已建构"这一声明**，
不得写入 fact-tree 已验证集。

一条正向旁证但**不解门禁**：T021 快照工程在 13:21:40–13:31:46 独立产出了同名 4 个 olean
（QParameter/Basic 96632 B、Theta/Basic 262240 B、Theta/Periodicity 222552 B、Kummer/ThetaGermCore 493688 B）。
这提高了"这些模块可编译"的信心，但那是另一个工程、另一次运行，不能替代交付方对 0 字节日志的举证责任。
