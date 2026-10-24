# 交付预检暴露的两个真实缺陷（供本批后续与下批复用）

日期：2026-10-24。来源：主线对 `delegated/2026-10-24/` 的独立复核。
这两个都不是"任务做错了数学"，而是**交付格式里的坑**，会让包永远无法通过预检。

## 缺陷 1：`delivery.json` 把自己的哈希写进 `artifacts`（自引用，不可满足）

**实例**：T003 的 `delivery.json` 在 `artifacts` 里列了自己。

```text
declared f69930324ce3…
actual   2e783619afb8…     （一旦文件被写定就永不相等）
```

**后果**：`check_delivery.py` 报 `PACKAGE_INCOMPLETE: artifact SHA mismatch: delivery.json`。
这个包**在任何情况下都不可能通过**——因为写哈希这个动作本身会改变文件。

**协议依据**：`handoffs/next-round/README.md` 与 `PROTOCOL.md` 都写明了"输出 hash 不包含 delivery 自身，
避免自引用"。T003 违反了这一条。

**处置**：主线删掉该自引用条目（20 → 19 个 artifacts），重跑预检得到 `PACKAGE_COMPLETE`。
删除是安全的：`delivery.json` 的身份由它在包里的**位置**决定，不需要自己证明自己。

**给后续任务的规则**：打包时先算完所有**其他**文件的哈希，最后写 `delivery.json`，
且**永远不要**把它列进 `artifacts`/`outputs`。

## 缺陷 2：`lake build` 无参 = 什么都没构建，却返回 0

**实例**：`candidates/core-transport` 的 lakefile 里 `lean_lib CoreTransport` 没有 `@[default_target]`。

```text
$ lake build
warning: no targets specified and no default targets configured
Nothing to build.
exit code: 0
```

**后果**：任何"构建通过"的声明若用这条命令，等于**什么都没验**。这正是
`research/core-germ-2026-10-24/lean-build.log` 只有 axioms 行、没有编译过程行的成因之一。

**协议依据**：`PROTOCOL.md` 已写"`lake build` 空目标不构成编译证据"。

**给后续任务的规则**：
1. 验收命令必须写**显式目标**（`lake build <Lib>` 或 `lake env lean <file>`）；
2. 日志里出现 `no targets specified` / `Nothing to build` 一律记 **FAIL**，不记 PASS；
3. 若 lib 没有 `@[default_target]`，要么加显式目标名，要么补 `@[default_target]`（后者属构建图改动，需单独立项）。

## 缺陷 3（顺带记录）：构建图残缺导致"文件存在但在库里不存在"

**实例**：`candidates/core-kummer` 有 30 个 Lean 模块，lakefile 只声明 7 个 roots。

**后果**：23 个模块永远不编译、永远无 `.olean`；import 它们必然失败。T008 的 A21
（`Boundary/DecompositionBridge.lean` 无法核验）就是这个后果，不是"这次忘了建"。

**处置**：提交 `764c7b3` 补全 roots，`lake build Boundary` 从零构建 exit 0（8789 jobs / 504.2 s），
`DecompositionBridge.olean` 首次生成（187120 B）。

**给后续任务的规则**：接手一个隔离工程前，先做一次"目录里的 `.lean` 数 vs lakefile 声明的 roots 数"比对；
不等就说明有游离模块，任何依赖它们的核验声明都不可信。

## 这三条的共性

三条都不是数学问题，全是**证据链的形式缺陷**，而且都能让一个虚假的"通过"看起来成立。
审查的价值就在这里：不看数学对错，先看"这个通过是真的吗"。
