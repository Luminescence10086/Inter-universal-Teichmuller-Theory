# M-i 的类型设计：把"除回 M 次幂"做成有名之项

日期：2026-10-23。状态：**设计 + 玩具形状**，非结论、非 fact-tree。核心 GAP 保持 OPEN。

## 义务回顾（来源已核）

原文两处只是**断言**：

- **(Ob4)**，txt 8135–8144：这个"稍作修改的目标"「does not result in any substantive problems such as, for
  instance, an indeterminacy arising from confusion between a given arithmetic line bundle and its `M`-th
  tensor power」——**断言无害**，没有映射、没有界、没有不变性陈述。
- **(Ob4-3)**，txt 8185–8189：重构出的非 tensor-power Frobenioids 与给定 tensor-power 副本之间只到
  「a "tensor-power-twist indeterminacy"」，随后断言「we shall ultimately … only be interested in
  **estimates of log-volumes**, such tensor-power-twist indeterminacies will not have any substantive effect
  on our computations」——注意用词是 **estimates**。

## 为什么"除回"不可能是对象层的逆

`det^{⊗M}(−)` 在对象层**不可逆**：从 `a^{⊗M}` 取回 `a` 需要 `M` 次根，而根一般不唯一、甚至不存在。
所以 M-i 能要求的东西**不在对象层，而在读数层**——这也解释了为什么原文的说法总是关于 log-volume。

于是"除回"只能是：**在一个读数上做的除法**，其合法性依赖两件事：

1. 读数对张量积**可加**（log-volume 正是如此）；
2. twist 的贡献为**零**，或至少可控。

原文把第 2 条当断言；本设计把它变成**一个有名字的项**，从而可被证伪。

## 类型设计

设 `Obj` 为某个交换幺半范畴中的对象类（line bundles 及其张量积），`R : Obj → ℝ` 为读数。

```
additive      : R (a ⊗ b) = R a + R b
tensorPower   : Obj → ℕ → Obj
pow_reading   : R (tensorPower a M) = M * R a          -- 由 additive 归纳得到
Twist         : Obj → Obj → Prop                        -- twist 不定性关系
twist_reading : ∀ {b c}, Twist b c → R c = R b + τ      -- τ 是 twist 自身的读数
```

要的"除回"是一个**部分定义**的操作：给定 `b` 与 `a`、`M` 以及一个见证 `Twist b (tensorPower a M)`，
```
divideBack : (h : Twist b (tensorPower a M)) → ℝ
divideBack h := R b / M = R a + τ / M                    -- 从上面两条直接算
```
于是：

- **`τ = 0`** ⇒ `divideBack h = R a`，即读数值与所选代表无关——这才是"无实质影响"的确切含义；
- **`τ ≠ 0`** ⇒ 除回后的读数带一个**非零的加项**，此时"除回"不给出原读数，除非另证该加项可被吸收
  （例如在估计里被界住）。

**关键**：M-i 的实质内容因此可以一句话说清——**它要求证明 `τ = 0`（或给出 `τ` 的界），而不是要求一个
对象层的逆**。原文没有给这个证明；它把 `τ` 的存在性连同"无实质影响"的断言一起写下。

## 玩具（W8）证什么、不证什么

在 `ℚ_[3]` 上用 `CoreTransport.localLog`（W3 已建立 `localLog (x^M) = M·localLog x`）：

- `twistReading`：`localLog ((u x)^M) = M·localLog u + M·localLog x`——把 twist 项**显式写出**；
- `divideBack_twist`：`localLog ((u x)^M) / M = localLog u + localLog x`——除回后正是"原读数 **+ twist 的读数**"；
- `twist_insensitive_iff`：`(∀ x, divideBack = localLog x) ↔ localLog u = 0`——**不变性当且仅当 twist 项的读数为零**。

最后一条是本设计的落点：它把"无实质影响"变成一条**可判定的等价条件**，而原文恰恰没有证明该条件成立。

**不证**：`τ` 在真实 tensor-power Frobenioid 上是什么、是否为零、是否为估计所吸收；也不涉及
`det^{⊗M}` 的真实对象、log-shell、prime-strip、Θ-link 或 Cor 3.12。

## 与 W3 / W5 / W6 / W7 的关系

- W3 给了"除以标量 M"的最简法则（无 twist 项）；
- W5/W7 给了"读数必须在商上取值"的一般形状；
- **M-i 是这两者的交叉点**：twist 项 `τ` 正是"商的类内差"，而 `divideBack_twist` 说明它不消失时，
  读数就落在呈现上而不是对象上。

## 仍未解决

1. `τ` 的**真实来源**：在原文的 1-column 归一化下，tensor-power twist 对
   `[suitably normalized, w.r.t. j ∈ |F_l|]` log-volume 的贡献是否为零——需要把 M-iii 的对齐做完才能谈；
2. **M-ii**：三处 `M` 同一个（hull 的 `det^{⊗M}`、q-pilot 侧、`(Ob4-1)` 的 degree-M Frobenius）；
3. 估计版的吸收（(Ob4-3) 说的是 *estimates*）：若 `τ ≠ 0`，需要给出 `|τ/M|` 的界并说明它进入哪个估计。
