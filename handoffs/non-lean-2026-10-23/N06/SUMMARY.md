# N06 — 归一化、平均与体积换算台账

状态：`STATIC_COMPLETE`（换算条件草稿；公式全部 `UNVERIFIED_MATH`，算例 `EXPERIMENTAL`）

## 10 行台账（`normalizations.csv`）最要紧的三条
1. **两套 pilot 之间缺一个常数 `c`**（N06-01）：`R^ss` 的 pilot 是 `M = 1·S` 的类，`η_q` 的 pilot 是 `{q_v O_v}` 对角嵌入的类。
   原文从没给出两者的换算因子；`c` 若存在且与 `S` 无关，(9-1) 才化归为一条标量方程。**这是 N03 的 O6 那一行的展开。**
2. **局部→全局缺权重 `w_v`**（N06-04）：`vol({q_v O_v}) = Σ_v w_v log‖q_v‖_v`；检索到的段落只讲 `O×` 不确定，没有给权重系统。
   没有 `w_v`，"局部到全局"就是一个带自由参数的公式。
3. **两套 log 之间根本没有桥**（N06-10）：`localLog` 取值在 `ℚ_p`（`CoreTransport/Basic.lean:9-10`），`logVol` 取值在 `ℝ`；
   `ℚ_p` 没有到 `ℝ` 的域嵌入。任何"log 相等"的写法都必须先给出一层比较映射，否则是换了对象。

## 已能引用的正面结论
- `averageOverLabels_eq_averageOverOrbit` **以 `hAct` 为假设**（`LabelNormalization.lean:165-169`，文件自述 `:84`、`:224`）；
  去掉 `hAct` 由同一文件的 `ZMod 3` 反例给出 2 vs 1（N06-06）。这两行是 `SOURCE_FACT` / `EXPERIMENTAL`，不是 `UNVERIFIED_MATH`。
- 稳定子重数 `Σ_{g∈G} f(g•base) = #Stab · Σ_{orbit} f`（N06-07）在玩具里已证；缺的是原文侧是否有对应因子。

## 未做 / 明确留白
- 没有算出任何 `logVol(out ι S)`；N06 只是把该算的东西列出来。
- `PadicPrincipalHull` 一行的行号未声称（只给声明文本），因为该文件的声明位置本轮未逐行核对。
- 不把浮点近似当恒等式；本表没有给出任何数值"验证"。
