# 独立局部域验证工程

本目录使用现有 Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0` 与 Lean `4.34.0-rc2`。父工程使用 Lean `4.34.0`；两套编译产物不能相互导入。路径依赖只读复用本机已有编译库，没有安装新工具链或修改数竞工程的源码。

`LocalFieldAudit/Shell.lean` 的五个定理依次证明：给定线性等价保持集合 L，则保持其任意标量缩放；相应成员资格等价；有明确非零元素 layer/measurement 对应时保持阈值；真实 ℚ_p 模块的特化；真实 ℚ_p 范数单位球的所有 p^n 缩放层保持。

L 作为任意集合处理，避免把 ℤ_p 格误作 ℚ_p 子空间。有关测量的定理明确排除零元素，利用线性等价的单射性证明像也非零。实际 log_p(O×) 的描述、有限扩张的分歧条件、Ism 对全部 open-H 格的作用以及 IUT packet 实现仍未建立。

第四轮 `LocalFieldAudit/Filtration.lean` 新增 14 个定理，使用实际 ℤ_p 最大理想及其幂的像，证明与 ℚ_p 范数球、非零元素估值及严格整数阈值的对应；再实例化 Shell 接口，去掉基域情形中的额外 layer/measurement 假设。另有实际乘以 p 的线性同构严格缩球例子。全部结论仍限于准确声明的基域对象和显式保持条件。

第五轮 `LocalFieldAudit/ContinuousLinearity.lean` 新增五个定理：从连续加法同态证明 ℚ_p 标量相容，再导出标量层、实际理想幂像、非零元素估值及包含零的范数保持。源和目标各有 ℚ_p 模结构、拓扑及连续标量乘法，目标为 Hausdorff；集合像相等仍须显式证明。两个连续线性映射／线性等价构造作为辅助定义参与依赖追踪，不另计事实节点。没有构造真实 Ism、log 坐标或联合 seed。

在本目录执行：

```powershell
python tools/verify.py
python tools/query.py padic
python tools/query.py --deep scalar_layer
```

验证器先执行 `lake --no-cache --wfail build LocalFieldAudit`，同步 Lake 的依赖追踪记录，再对本目录源码执行零诊断 Lean 检查、导出项目声明并检查传递公理。本轮构建复用了已有外部编译依赖；只运行裸 `lean -o` 会缺少 Lake 追踪记录，导致编辑器拒绝过期 imports。外部库常量作为工具链依赖记录，不作为已逐项 VS Code 验收的事实节点。`external-lock.json` 固定现有源码仓库身份；源快照前后检查这些 checkout 未变，并对实际导入编译产物及 Lean/Lake 二进制取哈希。

VS Code 验收入口是 `tools/EditorCheck.lean`，当前预期 48 条 information、0 error、0 warning；三个证明源文件最后的对应证明也须实际显示 `No goals`。实际验收前只保留候选，不准入 fact-tree。最终状态查看本目录的 `fact-tree/facts.json`。

第三轮（当时入口为 10 条 information）完成验收：5 个定理准入、4 条依赖边、0 个待验收。该轮观察、凭据、工具与图现在保存于 `verification/round3/`。

第四轮验收时为 19 个准入节点、21 条依赖边、0 个待验收，证据与工具归档在 `verification/round4/`；详细范围见父目录 `research/round4-results.md`。

第五轮验收后为 **24 个准入节点、31 条依赖边、0 个待验收**。当前观察为 `verification/vscode-observation-round5.txt`，凭据为 `verification/vscode-receipt.json`；CLI 源码零诊断、公理白名单及辅助定义依赖追踪均通过。实际编辑器入口显示 48 条信息、0 error、0 warning，三份证明均取得匹配 InfoView 的 `No goals`。范围、假设及工程恢复见父目录 `research/round5-results.md`、`GAP-round5-editor.md`。

父目录的 `python tools/forest.py query 关键词 --deep` 可同时查询两套已验收图；该总入口不构造跨工具链证明。
