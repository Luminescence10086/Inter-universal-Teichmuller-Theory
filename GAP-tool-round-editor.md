# GAP：本轮工具编辑器准入尚未完成

日期：2026-10-22。适用：`model-tools/run.py` 所调用的 HullTool / LedgerTool 新增辅助证明及生成证书。

命令行已经对代表输入实际执行 Lean，零 warning/error，并核对 `#print axioms`。这不代替用户要求的实际 VS Code 准入。

本轮先遇到工作区受限模式，用户已经回复处理。随后应用窗口被最小化/关闭；重新打开应用后，原生文件选择框的输入调用没有把路径写入可观察的文件名字段，部分调用返回缓存元素不可用。有限次恢复后仍未得到新增 Lean 文件、InfoView 和 Problems 的实际验收画面，因此停止重复 UI 操作。

状态：OPEN。不得将本轮新增定理加入正式 fact-tree 或宣称全部准入完成。已有命令行证书状态保留，其含义仅是该证书经过 Lean CLI 核验。

关闭条件：在各自锁定工程中打开 `Candidates/HullTool.lean`、`Candidates/LedgerTool.lean`，以及对应 `Candidates/Generated/<sha256>.lean` 代表证书，实际观察处理完成且零错误、零警告；记录源文件及证书哈希。无需为关闭此 GAP 重跑整套 IUT 审计。
