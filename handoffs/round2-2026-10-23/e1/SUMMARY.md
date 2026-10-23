# E1 返修：快速入口正常退出，总超时覆盖进程清理

修复前同一工作树实测：`python -B audit/tests/test_mutation_probe_exit.py` 打印 7/7 后墙钟 167.3 s，已超复核方 150 s 预算；
复核方另等约 445 s 的原因同样定位到了：子进程把 stdout/stderr 管道继承给孙进程，超时杀掉直接子进程后 `communicate()` 仍在等 EOF。

两处改动（都在冻结允许路径内，未删任何既有断言；新增的临时脚本已折回测试文件并删除）：
1. 去重：M1–M8 矩阵与全部健康探针只在 baseline 用例跑一次；失败用例用 `--reuse-probes` 复用这些**真实**结果，
   被注入的探针仍真实运行；复用前提是仓库字节指纹一致，伪造指纹 → exit 2（已测）。
2. 快速入口自带总期限：无参调用在子进程里跑用例，流写**文件**而非管道，一个硬墙钟期限涵盖杀树与回收；
   Windows 用 job object（`KILL_ON_JOB_CLOSE` + `TerminateJobObject`）——实测 `taskkill /T /F` 在此环境报
   Access denied、孙进程存活。超时即 124 INCOMPLETE。

实测（HEAD `24f42c64ba6ec61a693926d7956268e955a5b15`，退出码由独立父进程取得，不取 stdout 末行）：
快速入口 exit **0**，**34.49 s**，日志 `logs/e1-fast-entry.*`。超时自证 `--self-test-timeout`：子进程+孙进程挂死，
3 s 期限下 **3.4 s** 返回 124 且孙进程被回收（exit 0）。反向对照：把 `probe_violations` 还原成旧行为 →
**6/7 用例失败**（exit 1，119.22 s），说明用例仍抓得住原缺陷。discovery **exit 0**，72 项（既有 65 + 新增 7）全绿，150.43 s。
退出契约传播 `exit_contracts.py` exit 0（0.56 s）。

> 旧 bundle 描述的是 `e9ff362`——那版把「job object 建立失败时告警」删掉了；分支保留该告警，
> 故其上全部测量作废重测（旧日志归档在 `logs-superseded-e9ff362/`）。

未解决：本工作树路径含 "ü"，`test_tcb_manifest` 子进程解码在本机失败（E3 文件、本次未改，`PYTHONIOENCODING=utf-8` 后全绿）；
本沙箱禁止写 `mkdtemp(0o700)` 目录，故此处回放需 sitecustomize 仅改 `os.mkdir` 的 mode，不属本次提交。本次无 Lean 运行与编辑器观察。
