# 对诸多开问题的形式化收集

一个独立的 Lean 4 仓库，用于形式化不同数学领域文献开问题的定义、局部引理、反例与完整结论。项目按原论文和问题编号组织；数学证明、文献开放状态、原创性判断分别记录。

当前项目：

| 项目 | 来源 | 已核验范围 | 未完成或待外部核验 |
| --- | --- | --- | --- |
| [IdealSpectra](OpenProblemFormalizations/IdealSpectra/README.md) | Benhamou, *Scales in the Point Spectrum*, arXiv:2603.00305v1, Questions 3.17–3.18 | N02 的三测试对象反证及理想性质；N04 的可数边界引理 | N04 的一般问题、N02 的文献优先权及外部评审 |
| [IdealWebs](OpenProblemFormalizations/IdealWebs/CountableLevels.lean) | Hernández-Hernández–Hrušák–Rivas-González, *The bounded topology*, Conjecture 4.14 | 递增遗传层覆盖中的序列 web 固定层引理；拉回理想中序列 web 的直接像引理；有限选择性质下 sun 逐项有限删改的稳定性引理 | E05 的一般二分法及 flat 理想判别仍为纸笔审计，未形式化 |

依赖 Lean 4.30.0 与 mathlib4 v4.30.0。运行 `lake build`、`lake env lean Check.lean`、`lake env lean Audit.lean` 或 `./verify.ps1`。检查结果见 [verification/manifest.json](verification/manifest.json)。

本仓库不依赖 `InfinitaryCombinatorics` 项目；其中的 R0/A1 留在无穷组合仓库。


