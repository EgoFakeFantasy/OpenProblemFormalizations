# 对诸多开问题的形式化收集

一个独立的 Lean 4 仓库，用于形式化不同数学领域文献开问题的定义、局部引理、反例与完整结论。项目按原论文和问题编号组织；数学证明、文献开放状态、原创性判断分别记录。

当前项目：

| 项目 | 来源 | 已核验范围 | 未完成或待外部核验 |
| --- | --- | --- | --- |
| [IdealSpectra](OpenProblemFormalizations/IdealSpectra/README.md) | Benhamou, *Scales in the Point Spectrum*, arXiv:2603.00305v1, Questions 3.17–3.18 | N02 的三测试对象反证、理想性质及精确 cohesive 类；任意预序上的两种 Tukey 映射定义等价；N04 的可数边界引理 | N04 的一般问题、N02 的文献优先权及外部评审 |
| [IdealWebs](OpenProblemFormalizations/IdealWebs/CrossingGauge.lean) | Hernández-Hernández–Hrušák–Rivas-González, *The bounded topology*, Conjecture 4.14 | 递增遗传层与有限选择引理；crossing 活动行、理想封闭、有界集仅有有限多条无限行；在抽象行规范假设下，单行有限集族是 web，其有限坐标逼近族包含完整横行可数 sun，故不是 web | E05 反例仍在审查；尚未形式化有限成本子测度的构造、Cantor 闭包与有限坐标逼近的等价或排除不可数 sun 的抽稀证明，也没有外部审稿 |
| [CohenCoherence](OpenProblemFormalizations/CohenCoherence/CofinalGraphCover.lean) | Bannister, *Nonvanishing Higher Derived Limits without weak diamond*, Question 8.3 | 可数有向偏序上的可数图覆盖有一张图在每个上锥内出现共尾星形邻域 | 二维相干族的 Cohen 保持问题；图论引理不能自动给出覆盖共同定义域的路径 |

依赖 Lean 4.30.0 与 mathlib4 v4.30.0。运行 `lake build`、`lake env lean Check.lean`、`lake env lean Audit.lean` 或 `./verify.ps1`。检查结果见 [verification/manifest.json](verification/manifest.json)。

本仓库不依赖 `InfinitaryCombinatorics` 项目；其中的 R0/A1 留在无穷组合仓库。

N02 的后续结构性推论也已形式化：矩形 cohesive 类存在统一代表，当且仅当两个因子在 Tukey 序中可比较。候选代表无需预设为有向；证明会从它到因子的 Tukey 归约推出有向性。此项是已核验精确分类的推论，不是对 N04 或文献优先权的新断言。

2026-09-26 修正：E05 原有自然数值规范接口的全局单调性与无限集初段发散条件不能同时成立。现改为仅对有限上集要求单调的 `FiniteGaugeMonotone`，并以 `countingGauge` 给出修正接口的具体见证。该见证没有 E05 额外需要的不相交块压缩性质，因此不代表完整反例已经形式化。完整说明见 [verification scope](VERIFICATION_SCOPE.md)。

