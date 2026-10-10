# Erdős #206 具体构造的形式化

本目录形式化的是原稿的一个确定性有理嵌套区间构造。它定义具体实数 `Egyptian.explicitReal`，而非仅用“几乎处处”定理证明存在。

## 已证明的完整结论

`Egyptian.explicit_counterexample` 无额外研究假设，证明：

\[
  \frac14<x<\frac13,\qquad x\text{ 超越},\qquad
  x\text{ 不存在最终最优的严格递增无限分母链}.
\]

此外，`Egyptian.approximation n : ℚ` 是具体有理数算法，且内核证明

\[
 \left|x-\operatorname{approximation}(n)\right|\le 2^{-n-1}
 \quad(n\ge0).
\]

`explicitReal_no_eventually_optimal_sequence` 用原始最大值记号直接证明

\[
 \neg\exists (m_k)_{k\ge0},n_0:
 0<m_0<m_1<\cdots,\quad
 \sum_{k<n}m_k^{-1}=R_n(x)\ \text{对所有 }n\ge n_0.
\]

`Rn_attained` 证明每个 `x>0`、每个阶数的最大值确实取到。
`bestUnder_iff_sum_eq_Rn` 证明“对所有同长可行前缀最优”与该最大值的等价关系。最优表示可以并列；形式化覆盖全部候选链。

## 证明链与文件

| 文件 | 内核核验的作用 |
|---|---|
| [Basic.lean](Egyptian/Basic.lean) | 严格递增正分母前缀、全部同长竞争者、最佳追加强制使用最小允许分母 |
| [Greedy.lean](Egyptian/Greedy.lean) | 有理贪心步骤、有限跨越、调和级数终止论证、上限稳定性、最佳链延伸 |
| [BadPair.lean](Egyptian/BadPair.lean) | 原稿的全部二项不等式与分母顺序，坏区间搜索有解 |
| [Defeat.lean](Egyptian/Defeat.lean) | 同长可行替换严格击败候选最佳链 |
| [PrefixInterval.lean](Egyptian/PrefixInterval.lean) | 任意前缀、任意有理区间的统一排除；保留原稿记录的上限取最小值 |
| [FastSearch.lean](Egyptian/FastSearch.lean) | 两候选精确搜索，证明与原最小整数搜索逐输入相等，不改变构造出的数 |
| [PrefixEnumeration.lean](Egyptian/PrefixEnumeration.lean) | 二进制支持集枚举所有有限合法前缀，附反向编码证明 |
| [PolynomialEnumeration.lean](Egyptian/PolynomialEnumeration.lean) | 原稿高度、次数、系数字典序；非零性、完整覆盖、搜索终止与有理转换 |
| [PolynomialGrid.lean](Egyptian/PolynomialGrid.lean) | 有限网格必有非根，选择最小成功网格点 |
| [Intervals.lean](Egyptian/Intervals.lean) | 多项式定量界、四项半径、闭区间排根、唯一极限和误差控制 |
| [Chains.lean](Egyptian/Chains.lean) | 原始无限分母链表述与有限前缀排除的连接 |
| [MaxExists.lean](Egyptian/MaxExists.lean) | 每阶最大值存在、`Rn` 与普遍最优性等价 |
| [Construction.lean](Egyptian/Construction.lean) | 完整有理递归、所有前缀和多项式的排除、超越性与误差界 |
| [Main.lean](Egyptian/Main.lean) | 实例化全部枚举与终止证明；最终定理没有上述过程作为待证明假设 |
| [Checks.lean](Egyptian/Checks.lean) | 最终定理公理输出、实际执行和精确初始值检查 |

实数用唯一公共点定义，有理近似以可执行代码给出。经典选择只在实数及证明层使用；没有借助它在算法层选择一个未指定的区间或多项式。数学意义的可计算性由总有理算法和已证明的精度界体现。本目录没有另外把算法编码为 Mathlib 的 `Partrec`／图灵机谓词。

## 固定环境与复核

Lean：`leanprover/lean4:v4.35.0-rc2`，编译器提交 `11acb17ec6b07a8f9e9173e6845197929540936b`。

Mathlib：`v4.35.0-rc2`，精确提交 `065356127b1dc0016f66b7283ce0ce2c4055aa55`。完整依赖固定在 `lake-manifest.json`。

独立环境可在本目录执行：

```sh
lake exe cache get
lake build
lake env lean Egyptian/Checks.lean
```

原验收源码保持只读，公开副本迁移到固定的新环境。每个 Lean 源文件首行是 `module`；构造库使用公开导入和暴露的公开定义，运行检查补充相应的 meta 导入。报告与日志记录实际执行结果，不将网页中别人写出的 `#print axioms` 注释当成本次核验。

## 本次验收结果

2026-10-10，Lean 4.35.0-rc2 下全部默认目标（`Egyptian`、`Challenge`、`Solution`）已编译通过，`Checks.lean` 独立运行成功。最终完整运行约 9.27 秒，十三项实际公理输出（十二项构造结果及一个发布接口定理）均仅为 `propext`、`Classical.choice`、`Quot.sound`。它们包括主定理、原始 `Rn` 表述、精度界、枚举覆盖和加速等值定理。新版发布接口的全量验收结果见 [VERIFICATION_LOG.txt](VERIFICATION_LOG.txt)。

`Egyptian` 证明库及完成的 `Solution.lean` 没有 `sorry`、`admit`、自定义 `axiom`、`unsafe`、`native_decide` 或 `implemented_by`。独立问题声明 `Challenge.lean` 刻意保留两个值接口和一个定理证明占位，这是 Palomar 的比较格式；它不是已完成的证明文件。主定理已实例化全部枚举与终止论证，没有把过程完整性留下为待证明假设。

新环境下独立执行了阶段 0–12 的全部区间，13 对有理端点与原精确证书完全相同，最终复核用时约 9.20 秒，见 [EXECUTION_CROSSCHECK.json](EXECUTION_CROSSCHECK.json)。有限执行用于核对具体值；无限结论来自已编译的定理。快速索引函数与原最小搜索的逐输入等值定理确保该加速保留整条递归。

迁移的必要兼容改动包括：新版多项式的 `AddMonoidAlgebra` 构造包装、显式的 cast hom 与一步分母改写、两个已更名定理，以及新模块系统的导入与可见性。原始高度／次数／系数字典序、二进制前缀枚举、上限最小值、最小索引、网格和半径公式均保留。

Python 示例保留原构造的数学运算，超时时保存已经完整验证的阶段；零阶段、完成一阶段后中途超时和正常三阶段的检查已通过。该有限示例不用于证明无限范围定理。

## 数学及优先权边界

此定理涉及严格不同分母的最佳下逼近，所有长度与所有最优链；它不是“某一条初始贪心表示失败”的有限例子。误差定理对所有自然数成立；有限运行仅检查实现的具体值。

Erdős–Graham 1980 原书第 31 页已经断言可以构造失败无理数；Kovač 已经证明 #206 的主测度结论，本稿局部二项障碍也来自其式 (2.1)。有效 Baire／嵌套区间方法已有文献。本目录的形式化完成与全球新颖性或公开优先权互不推出。

公开文献与版本的比较另行进行了有限范围审计。公开文献检索未找到等价完整有效递归；未公开结果、出版全文缺口与作者对“explicit”含义的确认仍不能通过检索排除。此代码仓库不据此宣称外部作者或问题维护者已经确认构造请求或优先权。

## 发布接口与版权

独立问题声明见 [Challenge.lean](Challenge.lean)，完成的解答见 [Solution.lean](Solution.lean)，比较配置见 [comparator.json](comparator.json)。论文另由 Zenodo 分发，不包含在代码仓库中。

Copyright © 2026 Yuhang Shi，Zhengzhou University，[ORCID](https://orcid.org/0009-0006-3180-4767)。原创代码采用 [AGPL-3.0-only](../LICENSE)，Lean、Mathlib 与其他依赖保留各自许可证。
