# RiemannObserver

基于 **Molt 公理化体系** 对黎曼猜想（Riemann Hypothesis）的形式化表述与 $\mathcal{M}$ 证明框架。

**English:** Axiomatic framework (Molt) with metric μ=2 and Molt-primes $\mathbb{P}_{\mathcal{M}}=\{3,5,7,\ldots\}$; formalized in **Lean 4** (`formal/`). Two core papers (English PDFs): (1) *On the Limits of the Classical Foundation and the Legitimacy of Alternatives* (Gödel, Tarski, independence); (2) *Molt axiomatic framework* (RH in $\mathcal{M}$, mass gap, P≠NP, etc.). No claim that PA or ZFC is inconsistent.

### Core claims

- Classical foundations (PA, ZFC) cannot be proven uniquely correct (Gödel, Tarski, independence).
- Molt provides a logically consistent alternative perspective (different predicate, not contradiction).
- Key results in Molt: mass gap Δ=1>0, Riemann Hypothesis (in $\mathcal{M}$), P≠NP (dimensional isolation); formalized in Lean 4 where stated.

### Contents

| Item | Location |
|------|----------|
| **Lean 4 formalization** | [formal/](formal/) — run `lake build` in `formal/` to verify |
| **English papers** | `ProofClassicalLimits_EN.pdf` (limits of classical foundation), `main_EN.pdf` (Molt framework); build with `pdflatex ProofClassicalLimits_EN.tex` and `pdflatex main_EN.tex` |
| **Docs** | See [投稿完整教程](投稿完整教程_英文材料与完美准备.md), [绕过arXiv发布行动计划](绕过arXiv发布行动计划.md) |

### Status

- Axioms A1, A2, A3: ✓ formalized in Lean 4  
- Core lemmas (Ω, Δ), mass gap: ✓ verified  
- Consistency proof: ⏳ open  

---

## Quick links

| Item | Link |
|------|------|
| **Repository** | https://github.com/labaogao-cmd/RiemannObserver |
| **Formalization** | [Lean 4](formal/) — `lake build` in `formal/` |
| **English papers** | Build from `ProofClassicalLimits_EN.tex`, `main_EN.tex` (see above) |
| **Preprint (DOI)** | Optional — [Zenodo](https://zenodo.org) when you need a citable DOI |
| **Publish (tweet now)** | [立即发推_仅GitHub版](立即发推_仅GitHub版.md) — GitHub only, no Zenodo needed |

---

## 结构概览

| 部分 | 内容 |
|------|------|
| **共有公理基石** | $\mathcal{A}_1$ 湮灭守恒、$\mathcal{A}_2$ 度规 $\mu=2$ 与平庸子空间 $\mathbb{M}$、$\mathcal{A}_3$ 素数 $\mathbb{P}_{\mathcal{M}}=\{3,5,7,\ldots\}$ |
| **公理化体系** | 逻辑空间 $\mathbb{X}$、度规子空间、$\mathrm{Irr}(n)$、相位旋转 |
| **引理 1–2** | 2 的非素性、相位正交性（手性） |
| **定理 1** | 黎曼猜想：$\zeta_{\mu}$ 非平凡零点在 $\mathrm{Re}(s)=1/2$ |
| **解析映射** | $\zeta(s) = \mathcal{M}(s)\zeta_{\mu}(s)$；度规剥离（$\eta$）；零点同轨 $\Rightarrow$ 经典 $\zeta$ 零点在 1/2 |
| **定理 2** | 哥德巴赫：度规填充定理（$N \in \mathbb{M} \Rightarrow \exists P_1,P_2 \in \mathbb{P}_{\mathcal{M}},\ P_1 \oplus P_2 = N$） |
| **定理 3** | P $\neq$ NP：维度隔离定理（度规流 $\subset$ 相位流） |
| **定理 4** | 杨-米尔斯质量间隙：$\Delta = \inf \mathbb{P}_{\mathcal{M}} - \mu = 1 > 0$ |
| **定理 5** | 纳维-斯托克斯：相位平滑定理（光滑解、度规吸收阱） |
| **定理 6** | BSD 猜想：相位共振定理（有理点秩 = $L(s=1)$ 零点阶数） |
| **定理 7** | 霍奇猜想：逻辑投影定理（拓扑循环 = 代数循环的相位生成） |
| **定理 8** | 孪生素数猜想：相位捆绑定理（无穷多孪生对、度规步长相干回响） |
| **定理 9** | ABC 猜想：度规溢出定理（相位复杂度与空间填充率边界） |

在 $\mathcal{M}$ 内为达成“完美解决”（含义 A），每一定理均配有**形式定义**与**公理**；并有一节**从 $\mathcal{A}_1,\mathcal{A}_2,\mathcal{A}_3$ 推导七条扩展公理**：维度隔离、度规吸收、逻辑投影、度规溢出、相位共振可由底层公理直接或定义性推出；度规填充与孪生无穷在承认一条由 $\mathcal{A}_1$ 与定理 1 / $\mathbb{P}_{\mathcal{M}}$ 无穷性支持的引理后亦可推出。

## 文件（核心）

- **`ProofClassicalLimits_EN.tex`** / **`ProofClassicalLimits_EN.pdf`** — 举证论文（英文）：经典体系之限与根基替代（Gödel、Tarski、独立性），不声称 PA/ZFC 不一致。
- **`main_EN.tex`** / **`main_EN.pdf`** — 体系中的论证（英文）：Molt 公理、黎曼/哥德巴赫/P≠NP/质量间隙/N-S/BSD/霍奇/孪生/ABC。
- **`main.tex`** — 完整公理化叙述与证明的 LaTeX 源文件（含逻辑领域声明、公理/定义补全、黎曼/哥德巴赫/P≠NP/质量间隙/NS/BSD/霍奇/孪生/ABC、解析映射与 $Z_{\mu}$）。
- **`preprint.tex`** — 学术预印本：*On the Metric Reconstruction of Prime Definition and the Analytic Proof of the Riemann Hypothesis*（Molt-Phase Logic Research Group, 2026-02-07；摘要、引言、公理、解析映射、RH 证明、统一场扩展、结论、参考文献）。
- **`preprint_meaning_B.tex`** — 面向含义 B 的英文预印稿：*On the Metric-Phase Separation of the Riemann Zeta Function and the Chirality of Prime Rotations*（Molt-RH-B）。纯分析表述：$\mathcal{M}(s)$ 与 $\zeta_{\mu}$ 的定义、Separation Identity、Iso-Zero Principle（临界带内 $\zeta$ 与 $\zeta_{\mu}$ 零点一致）、Phase Chirality 与 Modulus Convexity 猜想。
- **`评估_Meaning_B草稿.md`** — 对 Metric-Phase Separation 稿的用途评估：有用性、与现有文档的关系、待补强处。
- **`scripts/figure1_metric_stripping.py`** — 论文 Figure 1 的 Python 仿真：临界线上 $|\zeta(1/2+it)|$ 与 $|\zeta_{\mu}(1/2+it)|$ 的对比（同零点性）、以及 $\sigma=0.8$ 时包络抬升（模长凸性）。输出为 `figures/figure1_metric_stripping.pdf` 与 `figures/figure1_envelope_off_critical.pdf`。
- **`figures/`** — 存放生成的图表（PDF）；预印本中通过 `\includegraphics{figures/figure1_metric_stripping.pdf}` 引用。
- **`audit_axioms.md`** — 公理化体系审核报告（在自定义逻辑领域内审查完整性、缺失项与补充建议）。
- **`深度解析_世纪难题.md`** — 在自定义逻辑领域与标准数学意义下对世纪难题“完美解决”的实事求是评估。

## 编译

需要支持中文的 LaTeX 引擎（如 XeLaTeX 或 LuaLaTeX）及 `ctex` 宏包：

```bash
xelatex main.tex
```

或使用 latexmk：

```bash
latexmk -xelatex main.tex
```

## 说明

- 黎曼猜想：$\zeta(s)$ 的所有非平凡零点满足 $\mathrm{Re}(s)=1/2$（临界线）。
- 本仓库将 $\mathbb{X}$ 视为复数域上的相位流形，用度规 $\mu=2$ 与湮灭公理推导零点重心 $s_{\mathrm{center}}=1/2$，属几何/物理风格的形式化尝试，供学习与讨论。

## 许可与引用

- **License:** 学术与教育使用。代码部分可选用 MIT 或 Apache-2.0；文稿可选用 CC-BY-4.0（见仓库内 LICENSE 或文稿首页）。
- **Citation:** 若使用 Zenodo 发布，请引用 DOI。引用或延拓时请注明 RiemannObserver 与 Molt 公理化框架。
