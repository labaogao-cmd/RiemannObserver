# RiemannObserver 形式化验证 (Lean 4)

本目录包含 [RiemannObserver](../main.tex) Molt 公理化体系的 **Lean 4** 形式化，使公理、定义与关键引理**机器可检查**。

## 与 main.tex 的对应

| 文件 | main.tex 位置 | 内容 |
|------|----------------|------|
| `RiemannObserver/Axioms.lean` | §1 共有公理基石 | 𝒜₁ 湮灭守恒、𝒜₂ 度规 μ=2、𝒜₃ 通过 ℙ_ℳ 定义 |
| `RiemannObserver/Definitions.lean` | §2 公理化体系建立 | M、Irr、ℙ_ℳ、Ψ，以及 2∈M、2 乘法不可约 |
| `RiemannObserver/Lemmas.lean` | 引理 1、Ω、Δ，杨-米尔斯 | 2∉ℙ_ℳ，3∈ℙ_ℳ，质量间隙 Δ=1>0，引理 Ω 的 Span 表述 |

## 已形式化并可机器验证的结果

- **引理 1** (`two_not_in_PM`)：2 ∉ ℙ_ℳ
- **引理 Δ** (`lem_Delta`)：质量间隙 Δ = 1 > 0（度规量子化）
- **杨-米尔斯质量间隙** (`yang_mills_mass_gap`)：存在 Δ > 0，且 Δ = 1
- **引理 Ω** (`lem_Omega_span`)：M 中元素均为 μ 的正整数倍

## 构建与检查

需先安装 [Lean 4](https://lean-lang.org/lean4/) 与 [Lake](https://github.com/leanprover/lake)（通常随 elan 安装）：

```bash
cd formal
lake build
```

成功执行 `lake build` 即表示当前形式化通过类型检查与证明检查。

## 依赖

当前仅依赖 Lean 4 标准库，未使用 Mathlib，便于在无网络环境下构建。若需扩展（如解析数论、实分析），可后续在 `lakefile.toml` 中添加 Mathlib 依赖。

## 扩展方向

- 黎曼猜想：需复分析/亚纯函数与 ζ_μ 的定义，可先以公理或陈述形式接入。
- N-S、ABC、P≠NP、BSD 等：可在现有公理与引理基础上逐步形式化陈述与可证部分。
