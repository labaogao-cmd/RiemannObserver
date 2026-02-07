/-
# RiemannObserver — Molt 公理化体系形式化

本库对 main.tex 中的公理、定义与关键引理进行 Lean 4 形式化，使证明可机器检查。

## 对应关系
- **Axioms.lean** — §1 共有公理基石 (𝒜₁, 𝒜₂, 𝒜₃)
- **Definitions.lean** — §2 公理化体系建立 (M, ℙ_ℳ, Irr, Ψ)
- **Lemmas.lean** — 引理 1 (2∉ℙ_ℳ)、引理 Ω、引理 Δ、杨-米尔斯质量间隙

## 使用
在项目中 `import RiemannObserver` 即可使用所有形式化结果。
-/

import RiemannObserver.Axioms
import RiemannObserver.Definitions
import RiemannObserver.Lemmas
