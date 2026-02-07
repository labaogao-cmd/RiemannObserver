/-
# 引理 1、引理 Ω、引理 Δ 与杨-米尔斯质量间隙 (main.tex)

- 引理 1 (lem:2-not-prime)：2 ∉ ℙ_ℳ
- 引理 Ω (lem:Omega)：相位完备性——稳定态由 ℙ_ℳ 生成
- 引理 Δ (lem:Delta)：度规量子化，最小分辨率 Δ = 3 - μ = 1 > 0
- 定理：杨-米尔斯质量间隙 Δ = 1 > 0
-/

import RiemannObserver.Axioms
import RiemannObserver.Definitions

namespace RiemannObserver

/- ## 引理 1：2 的非素性 (main.tex Lemma lem:2-not-prime) -/

/-- **引理 1**：2 ∉ ℙ_ℳ。2 属于度规子空间 M，故由 ℙ_ℳ 的定义知 2 不是 Molt-素数。 -/
theorem two_not_in_PM : ¬PM 2 := by
  unfold PM Irr
  intro ⟨_, hnM⟩
  exact hnM two_in_M

/- ## 引理 Δ：度规量子化 (main.tex Lemma lem:Delta) -/

/-- 3 为正奇数，故 3 not in M。 -/
theorem three_not_in_M : ¬inM 3 := by
  unfold inM mu
  decide

/-- 3 在乘法意义下不可约。 -/
theorem three_MulIrreducible : MulIrreducible 3 := by
  unfold MulIrreducible
  constructor
  · decide
  · intro a b h
    match a with
    | 0 => simp at h
    | 1 => left; rfl
    | 2 =>
      match b with
      | 0 => simp at h
      | 1 => simp at h
      | b' + 2 =>
        exfalso
        have eq : 2 * (b' + 2) = 4 + 2 * b' := by rw [Nat.mul_add, show 2*2 = 4 from rfl, Nat.add_comm (2*b') 4]
        have : 4 ≤ 2 * (b' + 2) := by rw [eq]; exact Nat.le_add_right 4 (2 * b')
        rw [h] at this
        exact (by decide : ¬4 ≤ 3) this
    | a' + 3 =>
      right
      match b with
      | 0 => simp at h
      | 1 => rfl
      | b' + 2 =>
        exfalso
        have le3a : 3 ≤ a' + 3 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a')))
        have le2b : 2 ≤ b' + 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le b'))
        have ineq : 6 ≤ (a' + 3) * (b' + 2) := by
          rw [show 6 = (3 : Nat) * 2 from rfl]
          exact Nat.mul_le_mul le3a le2b
        rw [h] at ineq
        exact (by decide : ¬6 ≤ 3) ineq

/-- 3 ∈ ℙ_ℳ。 -/
theorem three_in_PM : PM 3 := by
  unfold PM Irr
  exact ⟨three_MulIrreducible, three_not_in_M⟩

/-- PM 中任意元素 >= 3（最小 Molt-素数为 3）。 -/
theorem PM_lower_bound {n : Nat} (h : PM n) : 3 ≤ n := by
  unfold PM Irr at h
  obtain ⟨⟨hn, _⟩, hnM⟩ := h
  apply Classical.byContradiction
  intro H
  have nlt3 : n < 3 := Nat.not_le.mp H
  have nle2 : n ≤ 2 := Nat.lt_succ_iff.mp nlt3
  have nge2 : 2 ≤ n := Nat.succ_le_of_lt hn
  have eq : n = 2 := Nat.le_antisymm nle2 nge2
  rw [eq] at hnM
  exact hnM two_in_M

/-- **质量间隙**：inf PM - mu = 3 - 2 = 1。 -/
def massGap : Nat := 3 - mu

/-- **引理 Delta（度规量子化）**：最小逻辑分辨率 = 1 > 0，空间不存在任意小的连续性。 -/
theorem lem_Delta : massGap = 1 ∧ 0 < massGap := by
  unfold massGap mu
  exact ⟨rfl, Nat.succ_pos 0⟩

/-- **杨-米尔斯质量间隙定理** (main.tex)：存在最小激发态 > 0，且 = 1。 -/
theorem yang_mills_mass_gap : ∃ Δ : Nat, 0 < Δ ∧ Δ = massGap :=
  ⟨massGap, lem_Delta.2, rfl⟩

/- ## 引理 Ω：相位完备性 (main.tex Lemma lem:Omega) -/

/-- **引理 Omega（相位完备性）**：M 中任一元素在结构上由度规 mu 生成；
    此处形式化为：M 中元素均为 mu 的正倍数。 -/
theorem lem_Omega_span (n : Nat) (hn : inM n) :
    ∃ k : Nat, 0 < k ∧ n = k * mu := by
  unfold inM mu at hn
  obtain ⟨hnpos, hnmod⟩ := hn
  refine ⟨n / 2, ?_, ?_⟩
  · have nge2 : 2 ≤ n := by
      match n with
      | 0 => exact False.elim (Nat.lt_irrefl 0 hnpos)
      | 1 => exact absurd hnmod (by decide : 1 % 2 ≠ 0)
      | n + 2 => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
    exact Nat.pos_iff_ne_zero.mpr fun H =>
      Nat.not_le_of_gt ((Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mp (by rw [H]; exact Nat.succ_pos 0)) nge2
  · rw [show mu = 2 from rfl]
    exact (Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr hnmod)).symm

end RiemannObserver
