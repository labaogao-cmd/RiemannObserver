/-
# Molt 体系定义 (main.tex §2 公理化体系建立)

逻辑空间、度规子空间 M、不可约 Irr、Molt-素数集 ℙ_ℳ 等。
-/

import RiemannObserver.Axioms

namespace RiemannObserver

/-- 乘法意义下不可约：n > 1 且 n = a*b => a=1 或 b=1。
    对应 main.tex 定义 A-不可约 的乘法不可约部分。 -/
def MulIrreducible (n : Nat) : Prop :=
  1 < n ∧ ∀ a b : Nat, a * b = n → a = 1 ∨ b = 1

/-- **度规子空间 M（平庸子空间）**：由 mu=2 生成的偶数正整数的集合 M = {2, 4, 6, ...}。
    对应 main.tex Definition 度规子空间与度规项。 -/
def inM (n : Nat) : Prop :=
  0 < n ∧ n % mu = 0

/-- **度规项判定** Psi(n) = True 当且仅当 n in M。 -/
def Psi (n : Nat) : Bool :=
  0 < n && n % mu = 0

/-- **M-不可约 Irr(n)**：乘法不可约且不在度规子空间 M 中（即 n 为奇素数）。
    对应 main.tex Definition A-不可约 与 PM。 -/
def Irr (n : Nat) : Prop :=
  MulIrreducible n ∧ ¬inM n

/-- **Molt-素数集 PM**：Irr(n) 的 n 的集合，即 {3, 5, 7, ...}。
    在 Lean 中表述为谓词：n in PM ↔ Irr(n)。 -/
def PM (n : Nat) : Prop :=
  Irr n

/-- Span(mu) 与 M 一致：n in M <-> n 为正偶数。 -/
theorem inM_iff_even_pos (n : Nat) :
    inM n ↔ 0 < n ∧ n % 2 = 0 := by
  unfold inM mu; rfl

/-- 2 属于度规子空间 M。对应 main.tex：2 in Metric。 -/
theorem two_in_M : inM 2 := by
  unfold inM mu
  decide

/-- 2 是乘法不可约的（标准意义下 2 是素数），但 2 in M，故 2 not in PM 由定义保证。 -/
theorem two_MulIrreducible : MulIrreducible 2 := by
  unfold MulIrreducible
  constructor
  · decide
  · intro a b h
    match a with
    | 0 => simp at h
    | 1 => left; rfl
    | a' + 2 =>
      right
      match b with
      | 0 => simp at h
      | 1 => rfl
      | b' + 2 =>
        exfalso
        have le2a : 2 ≤ a' + 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a'))
        have le2b : 2 ≤ b' + 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le b'))
        have ineq : 4 ≤ (a' + 2) * (b' + 2) := by rw [show 4 = (2 : Nat) * 2 from rfl]; exact Nat.mul_le_mul le2a le2b
        rw [h] at ineq
        exact (by decide : ¬4 ≤ 2) ineq

end RiemannObserver
