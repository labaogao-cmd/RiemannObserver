/-
Molt axiomatic foundation (main.tex section 1).
A1: annihilation 1+(-1)=0. A2: metric mu=2, M = {2,4,6,...}. A3: PM in Definitions.lean.
-/

namespace RiemannObserver

/-- Axiom A1 (annihilation): 1 + (-1) = 0. -/
axiom A1_annihilation : 1 + (-1 : Int) = 0

/-- Axiom A2: metric mu = 2, M = {2,4,6,...}. -/
def mu : Nat := 2

axiom A2_metric : mu = 2

end RiemannObserver
