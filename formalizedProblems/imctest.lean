/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Test] }

/-!
# Math Contest Name, Problem 0

https://adam.math.hhu.de/#/g/hhu-adam/robo/world/Piazza/level/10

Prove {2, 7} ⊆ {2} ∪ { n : ℕ | Odd n}

-/

namespace testProblem1

problem test_problem : {2, 7} ⊆ {2} ∪ { n : ℕ | Odd n} := by
  intro x hx
  obtain l | r := hx
  · tauto
  right
  simp_all
  decide


end testProblem1
