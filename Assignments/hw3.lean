/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use
import Library.Theory.Parity

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

-- Example 2.5.2

/- 3 points -/
theorem p252 {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
-- ^ Given ^
-- Exercise solution starts here
  sorry

-- Example 2.5.6

/- 3 points -/
theorem p256 (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  sorry

-- Example 2.5.7

/- 4 points -/
theorem p257 {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  sorry

-- Exercise 2.5.9.5

/- 3 points -/
theorem p2595 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

-- Exercise 2.5.9.6
-- proof assuming t=1 and reaching a contradiction

/- 3 points -/
theorem p2596 {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry


-- Exercise 2.5.9.7

/- 4 points -/
theorem p2597 {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry
