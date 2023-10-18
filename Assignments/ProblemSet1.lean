import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

/- 4 points -/
theorem Problem3a {p q r : Prop}(h :  p ∧ q → r): p → (q → r) := by
  sorry

/- 4 points -/
theorem Problem3b {p q r : Prop}(h: p→ (q → r)): (p → q) → (p → r) := by
  sorry

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

/- 4 points -/
theorem Problem3c {p q r : Prop}(h: p ∧ ¬q → r) (h_not_r: ¬r) (h_p: p) : q := by
  sorry

-- Example 1.3.1
/- 4 points -/
theorem Problem131 {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  sorry


-- Example 1.3.2
/- 4 points -/
theorem Problem132 {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  sorry

-- Example 1.3.3
/- 4 points -/
theorem Problem133 {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  sorry