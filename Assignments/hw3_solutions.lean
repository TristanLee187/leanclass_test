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
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'

-- ^ Given ^
-- Exercise solution starts here

  · have hxt' : 0 < (-x) * t := by addarith [hxt] 
    have hxt'' : 0 < x * (-t) := 
    calc 
      0 < (-x) * t := by rel [hxt'] 
      _ = x * (-t) := by ring 
    have hx' : x ≥ 0 := by rel [hx] 
    cancel x at hxt'' 
    have ht : t < 0 := by addarith[hxt''] 
    apply ne_of_lt 
    apply ht 

-- Example 2.5.6
/- 3 points -/
theorem p256 (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring 

-- Example 2.5.7
/- 4 points -/
theorem p257 {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/2 
  have dubp : p + p < p + q := by addarith [h] 
  have dubp' : p + q > 2 * p := 
  calc 
    p + q > p + p := by rel [dubp] 
    _ = 2 * p := by ring 
  have avg_gt_p : (p + q)/2 > p := by addarith [dubp'] 
  have dubq : p + q < q + q := by addarith [h] 
  have dubq' : p + q < 2 * q := 
  calc 
    p + q < q + q := by rel [dubq] 
    _ = 2 * q := by ring 
  have avg_lt_q : (p + q)/2 < q := by addarith [dubq'] 
  constructor 
  · apply avg_gt_p 
  · apply avg_lt_q 

-- Exercise 2.5.9.5
/- 3 points -/
theorem p2595 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt x 1 
  obtain (H1 | H2) := H 
  · use 2 
    have conclusion : x < 4 := 
    calc 
      x ≤ 1 := by rel [H1] 
      _ < 4 := by numbers 
    ring 
    apply conclusion 
  · use x 
    calc 
      x ^ 2 = x * x := by ring 
      _ > 1 * x := by rel [H2] 
      _ = x := by ring 

-- Exercise 2.5.9.6

-- proof assuming t=1 and reaching a contradiction
/- 3 points -/
theorem p2596 {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a,h_at⟩ := h 
  have h_at' : (a - 1) * t < a - 1 := 
  calc 
    (a - 1) * t = a * t + 1 - 1 - t := by ring 
    _ < a + t - 1 - t := by rel [h_at] 
    _ = a - 1 := by ring 
  intros t_ne_1 
  rw [t_ne_1] at h_at' 
  simp at h_at' 

-- alternate proof without contradiction

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a,h_at⟩ := h 
  have h_at' : (1 - a) * (t - 1) > 0 := 
  calc 
    (1 - a) * (t - 1) = t + a - (a * t + 1) := by ring 
    _ > t + a - (a + t) := by rel [h_at] 
    _ = 0 := by ring 
  have H := le_or_gt a 1
  obtain ha1 | ha2 := H 
  · have ha1' : (1 - a) ≥ 0 := by addarith [ha1]
    cancel (1 - a) at h_at' 
    apply ne_of_gt 
    addarith [h_at'] 
  · have ha2' : a - 1 > 0 := by addarith [ha2] 
    apply ne_of_lt 
    have h_at'' : (a - 1) * (1 - t) > 0 := 
    calc 
     (a - 1) * (1 - t) = (1 - a) * (t - 1) := by ring 
      _ > 0 := by rel [h_at'] 
    cancel (a -1) at h_at'' 
    addarith [h_at''] 

-- Exercise 2.5.9.7
/- 4 points -/
theorem p2597 {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, h_am⟩ := h 
  have H := le_or_gt a 2
  obtain ha1 | ha2 := H 
  · apply ne_of_lt 
    calc 
      m = 2 * a := by rw [h_am] 
      _ ≤ 2 * 2 := by rel [ha1] 
      _ < 5 := by numbers 
  · apply ne_of_gt 
    have ha3 : a ≥ 3 := by addarith [ha2] 
    calc 
      m = 2 * a := by rw [h_am] 
      _ ≥ 2 * 3 := by rel [ha3] 
      _ > 5 := by numbers 
