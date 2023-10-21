import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

/- 5 points -/

theorem problem4a {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor 
  · intros h 
    dsimp [(.∣.)] at * 
    obtain ⟨c,hc⟩ := h 
    constructor 
    · use 9 * c 
      calc 
        n = 63 * c := by rw [hc] 
        _ = 7 * (9 * c) := by ring 
    · use 7 * c 
      calc 
        n = 63 * c := by rw [hc] 
        _ = 9 * (7 * c) := by ring 
  · intros h 
    dsimp [(.∣.)] at * 
    obtain ⟨h1,h2⟩ := h 
    obtain ⟨a,ha⟩ := h1 
    obtain ⟨b,hb⟩ := h2 
    use 4 * b - 3 * a 
    calc 
      n = 28 * n - 27 * n := by ring 
      _ = 4 * 7 * n + (-3) * 9 * n := by ring 
      _ = 4 * 7 * (n) + (-3) * 9 * (7 * a) := by rw [ha] 
      _ = 4 * 7 * (9 * b) + (-3) * 9 * (7 * a) := by rw [hb] 
      _ = 63 * (4 * b - 3 * a) := by ring 

/- 5 points -/

theorem problem4b {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor 
  · intros h 
    have H1 := le_or_gt k 0
    obtain H1 | H1 := H1 
    · left 
      simp at H1 
      apply H1 
    · right 
      have H2 := le_or_gt k 1 
      obtain H2 | H2 := H2 
      · left 
        have H3 : k ≥ 1 := by addarith [H1] 
        apply le_antisymm H2 H3 
      · right 
        have H3 : k ≥ 2 := by addarith [H2] 
        have H4 : ¬(k ≥ 3) := by 
          intros H5 
          have H6 : 3 * 2 ≥ 3 * k := 
          calc 
            3 * 2 = 6 := by ring 
            _ ≥ k ^ 2 := by rel [h] 
            _ = k * k := by ring 
            _ ≥ 3 * k := by rel [H5] 
          cancel 3 at H6 
          have H7 : k = 2 := le_antisymm H6 H3 
          addarith [H5,H7] 
        simp at H4 
        addarith [H3,H4] 
  · intros h 
    obtain h1 | h2 | h3 := h 
    · rw [h1] 
      numbers 
    · rw [h2] 
      numbers 
    · rw [h3] 
      numbers 

/- 3 points -/

theorem problem5a : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2 
  dsimp 
  constructor 
  · intros a ha1 ha3 
    simp 
    dsimp [abs] 
    simp 
    constructor 
    · calc 
        a ≤ 3 := ha3  
        _ = 1 + 2 := by numbers 
    · calc 
        1 + a ≥ 1 + 1 := by rel [ha1] 
        _ = 2 := by numbers 
  · intros y h
    have h1 : 1 ≥ 1 → 1 ≤ 3 → (1 - y) ^ 2 ≤ 1 := h 1 
    have h1' : (1 - y) ^ 2 ≤ 1 := by 
      apply h1 
      simp 
      simp 
    have h3 : 3 ≥ 1 → 3 ≤ 3 → (3 - y) ^ 2 ≤ 1 := h 3 
    have h3' : (3 - y) ^ 2 ≤ 1 := by 
      apply h3 
      simp 
      simp 
    have hAbove : (y - 2) ^ 2 ≤ 0 := 
    calc 
      (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring 
      _ ≤ (1 + 1 - 2) / 2 := by rel [h1',h3'] 
      _ = 0 := by numbers 
    have hBelow : 0 ≤ (y - 2) ^ 2 := by extra 
    have hy : (y - 2) ^ 2 = 0 := by apply le_antisymm hAbove hBelow 
    simp at hy
    calc 
      y = y - 2 + 2 := by ring 
      _ = 0 + 2 := by rw [hy] 
      _ = 2 := by numbers 

/- 3 points -/

theorem problem5b : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3 
  dsimp 
  constructor 
  · numbers 
  · intros y h 
    have h' : 4 * y = 4 * 3 := 
    calc 
      4 * y = 4 * y - 3 + 3 := by ring 
      _ = 9 + 3 := by rw [h] 
      _ = 4 * 3 := by numbers 
    cancel 4 at h' 

/- 4 points -/

theorem problem5c : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0 
  dsimp 
  constructor 
  · intros a 
    simp 
  · intros y h 
    have h0 : y ≤ 0 := h 0 
    simp at h0 
    apply h0 

/- 2.5 points -/

theorem problem6a {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    right 
    have hmp_le : m ≤ p := Nat.le_of_dvd hp' hmp 
    obtain m_eq_p | m_lt_p := eq_or_lt_of_le hmp_le 
    · apply m_eq_p 
    · have contra : ¬m ∣ p := H m hm_left m_lt_p 
      contradiction

/- 2.5 points -/

theorem problem6b {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain hneg | hpos : a ≤ 2 ∨ 2 < a := le_or_lt a 2 
  · obtain b_le_1 | b_gt_1 := le_or_lt b 1 
    · have h : c ^ 2 < 3 ^ 2 := 
      calc 
        c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth] 
        _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [hneg,b_le_1] 
        _ < 3 ^ 2 := by numbers 
      cancel 2 at h 
      interval_cases a 
      interval_cases b 
      interval_cases c <;> contradiction 
      interval_cases b 
      interval_cases c <;> contradiction 
    · have b_ge_2 : b ≥ 2 := b_gt_1 
      have fact : b ^ 2 < c ^ 2 := 
      calc 
        b ^ 2 < a ^ 2 + b ^ 2 := by extra 
        _ = c ^ 2 := by rw [h_pyth] 
      cancel 2 at fact 
      have factplus1 : b + 1 ≤ c := fact 
      have := 
      calc 
        c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth] 
        _ ≤ 2 ^ 2 + b ^ 2 := by rel [hneg] 
        _ = b ^ 2 + 2 * 2 := by ring 
        _ ≤ b ^ 2 + 2 * b := by rel [b_ge_2] 
        _ < b ^ 2 + 2 * b + 1 := by extra 
        _ = (b + 1) ^ 2 := by ring 
      cancel 2 at this 
      have that : ¬(c < b + 1) := by 
        push_neg 
        apply factplus1 
      contradiction 
  apply hpos 

/- 2.5 points -/

theorem problem6c {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  obtain h1 | h2 := le_or_lt y x
  · apply h1
  · have : ¬y ^ n ≤ x ^ n
    · apply not_le_of_lt
      rel [h2]
    contradiction

namespace Nat

/- 2.5 points -/

theorem problem6d (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at h 
  obtain ⟨h1,h2⟩ := h
  have h3 := h2 2 
  by_cases 2 ∣ p
  · left 
    have := h3 h 
    simp at this 
    symm; apply this 
  · right 
    rw [Nat.odd_iff_not_even p] 
    dsimp [Even] 
    dsimp [(.∣.)] at h 
    apply h 
