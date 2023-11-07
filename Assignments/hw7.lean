import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option push_neg.use_distrib true

/- 5 points -/

theorem problem4a : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 < 2 ^ 2 := by numbers
      _ ≤ n ^ 2 := by rel [hn]

/- 5 points -/

theorem problem4b (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intros h1
    by_cases P ∧ ¬Q
    · apply h
    · apply False.elim
      apply h1
      intros p
      rw [not_and_or] at h
      obtain h | h := h
      · contradiction
      · rw [not_not] at h
        apply h
  · intros h1 h2
    obtain ⟨p,nq⟩ := h1
    have q : Q := h2 p
    contradiction

/-
theorem problem4b (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intros h1
    by_cases pnq : P ∧ ¬Q
    · apply pnq
    · constructor
      · rw [not_and_or] at pnq
        rw [not_not] at pnq
        have pimpq : P → Q := by
          intros p
          obtain H | H := pnq
          · contradiction
          · apply H
        contradiction
      · intros q
        apply h1
        intros p
        apply q
  · intros h1 h2
    obtain ⟨p,nq⟩ := h1
    have q : Q := h2 p
    contradiction
-/

/- 5 points -/

theorem problem5a {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  apply And.intro hk (And.intro hk1 hkp)

/- 5 points -/

theorem problem5b {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have contra : Prime p := prime_test hp2 H
    contradiction
  push_neg at H
  apply H

/-
/- Negative Test Case 1:  Exercise 5.3.6.2 -/

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intros h1
    rw [not_imp] at h1
    apply h1
  · intros h1 h2
    rw [← not_imp] at h1
    contradiction

/- Negative Test Case 2:  Exercise 5.3.6.2 -/

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  push_neg
  simp
-/
