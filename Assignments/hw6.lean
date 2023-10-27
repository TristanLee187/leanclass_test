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
theorem problem4a {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor 
  · intros h' 
    obtain ⟨x,hpx⟩ := h' 
    have hx : P x ↔ Q x := h x 
    obtain ⟨hpq,hqp⟩ := hx 
    use x 
    apply hpq hpx 
  · intros h' 
    obtain ⟨x,hqx⟩ := h' 
    have hx : P x ↔ Q x := h x 
    obtain ⟨hpq,hqp⟩ := hx 
    use x 
    apply hqp hqx 

/- 5 points -/
theorem problem4b (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor 
  · intros h 
    obtain ⟨x,y,hxy⟩ := h 
    use y 
    use x 
    apply hxy 
  · intros h 
    obtain ⟨y,x,hyx⟩ := h 
    use x 
    use y 
    apply hyx 

/- 5 points -/
theorem problem4c (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor <;> intros h y x <;> apply h x y 

/- 5 points -/
theorem problem4d (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor 
  · intros h 
    obtain ⟨⟨x,hp⟩,q⟩ := h
    use x 
    apply And.intro hp q 
  · intros h 
    obtain ⟨x,⟨hp,q⟩⟩ := h 
    constructor 
    · use x 
      apply hp 
    · apply q 

def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

/- 10 points -/
theorem problem5a : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases tri1 : Tribalanced 1 
  · use 1 
    constructor 
    · apply tri1 
    · intros h 
      conv at h => numbers 
      dsimp [Tribalanced] at h 
      have contra := h 2 
      conv at contra => numbers 
      apply contra 
  · use 0
    constructor 
    · dsimp [Tribalanced] 
      simp 
      numbers 
    · conv => numbers 
      apply tri1 

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two

/- 10 points -/
theorem problem5b : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1 
  conv => numbers 
  constructor 
  · apply superpowered_one 
  · dsimp [Superpowered] 
    simp 
    use 5 
    apply not_prime 641 6700417 
    · numbers 
    · numbers 
    · numbers 
