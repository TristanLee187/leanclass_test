import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/- 2 points -/
theorem problem4a {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · ring
    dsimp [Int.ModEq,(.∣.)] at *
    use 0
    simp
  · dsimp [Int.ModEq,(.∣.)] at *
    obtain ⟨x,hx⟩ := IH
    obtain ⟨y,hy⟩ := h
    use (a * x + b ^ k * y)
    calc
        a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
        _ = a * (d * x) + b ^ k * (d * y) := by rw [hx,hy]
        _ = d * (a * x + b ^ k * y) := by ring

/- 3 points -/
theorem problem4b : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    simp
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra

/- 2 points -/
theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  have ha' : 0 ≤ 1 + a :=
  calc
    0 = 1 + (-1) := by ring
    _ ≤ 1 + a := by rel [ha]
  simple_induction n with n IH
  · simp
  · calc
      (1 + a) ^ (n + 1) = (1 + a) * (1 + a) ^ n := by ring
      _ ≥ (1 + a) * (1 + n * a) := by rel [IH]
      _ = 1 + (n + 1) * a + n * a ^ 2 := by ring
      _ ≥ 1 + (n + 1) * a := by extra

/- 3 points -/
theorem problem4d : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intros x hx
  induction_from_starting_point x, hx with n hn IH
  · simp
  · calc
      (3 : ℤ) ^ (n + 1) = 3 * 3 ^ n := by ring
      _ ≥ 3 * (2 ^ n + 100) := by rel [IH]
      _ = 2 * (2 ^ n + 100) + (2 ^ n + 100) := by ring
      _ ≥ 2 * (2 ^ n + 100) := by extra
      _ = 2 ^ (n + 1) + 100 + 100 := by ring
      _ ≥ 2 ^ (n + 1) + 100 := by extra

/- This tail-recursive function is equivalent to the sum. -/

def foo : ℕ → ℕ
  | 0  => 1
  | n + 1 => foo (n) + 2 * n + 3

/- 5 points -/
theorem problem5b : ∀ (n : ℕ), ∃ (k : ℕ), foo (n) = k ^ 2 := by
  intros n
  use n + 1
  have lemZ : foo (n) = (n + 1) ^ 2 := by
    simple_induction n with k IH
    · -- base case
      rw [foo]
      numbers
    · -- inductive step
      calc foo (k + 1) = foo (k) + 2 * k + 3 := by rw [foo]
             _         = (k + 1)^2 + 2 * k + 3 := by rw [IH]
             _         = (k + 2)^2 := by ring
  apply lemZ
