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

/- Example 3.1.4 -/ 

example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn 
  use 7 * k + 1 
  rw [hk] 
  ring 

/- Example 3.1.6 -/

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at * 
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + 3 * b + 1 
  rw [ha,hb] 
  ring 

/- Example 3.1.8 -/

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even] at hn 
  dsimp [Odd] 
  obtain ⟨k, hk⟩ := hn 
  use 2 * k ^ 2 + 2 * k - 3 
  rw [hk] 
  ring 

/- 3.1 Exercise 14 Attempt 1 -/

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a 
  · obtain hb | hb := Int.even_or_odd b 
    · obtain hc | hc := Int.even_or_odd c 
      · dsimp [Even] at * 
        obtain ⟨x, hx⟩ := ha 
        obtain ⟨y, hy⟩ := hb 
        left 
        use x - y 
        rw [hx,hy] 
        ring 
      · dsimp [Even] at * 
        dsimp [Odd] at * 
        obtain ⟨x, hx⟩ := ha 
        obtain ⟨y, hy⟩ := hb 
        left 
        use x - y 
        rw [hx,hy] 
        ring 
    · obtain hc | hc := Int.even_or_odd c 
      · dsimp [Even] at *
        dsimp [Odd] at *
        obtain ⟨x, hx⟩ := ha 
        obtain ⟨y, hy⟩ := hc 
        right 
        left 
        use x + y 
        rw [hx,hy] 
        ring 
      · dsimp [Even] at * 
        dsimp [Odd] at * 
        obtain ⟨x, hx⟩ := hb 
        obtain ⟨y, hy⟩ := hc 
        right 
        right 
        use x - y 
        rw [hx,hy] 
        ring 
  · obtain hb | hb := Int.even_or_odd b 
    · obtain hc | hc := Int.even_or_odd c 
      · dsimp [Even] at * 
        obtain ⟨x, hx⟩ := hb 
        obtain ⟨y, hy⟩ := hc 
        right 
        right 
        use x - y 
        rw [hx,hy] 
        ring 
      · dsimp [Odd] at * 
        dsimp [Even] at * 
        obtain ⟨x, hx⟩ := ha 
        obtain ⟨y, hy⟩ := hc 
        right 
        left 
        use x + y + 1
        rw [hx,hy] 
        ring 
    · obtain hc | hc := Int.even_or_odd c 
      · dsimp [Even] at * 
        dsimp [Odd] at * 
        obtain ⟨x, hx⟩ := ha 
        obtain ⟨y, hy⟩ := hb 
        left 
        use x - y 
        rw [hx,hy] 
        ring 
      · dsimp [Even] at * 
        dsimp [Odd] at * 
        obtain ⟨x, hx⟩ := ha 
        obtain ⟨y, hy⟩ := hb 
        left 
        use x - y 
        rw [hx,hy] 
        ring 

/- 3.1 Exercise 14 Attempt 2 -/

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain H1 | H1 := Int.even_or_odd (a - b) 
  · left 
    dsimp [Even,Int.Even] at * 
    have ⟨k,hk⟩ := H1 
    use k 
    calc 
      a - b = 2 * k := by rw [hk] 
      _ = k + k := by ring 
  · right 
    obtain H2 | H2 := Int.even_or_odd (a + c) 
    · left 
      dsimp [Even,Int.Even] at * 
      have ⟨k,hk⟩ := H2 
      use k 
      calc 
        a + c = 2 * k := by rw [hk] 
        _ = k + k := by ring
    · right 
      dsimp [Even,Int.Odd] at * 
      obtain ⟨k1,hk1⟩ := H1 
      obtain ⟨k2,hk2⟩ := H2 
      use -k1 + k2 - c 
      calc 
        b - c = -(a - b) + (a + c) - 2 * c := by ring 
        _ = -(2 * k1 + 1) + (2 * k2 + 1) - 2 * c := by rw [hk1,hk2] 
        _ = -k1 + k2 - c + (-k1 + k2 - c) := by ring 

/- Example 4.1.3 -/

example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have H : (a + b)/2 ≥ a ∨ (a + b)/2 ≤ b := by apply h 
  obtain h1 | h2 := H 
  · calc 
      a = 2 * a - a := by ring
      _ ≤ 2 * ((a + b) / 2) - a := by rel [h1] 
      _ = a + b - a := by ring 
      _ = b := by ring 
  · calc 
      b = 2 * b - b := by ring 
      _ ≥ 2 * ((a + b) / 2) - b := by rel [h2] 
      _ = a + b - b := by ring 
      _ = a := by ring 

/- Example 4.1.3 Alternate usage of universally quantified hyp -/

example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have H : (a + b)/2 ≥ a ∨ (a + b)/2 ≤ b := h ((a+b)/2) 
  obtain h1 | h2 := H 
  · calc 
      a = 2 * a - a := by ring
      _ ≤ 2 * ((a + b) / 2) - a := by rel [h1] 
      _ = a + b - a := by ring 
      _ = b := by ring 
  · calc 
      b = 2 * b - b := by ring 
      _ ≥ 2 * ((a + b) / 2) - b := by rel [h2] 
      _ = a + b - b := by ring 
      _ = a := by ring 

/- Example 4.1.6 -/

/- Use:  lemma abs_le_of_sq_le_sq' (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y := -/

example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3 
  intros x y h 
  have h1 : (x + y) ^ 2 ≤ 3 ^ 2 := 
  calc 
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra 
    _ = 2 * (x ^ 2 + y ^ 2) := by ring 
    _ ≤ 2 * 4 := by rel [h] 
    _ ≤ 3 ^ 2 := by numbers 
  have h2 : -3 ≤ (x + y) ∧ (x + y) ≤ 3 := by 
    apply abs_le_of_sq_le_sq' h1 
    numbers 
  obtain ⟨h2,h3⟩ := h2 
  apply h2 

/- 4.1 Exercise 2 -/

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have H3 : 1 ≤ 3 → 3 ≤ 5 → 3 ∣ n := hn 3 
  simp at H3
  have H5 : 1 ≤ 5 → 5 ≤ 5 → 5 ∣ n := hn 5 
  simp at H5 
  obtain ⟨a, ha⟩ := H3 
  obtain ⟨b, hb⟩ := H5 
  use 2 * b - a 
  calc 
    n = 6 * n - 5 * n := by ring 
    _ = 6 * n - 5 * (3 * a) := by rw [ha] 
    _ = 6 * (5 * b) - 5 * ( 3 * a) := by rw [hb] 
    _ = 15 * (2 * b - a) := by ring 

/- 4.1 Exercise 4 -/

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  use 7 
  intros x hx 
  calc 
    x ^ 3 + 3 * x = x * x ^ 2 + 3 * x := by ring 
    _ ≥ 7 * x ^ 2 + 3 * 7 := by rel [hx] 
    _ = 7 * x ^ 2 + 12 + 9 := by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra 

/- Example 4.2.5 -/

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor 
  · intros h 
    have h1 : x ^ 2 + x - 6 = (x + 3) * (x - 2) := by ring 
    rw [h1] at h 
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
    obtain h2 | h2 := h2 
    · left 
      addarith [h2] 
    · right 
      addarith [h2] 
  · intros h 
    obtain h | h := h 
    · rw [h] 
      addarith 
    · rw [h] 
      addarith 

/- Example 4.2.6 -/

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor 
  · intros h 
    have h1 : (2 * a - 5) ^ 2 ≤ 1 ^ 2 := 
    calc 
      (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring 
      _ ≤ 4 * (-1) + 5 := by rel [h] 
      _ = 1 ^ 2 := by numbers 
    have h2 : 0 ≤ 1 → -1 ≤ 2 * a - 5 ∧ 2 * a - 5 ≤ 1 := abs_le_of_sq_le_sq' h1 
    simp at h2 
    obtain ⟨h2,h3⟩ := h2 
    have h4 : 2 * 2 ≤ 2 * a := 
    calc 
      2 * a = 2 * a + 1 - 1 := by ring 
      _ ≥ 5 - 1 := by rel [h2] 
      _ = 2 * 2 := by ring 
    cancel 2 at h4 
    have h5 : 2 * a ≤ 2 * 3 := 
    calc 
      2 * a ≤ 1 + 5 := by rel [h3] 
      _ = 2 * 3 := by ring 
    cancel 2 at h5 
    have H := le_or_gt a 2 
    obtain H | H := H 
    · left 
      apply le_antisymm H h4 
    · right 
      addarith [h5,H] 
  · intros h 
    obtain h | h := h 
    · rw [h] 
      simp 
    · rw [h] 
      simp 
