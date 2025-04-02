inductive S : Nat × Nat → Type
  | zero : S (0, 0)
  | step1 x y : S (x, y) → S (x, y + 1)
  | step2 x y : S (x, y) → S (x + 2, y + 1)

open S

theorem proof : ∀ (x : Nat) (y : Nat) , S (x, y) → x ≤ 2 * y := by
  intro x y hp
  cases hp with
  | zero =>
    rw [Nat.mul_zero]
    exact Nat.zero_le 0
  | step1 x y hp =>
    simp [Nat.mul_add]
    have h1 : x ≤ 2 * y := proof x y hp
    have h2 : x ≤ 2 * y + 2 := Nat.le_add_right_of_le h1
    exact h2
  | step2 x y hp =>
    simp [Nat.mul_add]
    have h1 : x ≤ 2 * y := proof x y hp
    exact h1
