/- Universal Quantifier -/
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
    fun y : α =>
        show p y from (h y).left

variable (α β : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)
variable (a b c d : α)
variable (rab : r a b) (rbc : r b c)
#check trans_r a b c
#check trans_r a b c rab
#check trans_r a b c rab rbc

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)
example (rab : r a b) (rcb : r c b) (rcd : r c d) : r a d :=
  trans_r (trans_r rab (symm_r rcb)) rcd

/- Equality -/
#check Eq.refl
#check Eq.symm
#check Eq.trans
universe u
#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

-- rfl : Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := rfl
-- substitution : a = b → f a = f b
example (p : α → Prop) (h₁ : a = b) (h₂ : p a) : p b := Eq.subst h₁ h₂
example (p : α → Prop) (h₁ : a = b) (h₂ : p a) : p b := h₁ ▸ h₂

variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)
example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
-- common identities
variable (a b c d e : Nat)
example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h₁ : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h₂ : (x + y) * (x + y) = (x * x + y * x) + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h₁
  h₂.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

/- Calculational Proofs -/
theorem T₁ (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc
    a = b     := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg Nat.succ h3
    _ = 1 + d := Nat.add_comm d 1
    _ = e     := Eq.symm h4
-- use rewrite and simp tactics
theorem T₂ (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc
    a = b     := by rw [h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h4]

theorem T₃ (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc
    a = d + 1 := by rw [h1, h2, h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h4]

theorem T₄ (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
-- the difference is that simp apply the identities repeatedly
theorem T₅ (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
-- if the first expression takes much space, we can use _ in the first relation
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
    _ = x * x + y * x + (x * y + y * y) := by simp [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y := by rw [←Nat.add_assoc]
-- powerful simp
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

/- Existential Quantifier -/
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_one
  Exists.intro 1 h
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_one
  ⟨1, h⟩
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
      fun hw : p w ∧ q w =>
        show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
-- more convenient way to eliminate from an existential quantifier: match expression
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

open Classical

example (h : ¬ ∀ x , ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
          fun h3 : p x =>
            have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x ) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, Or.inl hpa⟩)
        (fun ⟨a, hqa⟩ => ⟨a, Or.inr hqa⟩))

variable (r : Prop) (a : α)
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
      fun h2 : ∀ x, p x =>
        show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
      show ∃ x, p x → r from
        byCases
          (fun hap : ∀ x, p x => ⟨a, fun _ => h1 hap⟩)
          (fun hnap : ¬ ∀ x, p x =>
            byContradiction
              (fun hnex : ¬ ∃ x, p x → r =>
                have hap : ∀ x, p x :=
                  fun x =>
                    byContradiction
                      (fun hnp : ¬ p x =>
                        have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                        show False from hnex hex)
                show False from hnap hap)))

-- keyword this: to refer to the last expression
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

-- by assumption: use when the goal can be inferred
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

-- ‹p› : show p by assumption
example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
    fun _ : f 1 ≥ f 2 =>
      have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
      have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
