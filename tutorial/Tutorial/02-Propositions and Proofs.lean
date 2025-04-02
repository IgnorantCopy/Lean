/- Propositions as Types -/
def Imp (p q : Prop) : Prop := p → q
#check And    -- Prop → Prop → Prop
#check Or     -- Prop → Prop → Prop
#check Not    -- Prop → Prop
#check Imp    -- Prop → Prop → Prop

variable (p q r s : Prop)
#check And p q                  -- Prop
#check Or (And p q) r           -- Prop
#check Imp (And p q) (And q p)  -- Prop

structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

axiom comm (p q : Prop) : Proof (Imp (And p q) (And q p))
#check comm p q     -- Proof (Implies (And p q) (And q p))

-- from a proof of Imp p q and a proof of p, we obtain a proof of q
axiom modus_pones : (p q : Prop) → Proof (Imp p q) → Proof p → Proof q
-- assuming that we have a hypothesis p and a proof of q, then we can cancel the hypothesis and obtain a proof of Imp p q
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Imp p q)

/- Examples -/
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p :=
  fun hp : p =>
    fun _ : q =>
      show p from hp
#print t1

theorem t2 (hp : p) (_ : q) : p := hp
#print t2

-- use theorem t2 as a function application
axiom hp : p
theorem t3 : q → p := t2 hp
#print t3

theorem t4 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
    show r from h₁ (h₂ h₃)

/- Propositional Logic -/
-- True False ¬ ∧ ∨ → ↔
/- conjuction -/
#check fun (hp : p) (hq : q) => And.intro hp hq
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

variable (hp :p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩
example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩
/- disjunction -/
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

/- Negation and Falsity -/
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
    show False from hnq (hpq hp)
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
-- ¬p → q → (q → p) → r
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

/- Logical Equivalence -/
theorem and_swap1 : (p ∧ q) ↔ (q ∧ p) :=
  Iff.intro
    (fun h : p ∧ q =>
      show q ∧ p from And.intro h.right h.left)
    (fun h : q ∧ p =>
      show p ∧ q from And.intro h.right h.left)

theorem and_swap2 : (p ∧ q) ↔ (q ∧ p) :=
  ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

example (h : p ∧ q) : q ∧ p := and_swap2.mp h

/- Introducing Auxiliary Subgoals -/
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from ⟨hq, hp⟩
  show q from hq

/- Classical Logic -/
open Classical
#check em p  -- p ∨ ¬p

theorem dne (p : Prop) (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

theorem dne2 (p : Prop) : ¬¬p → p :=
  fun h : ¬¬p =>
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p :=
  byCases
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr (show ¬q from
        fun hq : q => h ⟨hp, hq⟩))
    (fun hnp : ¬p =>
      Or.inl hnp)
