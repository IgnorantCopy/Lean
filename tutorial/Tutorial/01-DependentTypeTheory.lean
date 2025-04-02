/- Define some constants. -/
def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/
#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/
#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

/- Type -/
#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

/- Types as objects -/
#check Nat          -- Type
#check Bool         -- Type
#check Nat → Bool   -- Type
#check Nat × Bool   -- Type

def α : Type := Nat
def β : Type := Bool
def f : Type → Type := List
def g : Type → Type → Type := Prod

#check f α      -- Type
#check g α      -- Type → Type
#check g α β    -- Type

/- lambda function -/
#eval (λ x: Nat => x + 5) 10
#eval (fun (x: Nat) (y: Bool) => if not y then x + 1 else x + 2) 5 True
#check fun (α β γ : Type) (g: β → γ) (f : α → β) (x : α) => g (f x)

def f1 (n : Nat) : String := toString n
def g1 (s : String) : Bool := s.length > 0
#check (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g1 f1 0  -- True

/- Local Definitions -/
def twice_double(x : Nat) :=
  let y := x + x
  y * y

#eval twice_double 2

/- Variables and Sections -/
section useful
  variable (α β γ : Type)
  variable (h: α → α) (g : β → γ) (f : α → β) (x : α)

  def compose := g (f x)
  def twice := h (h x)
  def thrice := h (h (h x))

  #print compose
  #print twice
  #print thrice
end useful

/- Namespaces -/
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7
  def fa : Nat := f a
  def faa : Nat := f (f a)
end Foo

#check Foo.a

open Foo
#check f
#check fa
#check Foo.fa

/- Implicit Arguments -/
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α
