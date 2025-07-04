-- TinyFOL: Syntax plus semantics for a mini first-order language
import Mathlib.Data.Nat.Basic

namespace TinyFOL

/- Syntax: Terms of the language:
     - de Bruijn variables (an index of variables, last bound first)
     - constant zero
     - function successor
-/
inductive Term : Type
| var  : Nat → Term
| zero : Term
| succ : Term → Term

/- Syntax: Well-formed formulae
    - predicate `<`
    - implication
    - negation
    - ∀.
-/
inductive Formula : Type
| lt      : Term → Term → Formula
| imp     : Formula → Formula → Formula
| not     : Formula → Formula
| forallF : Formula → Formula

open Term Formula

/- Notation for the connectives and ∀. -/
infixr:25 " ⇒ "  => imp
prefix:50 "¬ "   => not
notation "∀." ϕ  => forallF ϕ

/- Atomic formula -/
def atm_lt (t₁ t₂ : Term) : Formula := lt t₁ t₂


/- Example of a sentence: φ = ∀x ∀y, x < y ⇒ succ x < succ y. -/
@[simp] def φ : Formula :=
  ∀. (∀. (
    atm_lt (var 1) (var 0) ⇒
    atm_lt (succ (var 1)) (succ (var 0))
  ))

/- Structure: signature symbols to be interpreted
     - domain of discourse U
     - constant zero
     - function succ
     - predicate lt
-/
structure Str where
  U    : Type
  zero : U
  succ : U → U
  lt   : U → U → Prop

/- Valuation function: interpreting variables -/
abbrev Val (𝔄 : Str) := Nat →  𝔄.U

/- Term interpretation -/
@[simp] def Term.eval {𝔄 : Str} : Term → Val 𝔄 → 𝔄.U
| var n, ρ   => ρ n
| zero, _    => 𝔄.zero
| succ t, ρ  => 𝔄.succ (t.eval ρ)

/- WFF interpretation -/
/- The last line:
   1. When we enter a ∀, we pick an x : 𝔄.U.
   2. We must bind var 0 to this x.
   3. Existing variables (from earlier) shift up by 1 (because a new binding is inserted at the front).
-/
@[simp] def Formula.holds {𝔄 : Str} : Formula → Val 𝔄 → Prop
| lt t₁ t₂,  ρ   => 𝔄.lt (t₁.eval ρ) (t₂.eval ρ)
| imp ϕ ψ,   ρ   => ϕ.holds ρ → ψ.holds ρ
| not ϕ,     ρ   => ¬ ϕ.holds ρ
| forallF ϕ, ρ   => ∀ x : 𝔄.U, ϕ.holds (fun n => if n = 0 then x else ρ (n-1))

/- The standard ℕ Structure. -/
def ℕStr : Str :=
{ U    := ℕ,
  zero := 0,
  succ := Nat.succ,
  lt   := (· < ·) }

/- Satisfiable in ℕStr under valuation ρ (default all-zero). -/
abbrev holdsInℕ (ϕ : Formula) (ρ : Val ℕStr := fun _ => ℕStr.zero) : Prop :=
  ϕ.holds (𝔄 := ℕStr) ρ

/- φ is valid in ℕStr. -/
example : holdsInℕ φ := by
  -- unfold both φ and holdsInℕ so we get two ∀-bindings
  simp [holdsInℕ, φ]
  intro x y hxy
  apply Nat.succ_lt_succ
  exact hxy

/- ψ ≔ 0 < x (open formula). -/
@[simp] def ψ : Formula := atm_lt zero (var 0)

/- ψ is false under valuation x ↦ 0. -/
example : ¬ holdsInℕ ψ (fun _ => ℕStr.zero) := by
  simp [holdsInℕ, ψ]
  exact Nat.not_lt_zero 0

/- ψ is true under valuation x ↦ succ(zero). -/
example : holdsInℕ ψ (fun _ => ℕStr.succ ℕStr.zero) := by
  simp [holdsInℕ, ψ]
  exact Nat.zero_lt_succ 0

/- Example wff with a quantifier: ∀x x < succ(x) -/
@[simp] def ϕ : Formula :=
  ∀. (atm_lt (var 0) (succ (var 0)))

example : holdsInℕ ϕ (fun _ => ℕStr.zero) := by
  simp [holdsInℕ, ϕ]
  intro x
  exact Nat.lt_succ_self x

end TinyFOL
