import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.Basic

/-- Syntax of well‐formed formulas (WFF) in propositional logic. -/
inductive WFF : Type where
  | p_atm : String → WFF
  | p_not : WFF → WFF
  | p_and : WFF → WFF → WFF
  | p_or  : WFF → WFF → WFF
  | p_imp : WFF → WFF → WFF
  | p_iff : WFF → WFF → WFF

open WFF

def WFF_to_String : WFF → String
  -- Base case
  | p_atm s   => s
  -- Induction steps
  | p_not φ   => "(¬" ++ WFF_to_String φ ++  ")"
  | p_and φ ψ => "(" ++ WFF_to_String φ ++ " ∧ " ++ WFF_to_String ψ ++ ")"
  | p_or  φ ψ => "(" ++ WFF_to_String φ ++ " ∨ " ++ WFF_to_String ψ ++ ")"
  | p_imp φ ψ => "(" ++ WFF_to_String φ ++ " → " ++ WFF_to_String ψ ++ ")"
  | p_iff φ ψ => "(" ++ WFF_to_String φ ++ " ↔ " ++ WFF_to_String ψ ++ ")"

/-- Utility function for fancy outputs --/
instance : ToString WFF where
  toString := WFF_to_String

/-- Some atomic formulas for testing. -/
def A₁ : WFF := p_atm "A₁"
def A₂ : WFF := p_atm "A₂"
def A₃ : WFF := p_atm "A₃"
def A₄ : WFF := p_atm "A₄"
def A₅ : WFF := p_atm "A₅"
def A₆ : WFF := p_atm "A₆"
def A₇ : WFF := p_atm "A₇"
def A₈ : WFF := p_atm "A₈"
def A₉ : WFF := p_atm "A₉"
def A₁₀ : WFF := p_atm "A₁₀"

/-- A sample complex formula for testing:
    (A₁ ∧ (¬A₂)) → A₃  -/
def complex_WFF : WFF :=
  p_imp (p_and A₁ (p_not A₂)) A₃

/-- The valuation function for formulas.
    It takes an atomic valuation (a function from String to Bool)
    and recursively computes the truth value of a formula. -/
def v (v_atom : String → Bool) : WFF → Bool
  | p_atm s   => v_atom s
  | p_not φ   => not (v v_atom φ)
  | p_and φ ψ => and (v v_atom φ) (v v_atom ψ)
  | p_or  φ ψ => or (v v_atom φ) (v v_atom ψ)
  | p_imp φ ψ => or (not (v v_atom φ)) (v v_atom ψ)
  | p_iff φ ψ => (v v_atom φ) = (v v_atom ψ)

/-- We define a set of “true” atoms using a Finset (because membership in a Finset is decidable). -/
def true_atoms : Finset String := {"A₁"}

/-- The atomic valuation function: an atom is true if it is in the given Finset. -/
def v_atom (S : Finset String) (s : String) : Bool :=
  if s ∈ S then true else false

-- Test evaluation: note that #eval shows the formula and its computed truth value.
#eval complex_WFF
#eval v (v_atom true_atoms) complex_WFF

/-
--------------------------------------------------------------------------------
Example 1. Uniqueness of Evaluation Under Atomic Agreement
--------------------------------------------------------------------------------

Show that if two atomic valuations agree on every atom, then they yield the same
formula valuation.
-/
theorem valuation_uniqueness {v₁ v₂ : String → Bool}
  (h : ∀ s : String, v₁ s = v₂ s) : ∀ φ : WFF, v v₁ φ = v v₂ φ :=
by
  intro φ
  induction φ
  case p_atm s           => simp [v, h s]
  case p_not φ IH        => simp [v, IH]
  case p_and φ ψ IH₁ IH₂ => simp [v, IH₁, IH₂]
  case p_or  φ ψ IH₁ IH₂ => simp [v, IH₁, IH₂]
  case p_imp φ ψ IH₁ IH₂ => simp [v, IH₁, IH₂]
  case p_iff φ ψ IH₁ IH₂ => simp [v, IH₁, IH₂]

/-
--------------------------------------------------------------------------------
Example 2. Commutativity of Conjunction
--------------------------------------------------------------------------------
Prove that for any atomic valuation v_atom and formulas φ and ψ, we have:
  v v_atom (p_and φ ψ) = v v_atom (p_and ψ φ)
-/

theorem valuation_and_comm (v_atom : String → Bool) (φ ψ : WFF) :
  v v_atom (p_and φ ψ) = v v_atom (p_and ψ φ) :=
by
    simp [v, Bool.and_comm]

/-
--------------------------------------------------------------------------------
Example 3. Reflexivity of Implication
--------------------------------------------------------------------------------
Prove that for any atomic valuation v_atom and formula φ, the formula
  p_imp φ φ   (i.e. φ → φ)
evaluates to true.
-/
theorem imp_rfl (v_atom : String → Bool) (φ : WFF) :
  v v_atom (p_imp φ φ) = true :=
by
  unfold v
  let a := v v_atom φ; simp

/-
--------------------------------------------------------------------------------
Example 4. De Morgan’s Law for Conjunction
--------------------------------------------------------------------------------
Prove that for any atomic valuation v_atom and formulas φ and ψ, the following holds:
  v v_atom (p_not (p_and φ ψ)) = v v_atom (p_or (p_not φ) (p_not ψ))
This corresponds to one of De Morgan’s laws.
-/
theorem de_morgan (v_atom : String → Bool) (φ ψ : WFF) :
  v v_atom (p_not (p_and φ ψ)) = v v_atom (p_or (p_not φ) (p_not ψ)) :=
by
  unfold v
  apply Bool.not_and

#print Bool.not_and