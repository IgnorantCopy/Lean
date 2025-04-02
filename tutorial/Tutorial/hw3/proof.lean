import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic


inductive WFF : Type
  | p_atom : String → WFF
  | p_not : WFF → WFF
  | p_and : WFF → WFF → WFF
  | p_or : WFF → WFF → WFF
  | p_imp : WFF → WFF → WFF
  | p_iff : WFF → WFF → WFF

open WFF

def WFF_toString : WFF → String
  | p_atom s => s
  | p_not φ => "(¬" ++ WFF_toString φ ++ ")"
  | p_and φ ψ => "(" ++ WFF_toString φ ++ " ∧ " ++ WFF_toString ψ ++ ")"
  | p_or φ ψ => "(" ++ WFF_toString φ ++ " ∨ " ++ WFF_toString ψ ++ ")"
  | p_imp φ ψ => "(" ++ WFF_toString φ ++ " → " ++ WFF_toString ψ  ++ ")"
  | p_iff φ ψ => "(" ++ WFF_toString φ ++ " ↔ " ++ WFF_toString ψ ++ ")"

def v_atom (S : Finset String) (s : String) : Bool :=
  if s ∈ S then true else false

def v (v_atom : String → Bool) : WFF → Bool
  | p_atom s => v_atom s
  | p_not φ => not (v v_atom φ)
  | p_and φ ψ => and (v v_atom φ) (v v_atom ψ)
  | p_or φ ψ => or (v v_atom φ) (v v_atom ψ)
  | p_imp φ ψ => or (not (v v_atom φ)) (v v_atom ψ)
  | p_iff φ ψ => (v v_atom φ) = (v v_atom ψ)

/- Prove 1.1 -/
theorem and_distrib (v_atom : String → Bool) (φ ψ χ : WFF) : v v_atom (p_and φ (p_or ψ χ)) = v v_atom (p_or (p_and φ ψ) (p_and φ χ)) := by
  simp [v, Bool.and_or_distrib_left]

/- Prove 1.2 -/
theorem iff_imp (v_atom : String → Bool) (φ ψ : WFF) : v v_atom (p_iff φ ψ) = v v_atom (p_and (p_imp φ ψ) (p_imp ψ φ)) := by
  simp [v]
  induction v v_atom φ with
    | true => simp
    | false => simp

/- Prove 1.3 -/
theorem vacuous_truth (v_atom : String → Bool) (φ ψ : WFF) : (v v_atom φ = false) → (v v_atom (p_imp φ ψ) = true) := by
  simp [v]
  induction v v_atom φ with
    | true => simp
    | false => simp

/- 1.4.1 -/
def atoms : WFF → Finset String
  | p_atom s => {s}
  | p_not φ => atoms φ
  | p_and φ ψ => atoms φ ∪ atoms ψ
  | p_or φ ψ => atoms φ ∪ atoms ψ
  | p_imp φ ψ => atoms φ ∪ atoms ψ
  | p_iff φ ψ => atoms φ ∪ atoms ψ

/- 1.4.2 -/
theorem v_atom_eq (v₁ v₂ : String → Bool) (φ : WFF) : (∀ s ∈ atoms φ, v₁ s = v₂ s) → (v v₁ φ = v v₂ φ) := by
  induction φ with
    | p_atom s => simp [atoms, v]
    | p_not p ih => 
      simp [atoms, v]
      apply ih
    | p_and p q ih1 ih2 => 
      simp [atoms, v]
      simp [or_imp]
      simp [forall_and]
      have h1 : (∀ x ∈ atoms p, v₁ x = v₂ x) → (∀ x ∈ atoms q, v₁ x = v₂ x) → ((v v₁ p = v v₂ p) ∧ (v v₁ q = v v₂ q)) := by exact
        fun x y => ⟨ih1 x, ih2 y⟩
      have h2 : ((v v₁ p = v v₂ p) ∧ (v v₁ q = v v₂ q)) → ((v v₁ p && v v₁ q) = (v v₂ p && v v₂ q)) := by
        intro h
        rw [h.left, h.right]
      exact fun x y => h2 (h1 x y)
    | p_or p q ih1 ih2 =>
      simp [atoms, v]
      simp [or_imp]
      simp [forall_and]
      have h1 : (∀ x ∈ atoms p, v₁ x = v₂ x) → (∀ x ∈ atoms q, v₁ x = v₂ x) → ((v v₁ p = v v₂ p) ∧ (v v₁ q = v v₂ q)) := by exact
        fun x y => ⟨ih1 x, ih2 y⟩
      have h2 : ((v v₁ p = v v₂ p) ∧ (v v₁ q = v v₂ q)) → ((v v₁ p || v v₁ q) = (v v₂ p || v v₂ q)) := by
        intro h
        rw [h.left, h.right]
      exact fun x y => h2 (h1 x y)
    | p_imp p q ih1 ih2 =>
      simp [atoms, v]
      simp [or_imp]
      simp [forall_and]
      have h1 : (∀ x ∈ atoms p, v₁ x = v₂ x) → (∀ x ∈ atoms q, v₁ x = v₂ x) → ((v v₁ p = v v₂ p) ∧ (v v₁ q = v v₂ q)) := by exact
        fun x y => ⟨ih1 x, ih2 y⟩
      have h2 : ((v v₁ p = v v₂ p) ∧ (v v₁ q = v v₂ q)) → ((!v v₁ p || v v₁ q) = (!v v₂ p || v v₂ q)) := by
        intro h
        rw [h.left, h.right]
      exact fun x y => h2 (h1 x y)
    | p_iff p q ih1 ih2 => 
      simp [atoms, v]
      simp [or_imp]
      simp [forall_and]
      have h1 : (∀ x ∈ atoms p, v₁ x = v₂ x) → (∀ x ∈ atoms q, v₁ x = v₂ x) → ((v v₁ p = v v₂ p) ∧ (v v₁ q = v v₂ q)) := by exact
        fun x y => ⟨ih1 x, ih2 y⟩
      have h2 : ((v v₁ p = v v₂ p) ∧ (v v₁ q = v v₂ q)) → ((v v₁ p = v v₁ q) ↔ (v v₂ p = v v₂ q)) := by
        intro h
        rw [h.left, h.right]
      exact fun x y => h2 (h1 x y)
