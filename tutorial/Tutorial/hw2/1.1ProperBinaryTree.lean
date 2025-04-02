inductive ProperBinaryTree : Type
  | leaf : ProperBinaryTree 
  | node : ProperBinaryTree → ProperBinaryTree → ProperBinaryTree

open ProperBinaryTree


def exampleTree : ProperBinaryTree :=
  node
    (node leaf leaf)
    (node leaf leaf)


def num_of_leaves : ProperBinaryTree → Nat
  | leaf => 1
  | node left right => num_of_leaves left + num_of_leaves right

def num_of_nodes : ProperBinaryTree → Nat
  | leaf => 0
  | node left right => 1 + num_of_nodes left + num_of_nodes right

#eval num_of_leaves exampleTree

#eval num_of_nodes exampleTree

theorem leaves_minus_nodes : ∀ tree : ProperBinaryTree, num_of_leaves tree = 1 + num_of_nodes tree := by
  intro tree
  induction tree
  case leaf => 
    simp [num_of_leaves, num_of_nodes]
  case node left right ih_left ih_right =>
    simp [num_of_leaves, num_of_nodes]
    rw [ih_left, ih_right]
    simp [Nat.add_assoc]
    simp [Nat.add_comm]
    simp [Nat.add_assoc]