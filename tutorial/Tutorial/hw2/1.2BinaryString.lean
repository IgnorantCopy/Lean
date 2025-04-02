inductive BinaryStr : Type
  | null : BinaryStr
  | add : BinaryStr → Bool → BinaryStr
  | plus : BinaryStr → BinaryStr → BinaryStr

open BinaryStr

def length : BinaryStr → Nat
  | null => 0
  | add s _ => 1 + length s
  | plus s1 s2 => length s1 + length s2

-- 101开头且长度为偶数的二进制字符串
inductive EvenLength101 : BinaryStr → Prop
  | base0 : EvenLength101 (add (add (add (add null true) false) true) false)
  | base1 : EvenLength101 (add (add (add (add null true) false) true) true)
  | step s src : EvenLength101 src → 
    (length s = 2) → EvenLength101 (plus src s)


-- 长度模5余2的二进制字符串
inductive Mod5Rem2Length : BinaryStr → Prop
  | base s : (length s = 2) → Mod5Rem2Length (plus null s)
  | step s src : Mod5Rem2Length src → 
    (length s = 5) → Mod5Rem2Length (plus src s)


-- 拥有偶数个 0 的二进制字符串
inductive Even0 : BinaryStr → Prop
  | empty : Even0 null
  | step_0_0_ s1 s2 s3 : Even0 (plus (add (plus (add s1 false) s2) false) s3)
  | step1 s : Even0 (add s true)


def count_zero : BinaryStr → Nat
  | null => 0
  | add s n =>
    if n then
      count_zero s
    else
      1 + count_zero s
  | plus s1 s2 => count_zero s1 + count_zero s2


theorem even_odd_zero : ∀ str : BinaryStr, count_zero str % 2 = 0 ∨ count_zero str % 2 = 1 := by
  intro tree
  exact Nat.mod_two_eq_zero_or_one (count_zero tree)
