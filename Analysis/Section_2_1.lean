import Mathlib.Tactic

namespace Chapter2

/--
假设 2.6

（非正式的） 存在一个数系ℕ，我们称ℕ中的元素为自然数
-/
inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq

/--
公理 2.1

`0`是一个自然数
-/
instance Nat.instZero : Zero Nat := ⟨zero⟩
#check (0:Nat)

/--
公理 2.2

如果`n`是一个自然数，那么`n++`也是一个自然数
-/
postfix:100 "++" => Nat.succ
#check (fun n ↦ n++)

/--
定义 2.1.3

定义`1`为数字`0++`, `2`为数字`1++`, `3`为数字`2++`, 等等
-/
instance Nat.instOfNat {n : _root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

instance Nat.instOne : One Nat := ⟨1⟩
lemma Nat.zero_succ : 0++ = 1 := by rfl
#check (1:Nat)

lemma Nat.one_succ : 1++ = 2 := by rfl
#check (2:Nat)

/--
命题 2.1.4

`3`是一个自然数
-/
lemma Nat.two_succ : 2++ = 3 := by rfl
#check (3:Nat)

/--
公理 2.3

`0`不紧跟在任何自然数之后。换言之，对任意一个自然数`n`, `n++ ≠ 0`均成立
-/
theorem Nat.succ_ne (n : Nat) : n++ ≠ 0 := by
  by_contra h
  injection h

/--
命题 2.1.6

`4`不等于`0`
-/
theorem Nat.four_ne : (4 : Nat) ≠ 0 := by
  -- 根据定义，`4 = 3++`
  change 3++ ≠ 0
  -- 根据公理 2.3, `3++`不等于0
  exact succ_ne _

/--
公理 2.4

对于不同的自然数而言，紧跟在它们之后的数字也一定是不同的。
也就是说，如果`n`和`m`都是自然数，并且`n ≠ m`，那么`n++ ≠ m++`。
等价说法为，如果`n++ = m++`，那么一定有`n = m`。
-/
theorem Nat.succ_cancel {n m : Nat} (hnm : n++ = m++) : n = m := by
  injection hnm

/--
公理 2.4

对于不同的自然数而言，紧跟在它们之后的数字也一定是不同的。
也就是说，如果`n`和`m`都是自然数，并且`n ≠ m`，那么`n++ ≠ m++`。
等价说法为，如果`n++ = m++`，那么一定有`n = m`。
-/
theorem Nat.succ_ne_succ (n m : Nat) : n ≠ m → n++ ≠ m++ := by
  intro h
  contrapose h
  exact succ_cancel h

/--
命题 2.1.8

`6`不等于`2`
-/
theorem Nat.six_ne_two : (6 : Nat) ≠ 2 := by
  by_contra h
  change 5++ = 1++ at h
  apply succ_cancel at h
  change 4++ = 0++ at h
  apply succ_cancel at h
  have := four_ne
  contradiction

/--
命题 2.1.8

`6`不等于`2`
-/
theorem Nat.six_ne_two' : (6 : Nat) ≠ 2 := by
  decide

/--
公理 2.5 数学归纳原理

令`P(n)`表示自然数`n`的任意一个性质，如果`P(0)`为真且`P(n)`为真时一定有`P(n++)`也为真，
那么对于任意自然数`n`，`P(n)`一定为真。
-/
theorem Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind _ ih

/-- `recurse f c`给出一个数列`aₙ`，满足`a₀ = c`且`a_{n++} = fₙ(aₙ)` -/
abbrev Nat.recurse (f : Nat → Nat → Nat) (c : Nat) : Nat → Nat := fun n ↦ match n with
| 0 => c
| n++ => f n (recurse f c n)

/--
命题 2.16 递归定义

假设对任意自然数`n`，都存在某个从自然数系到自然数系的函数`fₙ : ℕ → ℕ`，令`c`为某个固定的自然数。
那么对任意自然数`n`，都能够确定唯一的自然数`aₙ`，使得`a₀ = c`以及`a_{n++} = fₙ(aₙ)`恒成立。
-/
theorem Nat.recurse_zero (f : Nat → Nat → Nat) (c : Nat) : Nat.recurse f c 0 = c := by rfl

/--
命题 2.16 递归定义

假设对任意自然数`n`，都存在某个从自然数系到自然数系的函数`fₙ : ℕ → ℕ`，令`c`为某个固定的自然数。
那么对任意自然数`n`，都能够确定唯一的自然数`aₙ`，使得`a₀ = c`以及`a_{n++} = fₙ(aₙ)`恒成立。
-/
theorem Nat.recurse_succ (f : Nat → Nat → Nat) (c : Nat) (n : Nat) :
    Nat.recurse f c (n++) = f n (recurse f c n) := by rfl

/--
命题 2.16 递归定义

假设对任意自然数`n`，都存在某个从自然数系到自然数系的函数`fₙ : ℕ → ℕ`，令`c`为某个固定的自然数。
那么对任意自然数`n`，都能够确定唯一的自然数`aₙ`，使得`a₀ = c`以及`a_{n++} = fₙ(aₙ)`恒成立。
-/
theorem Nat.eq_recurse (f : Nat → Nat → Nat) (c : Nat) (a : Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c := by
  constructor
  · intro ⟨h0, hsucc⟩
    apply funext; apply induction
    · exact h0
    intro n hn
    rw [hsucc n, recurse_succ, hn]
  intro h
  rw [h]
  constructor
  · exact recurse_zero _ _
  exact recurse_succ _ _

/--
命题 2.16 递归定义

假设对任意自然数`n`，都存在某个从自然数系到自然数系的函数`fₙ : ℕ → ℕ`，令`c`为某个固定的自然数。
那么对任意自然数`n`，都能够确定**唯一**的自然数`aₙ`，使得`a₀ = c`以及`a_{n++} = fₙ(aₙ)`恒成立。
-/
theorem Nat.recurse_uniq (f : Nat → Nat → Nat) (c : Nat) :
    ∃! (a : Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
  apply ExistsUnique.intro (recurse f c)
  · constructor
    · exact recurse_zero _ _
    · exact recurse_succ _ _
  intro a
  exact (eq_recurse _ _ a).mp

end Chapter2
