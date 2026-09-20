import Mathlib.Tactic
import Analysis.Section_2_1

namespace Chapter2

/--
定义 2.2.1 自然数的加法

令{lit}`m`为一个自然数，我们定义{lit}`m`加上{lit}`0`为{lit}`0 + m := m`。
现在递归地假设我们已经定义了如何把{lit}`m`加上{lit}`n`，那么我们把{lit}`m`加上{lit}`n++`定义为{lit}`(n++) + m := (n + m)++`。
-/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

instance Nat.instAdd : Add Nat where add := add

@[simp]
theorem Nat.zero_add (m : Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

theorem Nat.succ_add (n m : Nat) : n++ + m = (n + m)++ := by rfl

theorem Nat.one_add (m : Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m : Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2 : Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++ = 4 from rfl, show 4++ = 5 from rfl]

-- 两个自然数的和仍为自然数
#check (fun (n m : Nat) ↦ n + m)

/--
引理 2.2.2

对任意的自然数{lit}`n`, {lit}`n + 0 = n`恒成立
-/
@[simp]
lemma Nat.add_zero (n : Nat) : n + 0 = n := by
  revert n; apply induction
  · exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/--
引理 2.2.3

对任意的自然数{lit}`n`和{lit}`m`，有{lit}`n + (m++) = (n + m)++`成立。
-/
lemma Nat.add_succ (n m : Nat) : n + (m++) = (n + m)++ := by
  revert n; apply induction
  · rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]

theorem Nat.succ_eq_add_one (n : Nat) : n++ = n + 1 := by
  symm
  calc
    n + 1 = n + (0++) := by rfl
    _ = (n + 0)++ := add_succ _ _
    _ = n++ := by rw [add_zero]

/--
命题 2.2.4 加法是可交换的

对任意的自然数{lit}`n`和{lit}`m`，有{lit}`n + m = m + n`成立。
-/
theorem Nat.add_comm (n m : Nat) : n + m = m + n := by
  revert n; apply induction
  · rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/--
命题 2.2.5 加法是可结合的

对任意的自然数{lit}`a、b、c`，有{lit}`(a + b) + c = a + (b + c)`成立。
-/
theorem Nat.add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  revert a; apply induction
  · rw [zero_add, zero_add]
  intro a ih
  rw [succ_add, succ_add, succ_add, ih]

/--
命题 2.2.6 消去律

令{lit}`a、b、c`为任意三个自然数且满足{lit}`a + b = a + c`，那么{lit}`b = c`成立。
-/
theorem Nat.add_left_cancel (a b c : Nat) (habc : a + b = a + c) : b = c := by
  revert a; apply induction
  · intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc

instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

example (a b c d : Nat) : (a + b) + (c + 0 + d) = (b + c) + (d + a) := by abel

/--
定义 2.2.7 正自然数

称一个自然数{lit}`n`是正的，当且仅当它不等于{lit}`0`
-/
def Nat.IsPos (n : Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n : Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/--
命题 2.2.8

如果{lit}`a`是正的并且{lit}`b`是自然数，那么{lit}`a + b`是正的
-/
theorem Nat.add_pos_left {a : Nat} (b : Nat) (ha : a.IsPos) : (a + b).IsPos := by
  revert b; apply induction
  · rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a + b)++ ≠ 0 := succ_ne _
  exact this

/--
命题 2.2.8

如果{lit}`a`是正的并且{lit}`b`是自然数，那么{lit}`b + a`是正的
-/
theorem Nat.add_pos_right {a : Nat} (b : Nat) (ha : a.IsPos) : (b + a).IsPos := by
  grind [add_comm, add_pos_left]

/--
推论 2.2.9

如果{lit}`a`和{lit}`b`是自然数并且满足{lit}`a + b = 0`，那么{lit}`a = 0`且{lit}`b = 0`
-/
theorem Nat.add_eq_zero (a b : Nat) (hab : a + b = 0) : a = 0 ∧ b = 0 := by
  by_contra h
  simp only [not_and_or, ← ne_eq] at h
  obtain ha | hb := h
  · rw [← isPos_iff] at ha
    observe : (a + b).IsPos
    contradiction
  rw [← isPos_iff] at hb
  observe : (a + b).IsPos
  contradiction

/-
`Tools/ExistsUnique.lean`里的API，特别是方法`existsUnique_of_exists_of_unique`，可能对下面的问题有用。
另外，`obtain`策略可用于从存在性声明中提取证据；例如，`obtain ⟨x, hx⟩ := h`从假设`h : ∃ x, P x`中提取值`x`以及证明`hx : P x`.
-/

#check existsUnique_of_exists_of_unique

/--
引理 2.2.10

令{lit}`a`表示一个正自然数，那么恰存在一个自然数{lit}`b`使得{lit}`b++ = a`
-/
lemma Nat.uniq_succ_eq (a : Nat) (ha : a.IsPos) : ∃! b, b++ = a := by
  have h : ∃ x, x++ = a := by
    revert a; apply induction
    · intro h
      contradiction
    intro n _ _
    use n
  apply existsUnique_of_exists_of_unique
  · exact h
  obtain ⟨_, h'⟩ := h
  intro _ _ h₁ h₂
  rw [← h'] at h₁ h₂
  rw [succ_cancel h₁, succ_cancel h₂]

/--
定义 2.2.11 自然数的排序

令{lit}`n`和{lit}`m`表示任意两个自然数。我们称{lit}`n`大于等于{lit}`m`，并且记作{lit}`n ≥ m`或者{lit}`m ≤ n`，当且仅当存在自然数{lit}`a`使得{lit}`n = m + a`。
-/
instance Nat.instLE : LE Nat where
  le m n := ∃ a : Nat, n = m + a


/--
定义 2.2.11 自然数的排序

令{lit}`n`和{lit}`m`表示任意两个自然数。我们称{lit}`n`严格大于{lit}`m`，并且记作{lit}`n > m`或者{lit}`m < n`，当且仅当{lit}`n ≥ m`且{lit}`n ≠ m`。
-/
instance Nat.instLT : LT Nat where
  lt m n := m ≤ n ∧ m ≠ n

lemma Nat.le_iff (n m : Nat) : n ≤ m ↔ ∃ a : Nat, m = n + a := by rfl
lemma Nat.lt_iff (n m : Nat) : n < m ↔ (∃ a : Nat, m = n + a) ∧ n ≠ m := by rfl

@[symm]
lemma Nat.ge_iff_le (n m : Nat) : n ≥ m ↔ m ≤ n := by rfl

@[symm]
lemma Nat.gt_iff_lt (n m : Nat) : n > m ↔ m < n := by rfl

lemma Nat.le_of_lt {n m : Nat} (hnm : n < m) : n ≤ m := hnm.1

lemma Nat.le_iff_lt_or_eq (n m : Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  · simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8 : Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  · have : (8 : Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

theorem Nat.succ_gt_self (n : Nat) : n++ > n := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  · rw [succ_eq_add_one]
    use 1
  rw [succ_eq_add_one]
  nth_rw 1 [← add_zero n]
  by_contra h
  apply add_left_cancel at h
  contradiction

end Chapter2
