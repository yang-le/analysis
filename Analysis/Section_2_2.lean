import Mathlib.Tactic
import Analysis.Section_2_1

namespace Chapter2

/--
定义 2.2.1 自然数的加法

令`m`为一个自然数，我们定义`m`加上`0`为`0 + m := m`。
现在递归地假设我们已经定义了如何把`m`加上`n`，那么我们把`m`加上`n++`定义为`(n++) + m := (n + m)++`。
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

对任意的自然数`n`, `n + 0 = n`恒成立
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

对任意的自然数`n`和`m`，有`n + (m++) = (n + m)++`成立。
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

对任意的自然数`n`和`m`，有`n + m = m + n`成立。
-/
theorem Nat.add_comm (n m : Nat) : n + m = m + n := by
  revert n; apply induction
  · rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/--
命题 2.2.5 加法是可结合的

对任意的自然数`a、b、c`，有`(a + b) + c = a + (b + c)`成立。
-/
theorem Nat.add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  revert a; apply induction
  · rw [zero_add, zero_add]
  intro a ih
  rw [succ_add, succ_add, succ_add, ih]

/--
命题 2.2.6 消去律

令`a、b、c`为任意三个自然数且满足`a + b = a + c`，那么`b = c`成立。
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

称一个自然数`n`是正的，当且仅当它不等于`0`
-/
def Nat.IsPos (n : Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n : Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/--
命题 2.2.8

如果`a`是正的并且`b`是自然数，那么`a + b`是正的
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

如果`a`是正的并且`b`是自然数，那么`b + a`是正的
-/
theorem Nat.add_pos_right {a : Nat} (b : Nat) (ha : a.IsPos) : (b + a).IsPos := by
  grind [add_comm, add_pos_left]

/--
推论 2.2.9

如果`a`和`b`是自然数并且满足`a + b = 0`，那么`a = 0`且`b = 0`
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

令`a`表示一个正自然数，那么恰存在一个自然数`b`使得`b++ = a`
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

令`n`和`m`表示任意两个自然数。我们称`n`大于等于`m`，并且记作`n ≥ m`或者`m ≤ n`，当且仅当存在自然数`a`使得`n = m + a`。
-/
instance Nat.instLE : LE Nat where
  le m n := ∃ a : Nat, n = m + a


/--
定义 2.2.11 自然数的排序

令`n`和`m`表示任意两个自然数。我们称`n`严格大于`m`，并且记作`n > m`或者`m < n`，当且仅当`n ≥ m`且`n ≠ m`。
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

/-
命题 2.2.12 自然数的序的基本性质

令`a`、`b`、`c`为任意自然数，那么
- `a ≥ a`
- 如果`a ≥ b`并且`b ≥ c`，那么`a ≥ c`
- 如果`a ≥ b`并且`b ≥ a`，那么`a = b`
- `a ≥ b`当且仅当`a + c ≥ b + c`
- `a < b`当且仅当`a++ ≤ b`
- `a < b`当且仅当存在正自然数`d`使得`b = a + d`
-/

theorem Nat.ge_refl (a : Nat) : a ≥ a := by
  use 0
  rw [add_zero]

@[refl]
theorem Nat.le_refl (a : Nat) : a ≤ a := a.ge_refl

/-- `refl`标签使得{tactic}`rfl`可以适用于不等式 -/
example (a b : Nat) : a + b ≥ a + b := by rfl

theorem Nat.ge_trans {a b c : Nat} (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  use y + x
  rw [← add_assoc, ← hy, ← hx]

theorem Nat.le_trans {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := Nat.ge_trans hbc hab

theorem Nat.ge_antisymm {a b : Nat} (hab : a ≥ b) (hba : b ≥ a) : a = b := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hba
  nth_rw 1 [hx, ← add_zero b, add_assoc] at hy
  apply add_left_cancel at hy
  have := (add_eq_zero x y hy.symm).1
  rwa [this, add_zero] at hx

theorem Nat.add_ge_add_right (a b c : Nat) : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  · rintro ⟨x, rfl⟩
    use x
    rw [add_assoc, add_comm x, ← add_assoc]
  · rintro ⟨x, hx⟩
    rw [add_comm, add_comm b, add_assoc] at hx
    apply add_left_cancel at hx
    use x

theorem Nat.add_ge_add_left (a b c : Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

theorem Nat.add_le_add_right (a b c : Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

theorem Nat.add_le_add_left (a b c : Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

section helpers
-- 一些有用的引理
lemma Nat.le_succ {a : Nat} : a ≤ a++ := by
  use 1
  exact succ_eq_add_one a

lemma Nat.succ_ne_self (a : Nat) : a++ ≠ a := by
  rw [succ_eq_add_one]
  nth_rw 2 [← add_zero a]
  by_contra h
  apply add_left_cancel at h
  contradiction
end helpers

theorem Nat.lt_iff_succ_le (a b : Nat) : a < b ↔ a++ ≤ b := by
  constructor
  · rintro ⟨⟨x, hx⟩, hne⟩
    have xpos : x ≠ 0 := by
      by_contra h
      rw [h, add_zero] at hx
      symm at hx
      contradiction
    obtain ⟨y, hy, _⟩ := uniq_succ_eq x xpos
    use y
    rwa [succ_add, add_comm, ← succ_add, hy, add_comm]
  · intro h
    constructor
    · exact le_trans le_succ h
    · by_contra heq
      rw [← heq] at h
      have h1 := ge_antisymm h le_succ
      have h2 := (succ_ne_self a).symm
      contradiction

theorem Nat.lt_iff_add_pos (a b : Nat) : a < b ↔ ∃ d : Nat, d.IsPos ∧ b = a + d := by
  constructor
  · rintro ⟨⟨x, hx⟩, hne⟩
    use x
    have xpos : x ≠ 0 := by
      by_contra h
      rw [h, add_zero] at hx
      symm at hx
      contradiction
    exact ⟨xpos, hx⟩
  · rintro ⟨d, dpos, hd⟩
    constructor
    · use d
    · by_contra h
      rw [h] at hd
      nth_rw 1 [← add_zero b] at hd
      apply add_left_cancel at hd
      symm at hd
      contradiction

theorem Nat.ne_of_lt (a b : Nat) : a < b → a ≠ b := by
  intro h
  exact h.2

theorem Nat.ne_of_gt (a b : Nat) : a > b → a ≠ b := by
  intro h
  exact h.2.symm

theorem Nat.not_lt_of_gt (a b : Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (le_of_lt h.1) (le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction

theorem Nat.not_lt_self {a : Nat} (h : a < a) : False := by
  apply not_lt_of_gt a a
  simp [h]

theorem Nat.lt_of_le_of_lt {a b c : Nat} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rw [lt_iff_add_pos] at *
  choose d hd using hab
  choose e he1 he2 using hbc
  use d + e; split_ands
  · exact add_pos_right d he1
  · rw [he2, hd, add_assoc]

theorem Nat.zero_le (a : Nat) : 0 ≤ a := by
  use a
  rw [zero_add]

/--
命题 2.2.13 自然数的序的三歧性

令`a`和`b`表示任意两个自然数，那么在下面三种表述中恰有一种表述为真：`a < b`，`a = b`，`a > b`
-/
theorem Nat.trichotomous (a b : Nat) : a < b ∨ a = b ∨ a > b := by
  revert a; apply induction
  · observe why : 0 ≤ b
    rw [le_iff_lt_or_eq] at why
    tauto
  intro a ih
  obtain case1 | case2 | case3 := ih
  · rw [lt_iff_succ_le] at case1
    rw [le_iff_lt_or_eq] at case1
    tauto
  · have why : a++ > b := by
      rw [case2]
      exact succ_gt_self b
    tauto
  have why : a++ > b := by
    rw [gt_iff_lt, lt_iff_succ_le]
    rw [gt_iff_lt, lt_iff_succ_le] at case3
    exact le_trans case3 le_succ
  tauto

def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    use b
    rw [zero_add]
  | a++, b => by
    cases decLe a b with
    | isTrue hle =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        rw [h]
        by_contra succ_le
        have h1 := ge_antisymm succ_le le_succ
        have h2 := (succ_ne_self b).symm
        contradiction
      | isFalse h =>
        apply isTrue
        rw [← lt_iff_succ_le]
        exact ⟨hle, h⟩
    | isFalse h =>
      apply isFalse
      by_contra h
      have := le_trans le_succ h
      contradiction

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans _ _ _ := le_trans
  lt_iff_le_not_ge a b := by
    constructor
    · intro h; refine ⟨le_of_lt h, ?_⟩
      by_contra h'
      exact not_lt_self (lt_of_le_of_lt h' h)
    rintro ⟨h1, h2⟩
    rw [lt_iff, ← le_iff]; refine ⟨h1, ?_⟩
    by_contra h
    subst h
    contradiction
  le_antisymm _ _ hab hba := ge_antisymm hba hab
  le_total a b := by
    obtain h | rfl | h := trichotomous a b
    · left; exact le_of_lt h
    · simp [ge_refl]
    · right; exact le_of_lt h
  toDecidableLE := decidableRel

example (a b c d : Nat) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hda : d ≤ a) : a = c := by order
example (a b c d e : Nat) (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) (hde : d ≤ e) : a + 0 < e := by
  calc
    a + 0 = a := by simp
        _ ≤ b := hab
        _ < c := hbc
        _ ≤ d := hcd
        _ ≤ e := hde

instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left a b hab c := (add_le_add_right a b c).mp hab

example (a b c d e : Nat) (hab : a ≤ b) (hbc : b < c) (hde : d < e) : a + d ≤ c + e := by
  gcongr
  order

/--
命题 2.2.14 强归纳法原理

令`m₀`表示一个自然数，`P(m)`表示与任意自然数`m`有关的性质。假设对任意满足`m ≥ m₀`的自然数`m`，均有如下内容成立：
若`P(m')`对任意满足`m₀ ≤ m' < m`的自然数`m'`均为真，那么`P(m)`也为真。
（特别地，这意味着`P(m₀)`为真，因为当`m = m₀`时，前提中的`m'`取值范围为空。）
于是我们能够断定，对于任意满足`m ≥ m₀`的自然数`m`，`P(m)`为真。
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  intro m hm
  let Q := fun n ↦ ∀ m', m₀ ≤ m' ∧ m' < n → P m'
  have Q' : ∀ n, Q n := by
    intro n
    apply induction Q
    · intro x ⟨_, h⟩
      absurd h; simp
      use x; simp
    · intro n hn x ⟨h1, h2⟩
      apply hind _ h1
      intro y ⟨hy, _⟩
      apply hn
      have : y < n := by
        rw [lt_iff_succ_le, succ_eq_add_one, succ_eq_add_one, ← add_le_add_right] at h2
        order
      exact ⟨hy, this⟩
  exact hind m hm (Q' m)

/--
习题 2.2.6 逆向归纳法原理

令`n`表示一个自然数，令`P(m)`是关于自然数的一个性质并且满足：只要`P(m++)`为真，`P(m)`就为真。
假设`P(n)`也为真，证明：`P(m)`对任意满足`m ≤ n`的自然数`m`均为真。
-/
theorem Nat.backwards_induction {n : Nat} {P : Nat → Prop}
  (hind : ∀ m, P (m++) → P m) (hn : P n) :
    ∀ m, m ≤ n → P m := by
  let Q := fun n ↦ P n → ∀ m, m ≤ n → P m
  have Q' : ∀ n, Q n := by
    intro n
    apply induction
    · intro _ m hm
      have : m ≥ 0 := by use m; simp
      rwa [ge_antisymm this hm]
    · intro k hk1 hk2 x hx
      by_cases h : x ≤ k
      · exact hk1 (hind _ hk2) _ h
      · have : x = k++ := by
          rw [le_iff_lt_or_eq] at hx
          obtain h' | h' := hx
          · rw [lt_iff_succ_le, succ_eq_add_one, succ_eq_add_one, ← add_le_add_right] at h'
            contradiction
          · exact h'
        rwa [this]
  exact Q' n hn

/--
习题 2.2.7 从指定的起点归纳
-/
theorem Nat.induction_from {n : Nat} {P : Nat → Prop} (hind : ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  intro hn m hm
  obtain ⟨k, rfl⟩ := hm
  let Q := fun k ↦ P n → P (n + k)
  have Q' : ∀ k, Q k := by
    intro k
    apply induction
    · intro h; simpa
    · intro _ hm hn
      rw [add_succ]
      exact hind _ (hm hn)
  exact Q' k hn

end Chapter2
