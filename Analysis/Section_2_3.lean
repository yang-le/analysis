import Mathlib.Tactic
import Analysis.Section_2_2

namespace Chapter2

/--
定义 2.3.1 自然数的乘法

令$`m`表示任意一个自然数。我们定义$`0 × m := 0`来表示把$`0`乘到$`m`上。
现在归纳性地假设已经定义了如何把$`n`乘到$`m`上，那么我们可以通过定义$`(n++) × m := (n × m) + m`把$`n++`乘到$`m`上。
-/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

instance Nat.instMul : Mul Nat where
  mul := mul

theorem Nat.zero_mul (m : Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod + m) _

theorem Nat.succ_mul (n m : Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod + m) _ _

theorem Nat.one_mul' (m : Nat) : 1 * m = 0 + m := by
  rw [← zero_succ, succ_mul, zero_mul]

theorem Nat.one_mul (m : Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m : Nat) : 2 * m = 0 + m + m := by
  rw [← one_succ, succ_mul, one_mul']

lemma Nat.mul_zero (n : Nat) : n * 0 = 0 := by
  revert n; apply induction
  · exact zero_mul _
  · intro n hn
    rw [succ_mul, hn]; simp

lemma Nat.mul_succ (n m : Nat) : n * m++ = n * m + n := by
  revert n; apply induction
  · rw [zero_mul, zero_mul]; simp
  · intro n hn
    rw [succ_mul, hn, succ_mul, succ_eq_add_one, succ_eq_add_one]; abel

/--
引理 2.3.2 乘法是可交换的

令$`n`和$`m`表示任意两个自然数，那么有$`n × m = m × n`成立。
-/
lemma Nat.mul_comm (n m : Nat) : n * m = m * n := by
  revert n; apply induction
  · rw [zero_mul, mul_zero]
  · intro n hn
    rw [succ_mul, mul_succ, hn]

theorem Nat.mul_one (m : Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

lemma Nat.pos_mul_pos {n m : Nat} (h₁ : n.IsPos) (h₂ : m.IsPos) : (n * m).IsPos := by
  revert n; apply induction
  · intro h
    absurd h
    rfl
  · intro _ _ _
    rw [succ_mul]
    apply add_pos_right
    exact h₂

/--
引理 2.3.3 正自然数没有零因子

设$`n, m`为自然数。那么$`n × m = 0`当且仅当$`n`和$`m`至少有一个为零。
特别地，如果$`n`和$`m`均为正的，那么$`nm`也是正的。
-/
lemma Nat.mul_eq_zero (n m : Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · left
      exact hn
    · right
      by_contra hm
      have := pos_mul_pos hn hm
      contradiction
  · rintro (rfl | rfl)
    exact zero_mul m
    exact mul_zero n

/--
命题 2.3.4 分配律

对于任意自然数$`a, b, c`，$`a(b + c) = ab + ac`成立。
-/
theorem Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  revert c; apply induction
  · rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ← add_assoc, ← habc]

/--
命题 2.3.4 分配律

对于任意自然数$`a, b, c`，$`(a + b)c = ac + bc`成立。
-/
theorem Nat.add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  simp only [mul_comm, mul_add]

/--
命题 2.3.5 乘法是可结合的

对任意自然数$`a, b, c`，$`(a × b) × c = a × (b × c)`均成立。
-/
theorem Nat.mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  revert a; apply induction
  · simp only [zero_mul]
  · intro n hn
    simp only [succ_mul, ← hn, add_mul]

instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

example (a b c d : Nat) : (a + b) * 1 * (c + d) = d * b + a * c + c * b + a * d + 0 := by ring

/--
命题 2.3.6 乘法保持序不变

如果$`a, b`是满足$`a < b`的自然数，并且$`c`是正的，那么$`ac < bc`
-/
theorem Nat.mul_lt_mul_of_pos_right {a b c : Nat} (h : a < b) (hc : c.IsPos) : a * c < b * c := by
  rw [lt_iff_add_pos] at h
  choose d hdpos hd using h
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d * c

/--
命题 2.3.6 乘法保持序不变

如果$`a, b`是满足$`a > b`的自然数，并且$`c`是正的，那么$`ac > bc`
-/
theorem Nat.mul_gt_mul_of_pos_right {a b c : Nat} (h : a > b) (hc : c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/--
命题 2.3.6 乘法保持序不变

如果$`a, b`是满足$`a < b`的自然数，并且$`c`是正的，那么$`ca < cb`
-/
theorem Nat.mul_lt_mul_of_pos_left {a b c : Nat} (h : a < b) (hc : c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/--
命题 2.3.6 乘法保持序不变

如果$`a, b`是满足$`a > b`的自然数，并且$`c`是正的，那么$`ca > cb`
-/
theorem Nat.mul_gt_mul_of_pos_left {a b c : Nat} (h : a > b) (hc : c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/--
推论 2.3.7 消去律

设$`a, b, c`是自然数，满足$`ac = bc`且$`c`不为零，那么$`a = b`
-/
lemma Nat.mul_cancel_right {a b c : Nat} (h : a * c = b * c) (hc : c.IsPos) : a = b := by
  have := trichotomous a b
  obtain hlt | rfl | hgt := this
  · replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  · rfl
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  apply ne_of_gt at hgt
  contradiction

instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by decide
  mul_le_mul_of_nonneg_left := by
    intro a _ _ _ hbc
    rw [le_iff_lt_or_eq] at hbc
    rw [le_iff_lt_or_eq]
    by_cases ha : a = 0
    · right
      simp only [ha, zero_mul]
    · rcases hbc with (hbc | hbc)
      · left
        exact mul_lt_mul_of_pos_left hbc ha
      · right
        rw [hbc]
  mul_le_mul_of_nonneg_right := by
    intro c _ _ _ hab
    rw [le_iff_lt_or_eq] at hab
    rw [le_iff_lt_or_eq]
    by_cases hc : c = 0
    · right
      simp only [hc, mul_zero]
    · rcases hab with (hab | hab)
      · left
        exact mul_lt_mul_of_pos_right hab hc
      · right
        rw [hab]

example (a b c d : Nat) (hab : a ≤ b) : c * a * d ≤ c * b * d := by
  gcongr
  · exact d.zero_le
  exact c.zero_le

/--
命题 2.3.9 欧几里得除法（带余除法）

设$`n`是一个自然数，$`q`表示一个正自然数，那么存在自然数$`m`和$`r`使得$`0 ≤ r < q`并且$`n = mq + r`。
也就是说，我们可以用一个正自然数$`q`去除一个自然数$`n`，从而得到商$`m`（另一个自然数）和余数$`r`（比$`q`小）
-/
theorem Nat.exists_div_mod (n : Nat) {q : Nat} (hq : q.IsPos) :
    ∃ m r : Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  revert n; apply induction
  · use 0, 0
    simp
    constructor
    · use q; simp
    · symm; rwa [← isPos_iff]
  · intro n ⟨m, r, h1, h2, h3⟩
    by_cases h : r + 1 = q
    · use m + 1, 0
      simp
      constructor
      · constructor
        · use q; simp
        · symm; rwa [← isPos_iff]
      · rw [succ_eq_add_one, h3, ← h]
        ring
    · use m, r + 1
      constructor
      · use r + 1; simp
      · constructor
        · constructor
          · rwa [lt_iff_succ_le, succ_eq_add_one] at h2
          · exact h
        · rw [succ_eq_add_one, h3, add_assoc]

/--
定义 2.3.11 自然数的指数运算

设$`m`是一个自然数。我们定义$`m⁰ := 1`来表示把$`m`升到$`0`次幂；特别地，定义$`0⁰ = 1`。
现在递归地假设对于某个自然数$`n`,$`mⁿ`已经被定义了，那么我们定义$`m^{(n++)} := mⁿ × m`
-/
abbrev Nat.pow (m n : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

@[simp]
theorem Nat.pow_zero (m : Nat) : m ^ (0 : Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

@[simp]
theorem Nat.zero_pow_zero : (0 : Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

theorem Nat.pow_succ (m n : Nat) : (m : Nat) ^ n++ = m ^ n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

@[simp]
theorem Nat.pow_one (m : Nat) : m ^ (1 : Nat) = m := by
  rw [← zero_succ, pow_succ]; simp

theorem Nat.sq_add_eq (a b : Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  simp [← one_succ, pow_succ]
  rw [one_succ]; ring; rfl

end Chapter2
