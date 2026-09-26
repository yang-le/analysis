import Mathlib.Tactic
import Analysis.Section_2_3

/--
转换第二章的自然数到Mathlib的自然数
-/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl
lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/--
该转换是一个双射
-/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n : Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [← succ_eq_add_one, hn]

section helpers
-- 一些有用的引理
lemma Chapter2.Nat.map_toNat {n m : Chapter2.Nat} : n.toNat = m.toNat → n = m := by
  intro h
  induction' n with n
  · rw [← Nat.equivNat.left_inv zero, ← Nat.equivNat.left_inv m]; dsimp
    rw [zero_toNat, ← h]
  · rw [← Nat.equivNat.left_inv (n++), ← Nat.equivNat.left_inv m]; dsimp
    rw [succ_toNat, ← h]
end helpers

/--
该转换保加法
-/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  · rw [succ_add, succ_toNat, succ_toNat, hn]
    rw [_root_.Nat.add_assoc, _root_.Nat.add_comm m.toNat, ← _root_.Nat.add_assoc]

/--
该转换保留乘法
-/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_mul, _root_.Nat.zero_mul]
  . rw [succ_mul, map_add, hn, succ_toNat, _root_.Nat.add_one_mul]

/--
该转换保留序关系
-/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor <;> induction' n with n hn <;> intro h
  · use m; rfl
  · rw [succ_toNat] at h
    have : n < m := by grind
    rwa [← lt_iff_succ_le]
  · simp
  · rw [← lt_iff_succ_le] at h
    have : n.toNat ≠ m.toNat := by
      by_contra h'
      have := map_toNat h'
      have := ne_of_lt _ _ h
      contradiction
    grind

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/--
该转换保留幂运算
-/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n ^ m).toNat := by
  · induction' m with m hm
    · rw [show zero = 0 from rfl, pow_zero, _root_.Nat.pow_zero]
    · rw [succ_toNat, pow_succ, _root_.Nat.pow_succ, hm, map_mul]

/--
皮亚诺公理
-/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- 公理 2.1
  succ : Nat → Nat -- 公理 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- 公理 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- 公理 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- 公理 2.5

namespace PeanoAxioms

def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/--
我们可以把Mathlib的自然数映射到任何遵循皮亚诺公理的结构
-/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  intro n
  have hcast : ∀ x, P.natCast (x + 1) = P.succ (natCast P x) := by grind
  induction' n with n hn <;> intro m <;> induction' m with m _
  · intro _; rfl
  · intro h
    rw [hcast] at h
    absurd h
    push Not
    symm
    exact P.succ_ne _
  · intro h
    rw [hcast] at h
    absurd h
    exact P.succ_ne _
  · intro h
    rw [hcast, hcast] at h
    have := hn (P.succ_cancel h)
    rw [this]

theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  apply P.induction
  · use 0
  · intro n ⟨a, ha⟩
    use a + 1
    have : P.natCast (a + 1) = P.succ (natCast P a) := by rfl
    rw [this, ha]

class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

abbrev Equiv.symm {P Q : PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    have := equiv.equiv_zero.symm
    grind
  equiv_succ n := by
    have := equiv.equiv_succ
    grind

abbrev Equiv.trans {P Q R : PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    have h1 := equiv1.equiv_zero
    have h2 := equiv2.equiv_zero
    grind
  equiv_succ n := by
    have h1 := equiv1.equiv_succ
    have h2 := equiv2.equiv_succ
    grind

noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := Function.surjInv (natCast_surjective P)
    left_inv := Function.leftInverse_surjInv ⟨natCast_injective P, natCast_surjective P⟩
    right_inv := Function.rightInverse_surjInv (natCast_surjective P)
  }
  equiv_zero := P.succ_cancel rfl
  equiv_succ _ := P.succ_cancel rfl

/--
任意两个遵循皮亚诺公理的结构是等价的
-/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q :=
  Equiv.trans (Equiv.fromNat P).symm (Equiv.fromNat Q)

/--
任意两个遵循皮亚诺公理的结构之间的等价是唯一的
-/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  revert n
  apply P.induction
  · rw [equiv_zero1, equiv_zero2]
  · intro n hn
    rw [equiv_succ1 n, equiv_succ2 n, hn]

/--
例：递归在任何遵循皮亚诺公理的结构上都是良定义的
-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f : P.Nat → P.Nat → P.Nat) (c : P.Nat) :
    ∃! (a : P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  sorry

end PeanoAxioms
