import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/--
定义 3.5.1 有序对

若`x`和`y`是任意两个对象（它们有可能相等），那么我们把**有序对**`(x, y)`定义为一个把`x`作为第一个分量，`y`作为第二个分量的新对象。
-/
@[ext]
structure OrderedPair where
  fst : Object
  snd : Object

#check OrderedPair.ext

/--
定义 3.5.1 有序对

两个有序对`(x, y)`和`(x', y')`被认为是相当的，当且仅当它们的两个分量都相等，即
`(x, y) = (x', y') ↔ (x = x' ∧ y = y')`
-/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
  (⟨x, y⟩ : OrderedPair) = (⟨x', y'⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

lemma SetTheory.Set.pair_eq_singleton_iff {a b c : Object} : {a, b} = ({c} : Set) ↔ a = c ∧ b = c := by
  constructor
  · intro h
    rw [Set.ext_iff] at h
    have := h a
    simp_all
  · rintro ⟨rfl, rfl⟩
    aesop

/--
习题 3.5.1
-/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({(({p.fst} : Set) : Object), (({p.fst, p.snd} : Set) : Object)} : Set)
  inj' := by
    intro x y h
    rw [eq]
    simp at h
    obtain (⟨h1, h2⟩ | ⟨h1, h2⟩) := pair_eq_pair h <;> simp_all <;> constructor
    · have : x.fst ∈ ({y.fst} : Set) := by
        rw [← h1]; simp
      simpa only [mem_singleton]
    · obtain (⟨h21, h22⟩ | ⟨h21, h22⟩) := pair_eq_pair h2
      · assumption
      · rw [← h21, h22]
        have : x.fst ∈ ({y.fst} : Set) := by
          rw [← h1]; simp
        symm; simpa only [mem_singleton]
    · have : x.fst ∈ ({y.fst} : Set) := by
        rw [← h2]; simp
      simpa only [mem_singleton]
    · have : x.snd ∈ ({y.fst} : Set) := by
        rw [← h2]; simp
      have : x.snd = y.fst := by simpa only [mem_singleton]
      have : x.fst ∈ ({y.fst} : Set) := by
        rw [← h2]; simp
      have : x.fst = y.fst := by simpa only [mem_singleton]
      have : y.snd ∈ ({x.fst} : Set) := by
        rw [h1]; simp
      have : y.snd = x.fst := by simpa only [mem_singleton]
      grind only

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

abbrev SetTheory.Set.slice (x : Object) (Y : Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩ : OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z : Object) (Y : Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y : Y, z = (⟨x, y⟩ : OrderedPair) := replacement_axiom _ _

/--
定义 3.5.4 笛卡儿积

如果`X`和`Y`是集合，那么我们定义**笛卡儿积**`X × Y`为第一个分量在`X`中且第二个分量在`Y`中的全体有序对的集合，因此
`X × Y = {(x, y) : x ∈ X, y ∈ Y}`
或等价地，
`a ∈ (X × Y) ↔ ∃ x ∈ X, ∃ y ∈ Y, a = (x, y)`
-/
abbrev SetTheory.Set.cartesian (X Y : Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y : Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z : Object) (X Y : Set) :
    z ∈ X ×ˢ Y ↔ ∃ x : X, ∃ y : Y, z = (⟨x, y⟩ : OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  · intro ⟨S, hz, hS⟩; rw [replacement_axiom] at hS; obtain ⟨x, hx⟩ := hS
    use x; simp_all
  rintro ⟨x, y, rfl⟩; use slice x Y; refine ⟨by simp, ?_⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.fst {X Y : Set} (z : X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y : Set} (z : X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y : Set} (z : X ×ˢ Y) :
    z.val = (⟨fst z, snd z⟩ : OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨y, hy : z.val = ((⟨fst z, y⟩ : OrderedPair))⟩ := this.choose_spec
  obtain ⟨x, hx : z.val = ((⟨x, snd z⟩ : OrderedPair))⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

def SetTheory.Set.mk_cartesian {X Y : Set} (x : X) (y : Y) : X ×ˢ Y :=
  ⟨(⟨x, y⟩ : OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y : Set} (x : X) (y : Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨y', hy : z.val = ((⟨fst z, y'⟩ : OrderedPair))⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [← hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y : Set} (x : X) (y : Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨x', hx : z.val = ((⟨x', snd z⟩ : OrderedPair))⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [← hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y : Set} (z : X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y : Set) :
    ((X ×ˢ Y) : _root_.Set Object) ≃ (X : _root_.Set Object) ×ˢ (Y : _root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/--
例 3.5.6
-/
example : ({1, 2} : Set) ×ˢ ({3, 4, 5} : Set) = ({
  ((mk_cartesian (1 : Nat) (3 : Nat)) : Object),
  ((mk_cartesian (1 : Nat) (4 : Nat)) : Object),
  ((mk_cartesian (1 : Nat) (5 : Nat)) : Object),
  ((mk_cartesian (2 : Nat) (3 : Nat)) : Object),
  ((mk_cartesian (2 : Nat) (4 : Nat)) : Object),
  ((mk_cartesian (2 : Nat) (5 : Nat)) : Object)
} : Set) := by ext; aesop

/--
习题 3.6.5

是的，你没看错，确实是3.6.5
-/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y : Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun z := ⟨mk_cartesian (snd z) (fst z), by grind only⟩
  invFun z := ⟨mk_cartesian (snd z) (fst z), by grind only⟩
  left_inv _ := by simp
  right_inv _ := by simp

/--
例 3.5.6
-/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z : Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f (mk_cartesian x y)
  left_inv _ := by ext; simp
  right_inv _ := by simp

/--
定义 3.5.7 有序`n`元组

设`n`是一个自然数，**有序`n`元组**`(xᵢ)_{1 ≤ i ≤ n}`（也记作`(x₁, ⋯, xₙ)`）是由对象`x₁, ⋯, xₙ`按次序构成的一个组，
我们把`xᵢ`称为有序`n`元组的第`i`个分量。
-/
abbrev SetTheory.Set.tuple {I : Set} {X : I → Set} (x : ∀ i, X i) : Object :=
  ((fun i ↦ ⟨x i, by rw [mem_iUnion]; use i; exact (x i).property⟩) : I → iUnion I X)

/--
定义 3.5.7 `n`重笛卡儿积

如果`(Xᵢ)_{1 ≤ i ≤ n}`是集合的有序`n`元组，我们定义它们的**笛卡儿积**`Π_{1 ≤ i ≤ n} Xᵢ`（也记作`Πⁿ_{i = 1} Xᵢ`或`X₁ × ⋯ × Xₙ`）为
`Π_{1 ≤ i ≤ n} Xᵢ := {(xᵢ)_{1 ≤ i ≤ n} : ∀ 1 ≤ i ≤ n, xᵢ ∈ Xᵢ}`
-/
abbrev SetTheory.Set.iProd {I : Set} (X : I → Set) : Set :=
  ((iUnion I X) ^ I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

end Chapter3
