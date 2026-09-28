import Mathlib.Tactic

namespace Chapter3

universe u v

/--
Zermelo-Frankel集合论公理
-/
class SetTheory where
  /-- 公理 3.1 集合 -/
  Set : Type u
  /-- 公理 3.1 对象 -/
  Object : Type v
  /-- 公理 3.1 集合是对象 -/
  set_to_object : Set ↪ Object
  /-- 公理 3.1 属于 -/
  mem : Object → Set → Prop
  /-- 定义 3.1.4 外延公理 -/
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y
  /-- 公理 3.2 空集 -/
  emptyset : Set
  /-- 公理 3.2 空集 -/
  emptyset_mem x : ¬ mem x emptyset
  /-- 公理 3.3 单元素集 -/
  singleton : Object → Set
  /-- 公理 3.3 单元素集 -/
  singleton_axiom x y : mem x (singleton y) ↔ x = y
  /-- 公理 3.4 两集合之并集 -/
  union_pair : Set → Set → Set
  /-- 公理 3.4 两集合之并集 -/
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y)
  /-- 公理 3.5 分离公理 (`A`中使得`P`为真的元素恰好构成`A`的一个子集) -/
  specify A (P : Subtype (mem . A) → Prop) : Set
  /-- 公理 3.5 分离公理 (`A`中使得`P`为真的元素恰好构成`A`的一个子集) -/
  specification_axiom A (P : Subtype (mem . A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x
  /-- 公理 3.6 替代公理 -/
  replace A (P : Subtype (mem . A) → Object → Prop)
    (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set
  /-- 公理 3.6 替代公理 -/
  replacement_axiom A (P : Subtype (mem . A) → Object → Prop)
    (hP : ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y
  /-- 公理 3.7 无穷公理 -/
  nat : Set
  /-- 公理 3.7 无穷公理 -/
  nat_equiv : ℕ ≃ Subtype (mem . nat)
  /-- 公理 3.9 正则公理 -/
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S
  /-- 公理 3.10 幂集公理 -/
  pow : Set → Set → Set
  /-- 公理 3.10 幂集公理 -/
  function_to_object (X : Set) (Y : Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object
  /-- 公理 3.10 幂集公理 -/
  powerset_axiom (X : Set) (Y : Set) (F : Object) :
    mem F (pow X Y) ↔ ∃ f : Subtype (mem . Y) → Subtype (mem . X), function_to_object Y X f = F
  /-- 公理 3.11 并集公理 -/
  union : Set → Set
  /-- 公理 3.11 并集公理 -/
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A

export SetTheory (Set Object)
variable [SetTheory]

/--
定义 3.1.1

我们把集合`A`定义为任意一堆没有次序的对像.
如果`x`是这堆对象中的一个, 那么我们称`x`是`A`中的元素, 记作`x ∈ A`; 否则, 记作`x ∉ A`.
-/
instance SetTheory.objects_mem_sets : Membership Object Set where
  mem X x := mem x X

example (X : Set) (x : Object) : x ∈ X ↔ SetTheory.mem x X := by rfl

/--
公理 3.1 集合是对象

如果`A`是一个集合, 那么`A`也是一个对象.
-/
instance SetTheory.sets_are_objects : Coe Set Object where
  coe X := set_to_object X

example (X : Set) : (X : Object) = SetTheory.set_to_object X := rfl

/--
公理 3.1 集合是对象

如果`A`是一个集合, 那么`A`也是一个对象.
-/
theorem SetTheory.Set.coe_eq {X Y : Set} (h : (X : Object) = (Y : Object)) : X = Y :=
  set_to_object.inj' h

@[simp]
theorem SetTheory.Set.coe_iff (X Y : Set) : (X : Object) = (Y : Object) ↔ X = Y :=
  ⟨coe_eq, by intro rfl; rfl⟩

/--
定义 3.1.4 集合的相等

称两个集合`A`和`B`是相等的, 即`A = B`, 当且仅当`A`中的每个元素都是`B`中的元素并且`B`中的每个元素也都是`A`中的元素.
-/
@[ext]
theorem SetTheory.Set.ext {X Y : Set} (h : ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := extensionality _ _ h

#check SetTheory.Set.ext_iff

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := emptyset

example : ∅ = SetTheory.emptyset := rfl

open SetTheory.Set

/--
公理 3.2 空集

存在一个集合`∅`, 被称为空集, 它不包含任何元素. 也就是说, 对于任意的对象`x`均有`x ∉ ∅`.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅ : Set) := emptyset_mem

theorem SetTheory.Set.eq_empty_iff_forall_notMem {X : Set} : X = ∅ ↔ (∀ x, x ∉ X) := by
  constructor
  · intro rfl; simp
  · intro h
    ext x
    constructor
    · intro hx
      absurd hx
      exact h x
    · intro hx
      absurd hx
      simp

theorem SetTheory.Set.empty_unique : ∃! (X : Set), ∀ x, x ∉ X := by
  use ∅; simp
  intro _ h
  exact eq_empty_iff_forall_notMem.mpr h

/--
引理 3.1.6 单个选取

设`A`是一个非空集合, 那么存在一个对象`x`使得`x ∈ A`
-/
lemma SetTheory.Set.nonempty_def {X : Set} (h : X ≠ ∅) : ∃ x, x ∈ X := by
  by_contra! this
  have claim (x : Object) : x ∈ X ↔ x ∈ (∅ : Set) := by simp [this, not_mem_empty]
  apply ext at claim
  contradiction

theorem SetTheory.Set.nonemtpy_of_inhabited {X : Set} {x : Object} (h : x ∈ X) : X ≠ ∅ := by
  contrapose! h
  rw [eq_empty_iff_forall_notMem] at h
  exact h x

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := singleton

example (x : Object) : {x} = SetTheory.singleton x := rfl

/--
公理 3.3 单元素集

如果`a`是一个对象, 那么存在一个集合`{a}`并且该集合中的唯一的一个元素就是`a`.
也就是说, 对于任意一个对象`y`, 我们有`y ∈ {a}`当且仅当`y = a`; 我们称`{a}`是元素为`a`的单元素集.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a : Object) : x ∈ ({a} : Set) ↔ x = a := singleton_axiom x a

instance SetTheory.Set.instUnion : Union Set where
  union := union_pair

example (X Y : Set) : X ∪ Y = SetTheory.union_pair X Y := rfl

/--
公理 3.4 两集合之并

给定任意两个集合`A`和`B`, 存在一个集合`A ∪ B`被称为`A`和`B`的并集, 该集合的元素由属于`A`的或者属于`B`的或者同时属于`A`和`B`的所有元素共同构成.
换言之, 对任意的对象`x`, `x ∈ A ∪ B ↔ (x ∈ A ∨ x ∈ B)`
-/
@[simp]
theorem SetTheory.Set.mem_union (x : Object) (X Y : Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

@[simp]
theorem SetTheory.Set.mem_insert (a b : Object) (X : Set) : a ∈ insert b X ↔ a = b ∨ a ∈ X := by
  simp only [Insert.insert, mem_union, mem_singleton]

/--
公理 3.3 双元素集

如果`a`和`b`都是对象, 那么存在一个集合`{a, b}`, 并且该集合的元素只有`a`和`b`.
换言之, 对任意一个对象`y`, 有`y ∈ {a, b}`当且仅当`y = a`或`y = b`; 我们称该集合是由`a`和`b`构成的双元素集.
-/
theorem SetTheory.Set.pair_eq (a b : Object) : ({a, b} : Set) = {a} ∪ {b} := by rfl

@[simp]
theorem SetTheory.Set.mem_pair (x a b : Object) : x ∈ ({a, b} : Set) ↔ (x = a ∨ x = b) := by
  simp only [pair_eq, mem_union, mem_singleton]

@[simp]
theorem SetTheory.Set.mem_triple (x a b c : Object) : x ∈ ({a, b, c} : Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  simp only [Insert.insert, mem_union, mem_singleton]

/--
注 3.1.9
-/
theorem SetTheory.Set.singleton_uniq (a : Object) : ∃! (X : Set), ∀ x, x ∈ X ↔ x = a := by
  use {a}; simp
  intro _ hy
  ext x; simp
  exact hy x

/--
注 3.1.9
-/
theorem SetTheory.Set.pair_uniq (a b : Object) : ∃! (X : Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by
  use {a, b}; simp
  intro _ hy
  ext x; simp
  exact hy x

/--
注 3.1.9
-/
theorem SetTheory.Set.pair_comm (a b : Object) : ({a, b} : Set) = {b, a} := by
  ext x; simp
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

/--
注 3.1.9
-/
theorem SetTheory.Set.pair_self (a : Object) : ({a, a} : Set) = {a} := by ext x; simp

theorem SetTheory.Set.pair_eq_pair {a b c d : Object} (h : ({a, b} : Set) = {c, d}) :
    a = c ∧ b = d ∨ a = d ∧ b = c := by
  have ha : a ∈ ({c, d} : Set) := by
    rw [← h]; simp
  simp at ha
  have hb : b ∈ ({c, d} : Set) := by
    rw [← h]; simp
  simp at hb
  rcases ha with (ha | ha)
  · left
    rcases hb with (hb | hb)
    · have : c = d := by
        rw [ha, hb] at h
        have : d ∈ ({c, c} : Set) := by
          rw [h]; simp
        simp at this
        rw [this]
      rw [this, ha, hb]
      exact ⟨this, this⟩
    · exact ⟨ha, hb⟩
  · right
    rcases hb with (hb | hb)
    · exact ⟨ha, hb⟩
    · have : c = d := by
        rw [ha, hb] at h
        have : c ∈ ({d, d} : Set) := by
          rw [h]; simp
        simp at this
        assumption
      rw [this, ha, hb]; simp

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {(empty : Object)}
abbrev SetTheory.Set.pair_empty : Set := {(empty : Object), (singleton_empty : Object)}

/--
习题 3.1.2

只利用定义 3.1.4, 公理 3.1 - 3.3 证明集合`∅, {∅}, {∅, {∅}}`是互不相等的集合(即任意两个集合彼此互不相等).
-/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  by_contra h
  have : (empty : Object) ∈ singleton_empty := by simp
  rw [← h] at this
  absurd this; simp

theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by
  by_contra h
  have : (empty : Object) ∈ pair_empty := by simp
  rw [← h] at this
  absurd this; simp

theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  by_contra h
  have : (singleton_empty : Object) ∈ pair_empty := by simp
  simp [← h] at this
  have := emptyset_neq_singleton.symm
  contradiction

/--
注 3.1.12
-/
theorem SetTheory.Set.union_congr_left (A A' B : Set) (h : A = A') : A ∪ B = A' ∪ B := by rw[h]
theorem SetTheory.Set.union_congr_right (A B B' : Set) (h : B = B') : A ∪ B = A ∪ B' := by rw[h]

/--
引理 3.1.13

如果`a`和`b`都是对象, 那么`{a, b} = {a} ∪ {b}`.
如果`A, B, C`都是集合, 那么求并运算是可交换的(即`A ∪ B = B ∪ A`), 而且也是可结合的(即`(A ∪ B) ∪ C = A ∪ (B ∪ C)`).
另外, 我们有`A ∪ A = A ∪ ∅ = ∅ ∪ A = A`.
-/
theorem SetTheory.Set.singleton_union_singleton (a b : Object) :
    ({a} : Set) ∪ ({b} : Set) = {a, b} := by
  rfl

theorem SetTheory.Set.union_comm (A B : Set) : A ∪ B = B ∪ A := by
  ext x; simp
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

theorem SetTheory.Set.union_assoc (A B C : Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  constructor
  · intro hx; rw [mem_union] at hx
    obtain case1 | case2 := hx
    · rw [mem_union] at case1
      obtain case1a | case1b := case1
      · rw [mem_union]; tauto
      have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    have : x ∈ B ∪ C := by rw [mem_union]; tauto
    rw [mem_union]; tauto
  · intro hx; rw [mem_union] at hx
    obtain case1 | case2 := hx
    · rw [mem_union, mem_union]; tauto
    rw [mem_union] at case2
    obtain case2a | case2b := case2
    · rw [mem_union, mem_union]; tauto
    rw [mem_union, mem_union]; tauto

@[simp]
theorem SetTheory.Set.union_self (A : Set) : A ∪ A = A := by ext x; simp

@[simp]
theorem SetTheory.Set.union_empty (A : Set) : A ∪ ∅ = A := by ext x; simp

@[simp]
theorem SetTheory.Set.empty_union (A : Set) : ∅ ∪ A = A := by ext x; simp

theorem SetTheory.Set.triple_eq (a b c : Object) : {a, b, c} = ({a} : Set) ∪ {b, c} := by rfl

/--
例 3.1.11
-/
theorem SetTheory.Set.pair_union_pair (a b c : Object) : ({a, b} : Set) ∪ {b, c} = {a, b, c} := by
  ext; simp only [mem_union, mem_pair, mem_triple]; tauto

/--
定义 3.1.15 子集

设`A`和`B`都是集合, 我们称`A`是`B`的子集, 并记作`A ⊆ B`, 当且仅当`A`的每一个元素都是`B`中的元素,即
`∀ x, x ∈ A → x ∈ B`
如果`A ⊆ B`并且`A ≠ B`, 那么我们称`A`是`B`的真子集, 记作`A ⊂ B`.
-/
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

example (X Y : Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

example (X Y : Set) : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y := by rfl

theorem SetTheory.Set.subset_def (X Y : Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl
theorem SetTheory.Set.ssubset_def (X Y : Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/--
注 3.1.16
-/
theorem SetTheory.Set.subset_congr_left {A A' B : Set} (hAA' : A = A') (hAB : A ⊆ B) : A' ⊆ B := by rwa [hAA'] at hAB

@[simp, refl]
theorem SetTheory.Set.subset_self (A : Set) : A ⊆ A := by rw [subset_def]; intro _ _; assumption

@[simp]
theorem SetTheory.Set.empty_subset (A : Set) : ∅ ⊆ A := by rw [subset_def]; intro _ h; absurd h; simp

/--
命题 3.1.18 集合的包含关系使集合是偏序的

设`A, B, C`是集合. 如果`A ⊆ B`并且`B ⊆ C`, 那么`A ⊆ C`.
如果`A ⊆ B`并且`B ⊆ A`, 那么`A = B`.
最后, 如果`A ⊂ B`并且`B ⊂ C`, 那么`A ⊂ C`.
-/
theorem SetTheory.Set.subset_trans {A B C : Set} (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  apply hAB x at hx
  apply hBC x at hx
  assumption

theorem SetTheory.Set.subset_antisymm (A B : Set) (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  ext x
  constructor
  · intro hxA
    apply hAB x at hxA
    assumption
  · intro hxB
    apply hBA x at hxB
    assumption

theorem SetTheory.Set.ssubset_trans {A B C : Set} (hAB : A ⊂ B) (hBC : B ⊂ C) : A ⊂ C := by
  rw [ssubset_def]
  obtain ⟨hAB1, _⟩ := hAB
  obtain ⟨hBC1, _⟩ := hBC
  constructor
  · exact subset_trans hAB1 hBC1
  · by_contra h
    rw [h] at hAB1
    have := subset_antisymm _ _ hBC1 hAB1
    contradiction

abbrev SetTheory.Set.toSubtype (A : Set) := Subtype (fun x ↦ x ∈ A)

example (A : Set) (x : Object) (hx : x ∈ A) : A.toSubtype := ⟨x, hx⟩
example (A : Set) (x' : A.toSubtype) : Object := x'.val
example (A : Set) (x' : A.toSubtype) : x'.val ∈ A := x'.property

example (A B : Set) (x : Object) (hx : x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B : Set) (x' : A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

instance : CoeSort (Set) (Type v) where
  coe A := A.toSubtype

example (A B : Set) (x' : A) : x'.val ∈ A ∪ B := by simp; left; exact x'.property


lemma SetTheory.Set.subset_property (A : Set) (x : A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A : Set) (x : A) : x.val = x := rfl
lemma SetTheory.Set.coe_inj (A : Set) (x y : A) : x.val = y.val ↔ x = y := Subtype.coe_inj

def SetTheory.Set.subtype_mk (A : Set) {x : Object} (hx : x ∈ A) : A := ⟨x, hx⟩

@[simp]
lemma SetTheory.Set.subtype_mk_coe {A : Set} {x : Object} (hx : x ∈ A) : A.subtype_mk hx = x := by rfl

abbrev SetTheory.Set.specify (A : Set) (P : A → Prop) : Set := SetTheory.specify A P

/--
公理 3.5 分离公理

设`A`是一个集合, 对任意的`x ∈ A`, 令`P(x)`表示关于`x`的一个性质(即`P(x)`要么是真命题, 要么是假命题).
那么存在一个集合, 记作`{x ∈ A : P(x)}`, 该集合恰好是由`A`中那些使得`P(x)`为真的元素`x`构成的. 换言之, 对任意的对象`y`,
`y ∈ {x ∈ A : P(x)} ↔ (y ∈ A ∧ P(y))`
-/
theorem SetTheory.Set.specification_axiom {A : Set} {P : A → Prop} {x : Object} (h : x ∈ A.specify P) :
    x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

theorem SetTheory.Set.specification_axiom' {A : Set} (P : A → Prop) (x : A) :
    x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

@[simp]
theorem SetTheory.Set.specification_axiom'' {A : Set} (P : A → Prop) (x : Object) :
    x ∈ A.specify P ↔ ∃ h : x ∈ A, P ⟨x, h⟩ := by
  constructor
  · intro h; use specification_axiom h
    simp [← specification_axiom' P, h]
  intro ⟨h, hP⟩
  simpa [← specification_axiom' P] using hP

theorem SetTheory.Set.specify_subset {A : Set} (P : A → Prop) : A.specify P ⊆ A := by
  intro x hx
  simp at hx
  exact hx.1

theorem SetTheory.Set.specify_congr {A A' : Set} (hAA' : A = A') {P : A → Prop} {P' : A' → Prop}
  (hPP' : (x : Object) → (h : x ∈ A) → (h' : x ∈ A') → P ⟨x, h⟩ ↔ P' ⟨x, h'⟩) :
    A.specify P = A'.specify P' := by
  ext x; simp
  constructor
  · rintro ⟨h, Pxh⟩
    have h' : x ∈ A' := by rwa [hAA'] at h
    use h'
    exact (hPP' x h h').mp Pxh
  · rintro ⟨h', P'xh'⟩
    have h : x ∈ A := by rwa [← hAA'] at h'
    use h
    exact (hPP' x h h').mpr P'xh'

instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

example (X Y : Set) : X ∩ Y = X.specify (fun x ↦ x.val ∈ Y) := rfl

/--
定义 3.1.23 交集

两个集合的交集`S₁ ∩ S₂`被定义为下面这样一个集合
`S₁ ∩ S₂ := {x ∈ S₁ : x ∈ S₂}`
即`S₁ ∩ S₂`是由所有同时属于`S₁`和`S₂`的元素构成的。于是对任意的对象`x`，
`x ∈ S₁ ∩ S₂ ↔ x ∈ S₁ ∧ x ∈ S₂`
-/
@[simp]
theorem SetTheory.Set.mem_inter (x : Object) (X Y : Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  · intro h; have h' := specification_axiom h; simp [h']
    exact (specification_axiom' _ ⟨x, h'⟩).mp h
  intro ⟨hX, hY⟩; exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨x, hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

example (X Y : Set) : X \ Y = X.specify (fun x ↦ x.val ∉ Y) := rfl

/--
定义 3.1.27 差集

给定两个集合`A`和`B`，我们定义集合`A - B`或`A \ B`是由`A`中所有不属于`B`的元素组成的集合。
`A \ B := {x ∈ A : x ∉ B}`
在很多情况下，`B`是`A`的一个子集，但并非必须如此。
-/
@[simp]
theorem SetTheory.Set.mem_sdiff (x : Object) (X Y : Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  · intro h; have h' := specification_axiom h; simp [h']
    exact (specification_axiom' _ ⟨x, h'⟩).mp h
  intro ⟨hX, hY⟩; exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨x, hX⟩).mpr hY

/--
命题 3.1.27 (d) 交换律
-/
theorem SetTheory.Set.inter_comm (A B : Set) : A ∩ B = B ∩ A := by
  ext; simp
  exact ⟨fun ⟨x, y⟩ ↦ ⟨y, x⟩, fun ⟨x, y⟩ ↦ ⟨y, x⟩⟩

/--
命题 3.1.27 (b) 最大元
-/
theorem SetTheory.Set.subset_union {A X : Set} (hAx : A ⊆ X) : A ∪ X = X := by
  ext; simp
  exact fun x ↦ hAx _ x

/--
命题 3.1.27 (b) 最大元
-/
theorem SetTheory.Set.union_subset {A X : Set} (hAx : A ⊆ X) : X ∪ A = X := by
  ext; simp
  exact fun x ↦ hAx _ x

/--
命题 3.1.27 (c) 幂等律
-/
@[simp]
theorem SetTheory.Set.inter_self (A : Set) : A ∩ A = A := by ext; simp

/--
命题 3.1.27 (e) 结合律
-/
theorem SetTheroy.Set.inter_assoc (A B C : Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext; simp
  exact ⟨fun ⟨⟨x, y⟩, z⟩ ↦ ⟨x, ⟨y, z⟩⟩, fun ⟨x, ⟨y, z⟩⟩ ↦ ⟨⟨x, y⟩, z⟩⟩

/--
命题 3.1.27 (f) 分配律
-/
theorem SetTheory.Set.inter_union_distrib_left (A B C : Set) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext; simp
  constructor
  · rintro ⟨h1, h2 | h2⟩
    exact Or.inl ⟨h1, h2⟩
    exact Or.inr ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    exact ⟨h1, Or.inl h2⟩
    exact ⟨h1, Or.inr h2⟩

/--
命题 3.1.27 (f) 分配律
-/
theorem SetTheory.Set.union_inter_distrib_left (A B C : Set) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext; simp
  constructor
  · rintro (h1 | ⟨h2, h3⟩)
    exact ⟨Or.inl h1, Or.inl h1⟩
    exact ⟨Or.inr h2, Or.inr h3⟩
  · rintro ⟨h1 | h1, h2 | h2⟩
    exact Or.inl h1
    exact Or.inl h1
    exact Or.inl h2
    exact Or.inr ⟨h1, h2⟩

/--
命题 3.1.27 (g) 拆分法
-/
theorem SetTheory.Set.union_compl {A X : Set} (hAX : A ⊆ X) : A ∪ (X \ A) = X := by
  ext x; simp
  constructor
  · rintro (h | ⟨_, _⟩)
    exact hAX _ h
    assumption
  · intro h
    by_cases hA : x ∈ A
    exact Or.inl hA
    exact Or.inr ⟨h, hA⟩

/--
命题 3.1.27 (g) 拆分法
-/
theorem SetTheory.Set.inter_compl {A X : Set} : A ∩ (X \ A) = ∅ := by
  ext; simp
  exact fun x _ ↦ x

/--
命题 3.1.27 (h) 德·摩根定律
-/
theorem SetTheory.Set.compl_union {A B X : Set} : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  ext; simp
  exact ⟨fun ⟨x, y, z⟩ ↦ ⟨⟨x, y⟩, x, z⟩, fun ⟨⟨_, x⟩, y, z⟩ ↦ ⟨y, x, z⟩⟩

theorem SetTheory.Set.compl_inter {A B X : Set} : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  ext x; simp
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : x ∈ A
    exact Or.inr ⟨h1, h2 h⟩
    exact Or.inl ⟨h1, h⟩
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp [h1, h2]

instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by intro _ _ _; simp; exact Or.inl
  le_sup_right := by intro _ _ _; simp; exact Or.inr
  sup_le := by
    intro _ _ _ hac hbc _; simp
    rintro (hxa | hxa)
    exact hac _ hxa
    exact hbc _ hxa
  inf_le_left := by intro _ _ _; simp; exact fun x _ ↦ x
  inf_le_right := by intro _ _ _; simp
  le_inf := by
    intro _ _ _ hac hbc _; simp;
    exact fun x ↦ ⟨hac _ x, hbc _ x⟩
  le_sup_inf := by
    intro X Y Z; change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [← union_inter_distrib_left]

instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

example (A B : Set) : (A ≤ B) ↔ (A ⊆ B) := by rfl
example : ⊥ = (∅ : Set) := by rfl
example (A B : Set) : Prop := Disjoint A B

theorem SetTheory.Set.disjoint_iff (A B : Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A : Set) {P : A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/--
公理 3.6 替代公理

设`A`是一个集合，对任意的`x ∈ A`和任意的一个对象`y`，
假设存在一个关于`x`和`y`的命题`P(x, y)`使得对任意的`x ∈ A`，最多能够找到一个`y`使得`P(x, y)`为真。
那么存在一个集合`{y : ∃ x ∈ A, P(x, y)}`使得对任意的对象`z`
`z ∈ {y : ∃ x ∈ A, P(x, y)} ↔ ∃ x ∈ A, P(x, z)`
-/
@[simp]
theorem SetTheory.Set.replacement_axiom {A : Set} {P : A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') (y : Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

example (x : Nat) : Nat.toSubtype := x
example (x : Nat) : Object := x.val
example (x : Nat) : (x.val ∈ Nat) := x.property
example (o : Object) (ho : o ∈ Nat) : Nat := ⟨o, ho⟩

/--
公理 3.7 无穷公理

存在一个集合`ℕ`，它的元素被称为自然数。
对象`0`在`ℕ`中，且由每一个自然数`n ∈ ℕ`所指定的满足皮亚诺公理（公理2.1 ~ 2.5）的对象`n++`也在`ℕ`中。
-/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

instance SetTheory.Set.instOfNat {n : ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

example : Nat := 5
example : (5 : Nat).val ∈ Nat := (5 : Nat).property

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

example (n : ℕ) : Nat := n
example (n : ℕ) : (n : Nat).val ∈ Nat := (n : Nat).property

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

example (n : Nat) : ℕ := n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n : Nat).val

example (n : ℕ) : Object := n
example (n : ℕ) : Set := {(n : Object)}

instance SetTheory.Object.instOfNat {n : ℕ} : OfNat Object n where
  ofNat := ((n : Nat) : Object)

example : Object := 1
example : Set := {1, 2, 3}

@[simp]
lemma SetTheory.Object.ofnat_eq {n : ℕ} : ((n : Nat) : Object) = (n : Object) := rfl
lemma SetTheory.Object.ofnat_eq' {n : ℕ} : (ofNat(n) : Object) = (n : Object) := rfl
@[simp]
lemma SetTheory.Object.ofnat_eq'' {n : Nat} : ((n : ℕ) : Object) = (n : Object) := by
  simp only [Nat.cast, NatCast.natCast, Equiv.apply_symm_apply]
@[simp]
lemma SetTheory.Object.ofnat_eq''' {n : ℕ} {hn} : ((⟨(n : Object), hn⟩ : nat) : ℕ) = n := by
  simp only [Nat.cast, NatCast.natCast, Subtype.coe_eta, Equiv.symm_apply_apply]

lemma SetTheory.Set.nat_coe_eq {n : ℕ} : (n : Nat) = ofNat(n) := rfl
@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m : ℕ) : (n : Nat) = (m : Nat) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv
@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m : Nat) : (n : ℕ) = (m : ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m : ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
  convert nat_equiv_inj _ _

example : (5 : Nat) ≠ (3 : Nat) := by simp

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m : ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
  simp only [← Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
  rfl

example : (5 : Object) ≠ (3 : Object) := by simp

@[simp]
theorem SetTheory.Set.nat_coe_eq_iff {m n : ℕ} : (m : Object) = ofNat(n) ↔ m = n := by
  exact ofNat_inj' m n

example (n : ℕ) : (n : Object) = 2 ↔ n = 2 := by simp

@[simp]
theorem SetTheory.Object.natCast_inj (n m : ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
  simp only [← ofnat_eq, Subtype.val_inj, nat_equiv_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n : ℕ) : ((n : Nat) : ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n
@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n : Nat) : ((n : ℕ) : Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n
@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe'' (n : ℕ) : ((ofNat(n) : Nat) : ℕ) = n :=
  nat_equiv_coe_of_coe n
@[simp]
lemma SetTheory.Set.nat_coe_eq_iff' {m : Nat} {n : ℕ} : (m : Object) = (ofNat(n) : Object) ↔ (m : ℕ) = ofNat(n) := by
  constructor <;> intro h <;> rw [show m = n by aesop]
  apply nat_equiv_coe_of_coe; rfl

example : ({3, 5} : Set) ⊆ {1, 3, 5} := by
  simp only [subset_def, mem_pair, mem_triple]; tauto
example : ({3, 5} : Set).specify (fun x ↦ x.val ≠ 3) = ({5} : Set) := by
  ext
  simp only [mem_singleton, specification_axiom'']
  constructor
  · intro ⟨h1, h2⟩; simp only [mem_pair] at h1; tauto
  rintro rfl; norm_num
example : ({1, 2, 4} : Set) ∩ {2, 3, 4} = {2, 4} := by aesop
example : ({1, 2} : Set) ∩ {3, 4} = ∅ := by aesop
example : ¬ Disjoint ({1, 2, 3} : Set) {2, 3, 4} := by
  rw [disjoint_iff]
  intro h
  change {1, 2, 3} ∩ {2, 3, 4} = ∅ at h
  rw [eq_empty_iff_forall_notMem] at h
  aesop
example : Disjoint (∅ : Set) ∅ := by aesop
example : ({1, 2, 3, 4} : Set) \ {2, 4, 6} = {1, 3} := by aesop
example : ({3, 5, 9} : Set).replace (P := fun x y ↦ ∃ (n : ℕ), x.val = n ∧ y = (n + 1 : ℕ)) (by aesop)
    = {4, 6, 10} := by
  ext; simp only [replacement_axiom]
  constructor
  · rintro ⟨x, n, h1, h2⟩; aesop
  · aesop
example : ({3, 5, 9} : Set).replace (P := fun _ y ↦ y = 1) (by aesop) = {1} := by
  ext; simp only [replacement_axiom]; aesop

end Chapter3
