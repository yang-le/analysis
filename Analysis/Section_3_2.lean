import Mathlib.Tactic
import Analysis.Section_3_1

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/--
公理 3.8 万有分类

假设对任意的对象`x`，存在关于`x`的性质`P(x)`（于是对每一个`x`，`P(x)`要么是真命题，要么是假命题。）
那么存在一个集合`{x : P(x)}`使得对任意对象`y`，`y ∈ {x : P(x)} ↔ P(y)`
-/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

/--
罗素悖论
-/
theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  intro h
  -- `x`是一个集合，并且`x ∉ x`
  set P : Object → Prop := fun x ↦ ∃ X : Set, x = X ∧ x ∉ X
  -- 根据公理3.8，我们就能构造这样一个集合`Ω := {x : P(x)}`
  -- 即由所有不包含自身的集合构成的集合
  choose Ω hΩ using h P
  -- 现在问一个问题：`Ω`是否包含自身？
  by_cases h : (Ω : Object) ∈ Ω
    -- 如果`Ω`包含自身，那么根据定义`P(Ω)`就为真
  · have : P (Ω : Object) := (hΩ _).mp h
    -- 即`Ω`是一个集合且`Ω ∉ Ω`，这与假设矛盾
    obtain ⟨Ω', ⟨hΩ1, hΩ2⟩⟩ := this
    simp at hΩ1
    rw [← hΩ1] at hΩ2
    contradiction
  -- 如果`Ω`不包含自身，那么`P(Ω)`为真
  have : P (Ω : Object) := by use Ω
  -- 因此`Ω ∈ Ω`，这又导致矛盾
  rw [← hΩ] at this
  contradiction

/--
公理 3.9 正则公理

如果`A`是一个非空集合，那么`A`中至少存在一个元素`x`满足：`x`要么不是集合，要么`x`与`A`不相交。
-/
theorem SetTheory.Set.axiom_of_regularity {A : Set} (h : A ≠ ∅) :
    ∃ x : A, ∀ S : Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
习题 3.2.1
-/
theorem SetTheory.Set.emptyset_exists (h : axiom_of_universal_specification) :
    ∃ (X : Set), ∀ x, x ∉ X := by
  set P : Object → Prop := fun _ ↦ false
  choose Ω hΩ using h P
  use Ω
  by_contra! h
  obtain ⟨x, hx⟩ := h
  rw [hΩ x] at hx
  aesop

theorem SetTheory.Set.singleton_exists (h : axiom_of_universal_specification) (x : Object) :
    ∃ (X : Set), ∀ y, y ∈ X ↔ y = x := by
  set P : Object → Prop := fun y ↦ y = x
  choose Ω hΩ using h P
  use Ω

theorem SetTheory.Set.pair_exists (h : axiom_of_universal_specification) (x₁ x₂ : Object) :
    ∃ (X : Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  obtain ⟨Ω, _⟩ := h (fun y ↦ y = x₁ ∨ y = x₂)
  use Ω

theorem SetTheory.Set.union_exists (h : axiom_of_universal_specification) (A B : Set) :
    ∃ (Z : Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  obtain ⟨Ω, _⟩ := h (fun y ↦ y ∈ A ∨ y ∈ B)
  use Ω

theorem SetTheory.Set.specify_exists (h : axiom_of_universal_specification) (A : Set) (P : A → Prop) :
    ∃ (Z : Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨z, h⟩ := by
  obtain ⟨Ω, _⟩ := h (fun y ↦ ∃ h : y ∈ A, P ⟨y, h⟩)
  use Ω

theorem SetTheory.Set.replace_exists (h : axiom_of_universal_specification) (A : Set)
  (P : A → Object → Prop) (_hP : ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z : Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  obtain ⟨Ω, _⟩ := h (fun y ↦ ∃ a : A, P a y)
  use Ω

/--
习题 3.2.2
-/
theorem SetTheory.Set.not_mem_self (A : Set) : (A : Object) ∉ A := by
  -- 考虑单元素集合`{A}`
  let A' : Set := {(A : Object)}
  have h : A' ≠ ∅ := by
    by_contra h
    have : (A : Object) ∈ A' := by rw [mem_singleton]
    aesop
  obtain ⟨x, hx⟩ := axiom_of_regularity (A := A') h
  have := hx A (show x = (A : Object) by aesop)
  rw [disjoint_iff] at this
  by_contra
  have : (A : Object) ∈ A ∩ A' := by simp; aesop
  aesop

theorem SetTheory.Set.not_mem_mem (A B : Set) : (A : Object) ∉ B ∨ (B : Object) ∉ A := by
  by_contra! ⟨h1, h2⟩
  -- 考虑集合`{A, B}`
  let C : Set := {(A : Object), (B : Object)}
  have h : C ≠ ∅ := by
    by_contra h
    have : (A : Object) ∈ C := by rw [mem_pair]; simp
    aesop
  obtain ⟨x, hx⟩ := axiom_of_regularity (A := C) h
  obtain (h | h) := (mem_pair _ _ _).mp x.property
  · have := hx A (show x = (A : Object) by aesop)
    rw [disjoint_iff] at this
    have : (B : Object) ∈ A ∩ C := by simp; aesop
    aesop
  · have := hx B (show x = (B : Object) by aesop)
    rw [disjoint_iff] at this
    have : (A : Object) ∈ B ∩ C := by simp; aesop
    aesop

/--
习题 3.2.3
-/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
    ∃ (U : Set), ∀ x, x ∈ U := by
  constructor
  · intro h
    obtain ⟨Ω, _⟩ := h (fun _ ↦ true)
    use Ω; aesop
  · rintro ⟨U, _⟩ P
    use U.specify (fun x ↦ P x)
    aesop

theorem SetTheory.Set.no_univ : ¬ ∃ (U : Set), ∀ (x : Object), x ∈ U := by
  rw [← univ_iff]
  exact Russells_paradox

theorem SetTheory.Set.no_univ' : ¬ ∃ (U : Set), ∀ (x : Object), x ∈ U := by
  by_contra ⟨U, hU⟩
  have := hU U
  have := not_mem_self U
  contradiction

end Chapter3
