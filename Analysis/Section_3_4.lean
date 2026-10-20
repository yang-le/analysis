import Mathlib.Tactic
import Analysis.Section_3_1

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/--
定义 3.4.1 集合的象

如果`f : X → Y`是从`X`到`Y`的函数，并且`S`是`X`的一个子集，我们把`f(S)`定义为集合
`f(S) := {f(x) : x ∈ S}`
该集合是`Y`的一个子集，并且被称为`S`在映射`f`下的象
-/
abbrev SetTheory.Set.image {X Y : Set} (f : X → Y) (S : Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp)

theorem SetTheory.Set.mem_image {X Y : Set} (f : X → Y) (S : Set) (y : Object) :
    y ∈ image f S ↔ ∃ x : X, x.val ∈ S ∧ f x = y := by
  grind [replacement_axiom]

theorem SetTheory.Set.image_eq_sepcify {X Y : Set} (f : X → Y) (S : Set) :
    image f S = Y.specify (fun y ↦ ∃ x : X, x.val ∈ S ∧ f x = y) := by
  ext x; rw [mem_image]
  grind [specification_axiom'']

theorem SetTheory.Set.image_eq_image {X Y : Set} (f : X → Y) (S : Set) :
    (image f S : _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext; simp; grind

theorem SetTheory.Set.image_in_codomain {X Y : Set} (f : X → Y) (S : Set) :
    image f S ⊆ Y := by intro _ h; rw [mem_image] at h; grind

/--
例 3.4.2
-/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2 * n : ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1, 2, 3} = {2, 4, 6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals simp_all

/--
例 3.4.3
-/
example : (fun n : ℤ ↦ n ^ 2) '' {-1, 0, 1, 2} = {0, 1, 4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y : Set} (f : X → Y) (S : Set) (x : X) :
    x.val ∈ S → (f x).val ∈ image f S := by
  intro h; simp
  use x.val
  constructor
  · use x.property
  · assumption

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y : Set) (f : X → Y) (S : Set) (x : X), ¬ ((f x).val ∈ image f S → x.val ∈ S) := by
  use Nat, Nat, fun x ↦ 1, {1}, 2
  push Not
  constructor
  · rw [mem_image]; use 1; simp
  · simp

/--
定义 3.4.4 逆象

如果`U`是`Y`的一个子集，我们定义集合`f⁻¹(U)`为`f⁻¹(U) := {x ∈ X : f(x) ∈ U}`
换言之，`f⁻¹(U)`是由`X`中所有被映射到`U`中的元素构成的：`f(x) ∈ U ↔ x ∈ f⁻¹(U)`
我们称`f⁻¹(U)`为`U`的逆象。
-/
abbrev SetTheory.Set.preimage {X Y : Set} (f : X → Y) (U : Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y : Set} (f : X → Y) (U : Set) (x : X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

theorem SetTheory.Set.mem_preimage' {X Y : Set} (f : X → Y) (U : Set) (x : Object) :
    x ∈ preimage f U ↔ ∃ x' : X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  · intro h; by_cases hx : x ∈ X
    · use ⟨x, hx⟩; have := mem_preimage f U ⟨_, hx⟩; simp_all
    · grind [specification_axiom]
  · rintro ⟨x', rfl, hfx'⟩; rwa [mem_preimage]

theorem SetTheory.Set.preimage_eq {X Y : Set} (f : X → Y) (U : Set) :
    ((preimage f U) : _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y : Set} (f : X → Y) (U : Set) :
    (preimage f U) ⊆ X := by intro _ _; aesop

/--
例 3.4.5
-/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2, 4, 6} = {1, 2, 3} := by
  ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl); map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1, 2, 3}) ≠ {1, 2, 3} := by
  by_contra h
  rw [SetTheory.Set.ext_iff] at h
  have := (h 1).mpr (by simp)
  simp only [mem_image, mem_preimage, mem_triple, f_3_4_2] at this
  obtain ⟨_, ⟨_, h2⟩⟩ := this
  simp at h2

/--
例 3.4.6
-/
example : (fun n : ℤ ↦ n ^ 2)⁻¹' {0, 1, 4} = {-2, -1, 0, 1, 2} := by
  ext; refine ⟨?_, by aesop⟩; rintro (_ | _ | h)
  on_goal 3 => have : 2 ^ 2 = (4 : ℤ) := (by norm_num); rw [← h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n : ℤ ↦ n ^ 2)⁻¹' ((fun n : ℤ ↦ n ^ 2) '' {-1, 0, 1, 2}) ≠ {-1, 0, 1, 2} := by
  simp
  by_contra h
  have : (fun n : ℤ ↦ n ^ 2)⁻¹' {0, 1, 4} = {-2, -1, 0, 1, 2} := by
    ext; refine ⟨?_, by grind⟩; rintro (_ | _ | h)
    on_goal 3 => have : 2 ^ 2 = (4 : ℤ) := (by norm_num); rw [← h, sq_eq_sq_iff_eq_or_eq_neg] at this
    all_goals aesop
  rw [this] at h
  aesop

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y : Set} (f : X → Y) : Object := function_to_object X Y f

instance SetTheory.Set.inst_coe_of_fun {X Y : Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y : Set} (f g : X → Y) : (f : Object) = (g : Object) ↔ f = g := by
  simp [coe_of_fun]

/--
公理 3.10 幂集公理

设`X`和`Y`都是集合，那么存在一个集合记作`Y ^ X`，该集合是由从`X`到`Y`的全体函数构成的。于是
`f ∈ Y ^ X ↔ f : X → Y`
-/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y : Set} (F : Object) :
    F ∈ (Y ^ X) ↔ ∃ f : X → Y, f = F := SetTheory.powerset_axiom Y X F

/--
例 3.4.8
-/
abbrev f_3_4_9_a : ({4, 7} : Set) → ({0, 1} : Set) := fun x ↦ ⟨0, by simp⟩
open Classical in
noncomputable abbrev f_3_4_9_b : ({4, 7} : Set) → ({0, 1} : Set) :=
  fun x ↦ if x.val = 4 then ⟨0, by simp⟩ else ⟨1, by simp⟩
open Classical in
noncomputable abbrev f_3_4_9_c : ({4, 7} : Set) → ({0, 1} : Set) :=
  fun x ↦ if x.val = 4 then ⟨1, by simp⟩ else ⟨0, by simp⟩
abbrev f_3_4_9_d : ({4, 7} : Set) → ({0, 1} : Set) := fun x ↦ ⟨1, by simp⟩

theorem SetTheory.Set.example_3_4_9 (F : Object) :
    F ∈ ({0, 1} : Set) ^ ({4, 7} : Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right; left); (right; right; left); (right; right; right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

/--
引理 3.4.9

设`X`是一个集合，那么`{Y : Y ⊆ X}`是一个集合
-/
def SetTheory.Set.powerset (X : Set) : Set :=
  (({0, 1} ^ X) : Set).replace (P := fun x y ↦ ∃ f : X → ({0, 1} : Set), f = x.val ∧ y = preimage f {1}) (by simp)

open Classical in
@[simp]
theorem SetTheory.Set.mem_powerset {X : Set} (x : Object) :
    x ∈ powerset X ↔ ∃ Y : Set, x = Y ∧ Y ⊆ X := by
  constructor
  · intro h
    rw [powerset, replacement_axiom] at h
    obtain ⟨_, ⟨f, hf⟩⟩ := h
    use preimage f {1}
    exact ⟨hf.2, preimage_in_domain _ _⟩
  · rintro ⟨Y, ⟨h1, h2⟩⟩
    rw [powerset, replacement_axiom]; simp
    use fun y ↦ if y.val ∈ Y then ⟨1, by simp⟩ else ⟨0, by simp⟩
    simp [preimage, h1]; ext y
    aesop
    -- constructor
    -- · intro hy
    --   rw [specification_axiom'']
    --   use h2 y hy
    --   simp [hy]
    -- · intro hy
    --   obtain ⟨_, h⟩ := (specification_axiom'' _ _).mp hy
    --   split at h
    --   · assumption
    --   · simp at h

theorem SetTheory.Set.exists_powerset (X : Set) :
    ∃ (Z : Set), ∀ x, x ∈ Z ↔ ∃ Y : Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/--
注 3.4.10
-/
theorem SetTheory.Set.powerset_of_triple (a b c x : Object) :
    x ∈ powerset {a, b, c}
    ↔ x = (∅ : Set)
    ∨ x = ({a} : Set)
    ∨ x = ({b} : Set)
    ∨ x = ({c} : Set)
    ∨ x = ({a, b} : Set)
    ∨ x = ({a, c} : Set)
    ∨ x = ({b, c} : Set)
    ∨ x = ({a, b, c} : Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨?_, by aesop⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/--
公理 3.11 并集

设`A`是一个集合，并且`A`中的每一个元素本身也是一个集合。那么存在一个集合`∪A`，它的元素恰好是`A`的元素的元素。于是对任意的对象`x`,
`x ∈ ⋃A ↔ ∃ S ∈ A, x ∈ S`
-/
theorem SetTheory.Set.union_axiom (A : Set) (x : Object) :
    x ∈ union A ↔ ∃ (S : Set), x ∈ S ∧ (S : Object) ∈ A := SetTheory.union_axiom A x

/--
例 3.4.11
-/
theorem SetTheory.Set.example_3_4_12 :
    union {(({2, 3} : Set) : Object), (({3, 4} : Set) : Object), (({4, 5} : Set) : Object)} = {2, 3, 4, 5} := by
  ext x
  rw [union_axiom]
  refine ⟨?_, by aesop⟩
  rintro ⟨S, ⟨xS, h⟩⟩
  simp at h; simp
  obtain (h | h | h) := h <;> subst h <;>
  simp at xS <;> obtain (xS | xS) := xS
  on_goal 1 => left
  on_goal 2 => right; left
  on_goal 3 => right; left
  on_goal 4 => right; right; left
  on_goal 5 => right; right; left
  on_goal 6 => right; right; right
  all_goals assumption

theorem SetTheory.Set.union_eq (A : Set) :
    (union A : _root_.Set Object) =
    ⋃₀ {S : _root_.Set Object | ∃ S' : Set, S = S' ∧ (S' : Object) ∈ A} := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

abbrev SetTheory.Set.iUnion (I : Set) (A : I → Set) : Set :=
  union (I.replace (P := fun a S ↦ S = A a) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

theorem SetTheory.Set.mem_iUnion {I : Set} (A : I → Set) (x : Object) :
    x ∈ iUnion I A ↔ ∃ a : I, x ∈ A a := by
  rw [union_axiom]; constructor
  · simp_all [replacement_axiom]
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1, 2, 3} : Set) → Set :=
  fun i ↦ if i.val = 1 then {2, 3} else if i.val = 2 then {3, 4} else {4, 5}

theorem SetTheory.Set.iUnion_example : iUnion {1, 2, 3} index_example = {2, 3, 4, 5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨by aesop, ?_⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

theorem SetTheory.Set.iUnion_eq (I : Set) (A : I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α : _root_.Set Object) := by
  ext; simp [mem_iUnion]

noncomputable abbrev SetTheory.Set.nonempty_choose {I : Set} (hI : I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I : Set) (β : I) (A : I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α : I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I : Set) (hI : I ≠ ∅) (A : I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I : Set} (hI : I ≠ ∅) (A : I → Set) (x : Object) :
    x ∈ iInter I hI A ↔ ∀ α : I, x ∈ A α := by
  constructor
  · simp [specification_axiom'']
  · intro h; simp
    exact ⟨h _, by intros; exact h _⟩

/--
习题 3.4.1
-/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V : Set} (f : X → Y) (f_inv : Y → X)
  (hf : Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV : V ⊆ Y) :
    image f_inv V = preimage f V := by
  ext x; constructor
  · intro h
    simp at h
    obtain ⟨a, ⟨aY, rfl⟩, _⟩ := h
    simp
    use (f_inv ⟨a, aY⟩).property
    rwa [hf.2]
  · intro h
    simp at h
    obtain ⟨xX, h⟩ := h
    simp
    use f ⟨x, xX⟩
    constructor
    · use hV _ h; rw [hf.1]
    · assumption

/--
习题 3.4.2
-/
theorem SetTheory.Set.preimage_of_image {X Y : Set} (f : X → Y) (S : Set) (hS : S ⊆ X) :
    S ⊆ preimage f (image f S) := by
  intro x xS; simp
  use hS _ xS
  use x; constructor
  · use hS _ xS
  · assumption

theorem SetTheory.Set.image_of_preimage {X Y : Set} (f : X → Y) (U : Set) :
    image f (preimage f U) ⊆ U := by
  intro _ h; simp at h
  obtain ⟨_, _, h1, _, h2⟩ := h
  rwa [h1] at h2

theorem SetTheory.Set.preimage_of_image_of_preimage {X Y : Set} (f : X → Y) (U : Set) :
    preimage f U = preimage f (image f (preimage f U)) := by
  ext x; constructor
  · intro h
    exact preimage_of_image _ _ (preimage_in_domain _ _) _ h
  · intro h
    simp at h
    obtain ⟨xX, _, _, h1, _, h2⟩ := h
    simp; use xX
    rwa [h1] at h2

theorem SetTheory.Set.image_of_preimage_of_image {X Y : Set} (f : X → Y) (S : Set) :
    image f S = image f (preimage f (image f S)) := by
  ext x; constructor
  · intro h
    simp at h
    obtain ⟨a, ⟨aX, _⟩, _⟩ := h
    simp; use a, aX; split_ands
    · assumption
    · assumption
    · use a; constructor
      · use aX
      · assumption
  · intro h
    exact image_of_preimage _ _ _ h

/--
习题 3.4.3
-/
theorem SetTheory.Set.image_of_inter {X Y : Set} (f : X → Y) (A B : Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
  intro x h
  simp at h; simp
  obtain ⟨a, ⟨aX, rfl⟩, aA, aB⟩ := h
  constructor <;>
  · use a; constructor
    · use aX
    · assumption

theorem SetTheory.Set.image_of_diff {X Y : Set} (f : X → Y) (A B : Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
  intro x h
  simp at h; simp
  obtain ⟨⟨a, ⟨aX, rfl⟩, aA⟩, h⟩ := h
  use a; constructor
  · use aX
  · exact ⟨aA, h _ aX rfl⟩

theorem SetTheory.Set.image_of_union {X Y : Set} (f : X → Y) (A B : Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
  ext x; simp; constructor
  · rintro ⟨a, ⟨aX, rfl⟩, (h | h)⟩
    · left; use a; constructor; use aX; assumption
    · right; use a; constructor; use aX; assumption
  · rintro (⟨a, ⟨aX, rfl⟩, aA⟩ | ⟨a, ⟨aX, rfl⟩, aB⟩)
    · use a; constructor; use aX; exact Or.inl aA
    · use a; constructor; use aX; exact Or.inr aB

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y : Set, ∀ f : X → Y, ∀ A B : Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  apply isFalse
  push Not
  use Nat, Nat, fun x ↦ 2, {0}, {1}
  by_contra h
  have : image (fun (x : Nat) ↦ (2 : Nat)) {0} ∩ image (fun (x : Nat) ↦ (2 : Nat)) {1} = {2} := by
    ext x; constructor
    · intro hx; aesop
    · intro h
      simp at h
      simp; constructor <;> constructor
      · exact h.symm
      · use (0 : Nat).val, (0 : Nat).property
        simp
      · exact h.symm
      · use (1 : Nat).val, (1 : Nat).property
        simp
  rw [this] at h
  have : image (fun (x : Nat) ↦ (2 : Nat)) (({0} : Set) ∩ ({1} : Set)) = ∅ := by
    rw [show ({0} : Set) ∩ ({1} : Set) = ∅ by aesop]; aesop
  rw [this] at h
  have : 2 ∈ (∅ : Set) := by rw [h]; simp
  simp at this

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y : Set, ∀ f : X → Y, ∀ A B : Set, image f (A \ B) = (image f A) \ (image f B)) := by
  apply isFalse
  push Not
  use Nat, Nat, fun x ↦ 2, {0, 1}, {1}
  by_contra h
  have : image (fun (x : Nat) ↦ (2 : Nat)) {0, 1} \ image (fun (x : Nat) ↦ (2 : Nat)) {1} = ∅ := by
    ext x; constructor <;> intro h <;> simp at h
    obtain ⟨⟨h1, _⟩, h2⟩ := h
    have := h2 h1 (1 : Nat).val (1 : Nat).property
    simp at this
  rw [this] at h
  have : image (fun (x : Nat) ↦ (2 : Nat)) ({0, 1} \ {1}) = {2} := by
    rw [show ({0, 1} : Set) \ {1} = {0} by aesop]
    ext x; constructor <;> intro h <;> simp at h
    · rw [h.1.symm]; simp
    · rw [h]; simp; use (0 : Nat).val, (0 : Nat).property; simp
  rw [this] at h
  have : 2 ∈ (∅ : Set) := by rw [← h]; simp
  simp at this

/--
习题 3.4.4
-/
theorem SetTheory.Set.preimage_of_inter {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
  ext x; constructor
  · intro h
    simp at h; simp
    obtain ⟨xX, _, _⟩ := h
    constructor
    · use xX
    · use xX
  · intro h
    simp at h; simp
    obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := h
    constructor
    · exact ⟨h1, h2⟩
    · assumption

theorem SetTheory.Set.preimage_of_union {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
  ext x; constructor
  · intro h
    simp at h; simp
    obtain ⟨xX, (h | h)⟩ := h
    · left; use xX
    · right; use xX
  · intro h
    simp at h; simp
    obtain (⟨xX, h⟩ | ⟨xX, h⟩) := h
    · use xX; left; assumption
    · use xX; right; assumption

theorem SetTheory.Set.preimage_of_diff {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B) := by
  ext x; constructor
  · intro h
    simp at h; simp
    obtain ⟨xX, h1, h2⟩ := h
    constructor
    · use xX
    · intro _; assumption
  · intro h
    simp at h; simp
    obtain ⟨⟨xX, h1⟩, h2⟩ := h
    use xX; constructor
    · assumption
    · exact h2 _

/--
习题 3.4.5
-/
theorem SetTheory.Set.image_preimage_of_surj {X Y : Set} (f : X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
  constructor
  · intro h y
    have : y.val ∈ image f (preimage f Y) := by aesop
    simp at this
    obtain ⟨x, xX, _, _, _⟩ := this
    use ⟨x, xX⟩; aesop
  · intro fSurj _ hS
    ext x; constructor
    · intro h
      exact image_of_preimage _ _ _ h
    · intro h; simp
      obtain ⟨a, ha⟩ := fSurj ⟨x, hS _ h⟩
      use a, a.property; aesop

theorem SetTheory.Set.preimage_image_of_inj {X Y : Set} (f : X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
  constructor
  · intro h x x' hf
    have : x.val ∈ preimage f (image f {x'.val}) := by aesop
    rw [h] at this
    aesop; intro y hy; simp at hy; rw [hy]; exact x'.property
  · intro fInj _ hS
    ext x; constructor
    · intro h; simp at h
      obtain ⟨xX, a, ⟨aX, hf⟩, aS⟩ := h
      have := fInj (show f ⟨a, aX⟩ = f ⟨x, xX⟩ by aesop)
      aesop
    · intro h
      exact preimage_of_image _ _ hS _ h

/--
习题 3.4.7
-/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S' : Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

theorem SetTheory.Set.partial_functions {X Y : Set} :
    ∃ Z : Set, ∀ F : Object, F ∈ Z ↔ ∃ X' Y' : Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f : X' → Y', F = f := by
  let U (x : X.powerset) := union (Y.powerset.replace (P :=
      fun y W ↦ ∃ X' Y' : Set, X' = x.val ∧ Y' = y.val ∧ W = pow Y' X') (by aesop))
  use union (X.powerset.replace (P := fun x W ↦ W = U x) (by aesop))
  intro F; constructor
  · intro hF
    rw [mem_union_powerset_replace_iff] at hF
    obtain ⟨X', _, _, hF⟩ := hF
    have hF : F ∈ U X' := by aesop
    rw [mem_union_powerset_replace_iff] at hF
    obtain ⟨Y', U', ⟨x, y, h1, h2, _⟩, h3⟩ := hF
    use x, y; split_ands
    · have : (x : Object) ∈ X.powerset := by
        rw [h1]; exact X'.property
      simp at this; assumption
    · have : (y : Object) ∈ Y.powerset := by
        rw [h2]; exact Y'.property
      simp at this; assumption
    · rw [show U' = y ^ x by aesop] at h3
      simp at h3
      obtain ⟨f, hf⟩ := h3
      use f; exact hf.symm
  · intro h
    obtain ⟨X', Y', h1, h2, ⟨f, h3⟩⟩ := h
    rw [mem_union_powerset_replace_iff]
    rw [← mem_powerset'] at h1 h2
    use ⟨X', h1⟩, U ⟨X', h1⟩
    simp; rw [mem_union_powerset_replace_iff]
    use ⟨Y', h2⟩, Y' ^ X'
    constructor
    · use X', Y'
      exact ⟨rfl, rfl, by aesop⟩
    · rw [powerset_axiom, h3]
      use f

/--
习题 3.4.8

仅可使用公理3.1, 3.3和3.11
-/
theorem SetTheory.Set.union_pair_exists (X Y : Set) : ∃ Z : Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  use union {(X : Object), (Y : Object)}
  intro _
  rw [union_axiom]
  constructor
  · rintro ⟨S, _, hS⟩
    -- 虽然mem_pair的证明用到了公理3.4，但其结论实际上是课本上公理3.3的内容
    rw [mem_pair] at hS
    obtain (hS | hS) := hS
    left; rwa [show X = S by aesop]
    right; rwa [show Y = S by aesop]
  · rintro (h | h)
    use X; simpa
    use Y; simpa

/--
习题 3.4.9
-/
theorem SetTheory.Set.iInter'_insensitive {I : Set} (β β' : I) (A : I → Set) :
    iInter' I β A = iInter' I β' A := by
  ext x; constructor <;> intro _ <;> simp_all

/--
习题 3.4.10
-/
theorem SetTheory.Set.union_iUnion {I J : Set} (A : (I ∪ J : Set) → Set) :
    iUnion I (fun α ↦ A ⟨α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by
  ext; constructor
  · intro h
    rw [mem_union] at h
    simp [mem_iUnion] at h
    simp [mem_iUnion]
    aesop
  · intro h
    rw [mem_union]
    simp [mem_iUnion] at h
    simp [mem_iUnion]
    aesop

theorem SetTheory.Set.union_of_nonempty {I J : Set} (hI : I ≠ ∅) (_hJ : J ≠ ∅) : I ∪ J ≠ ∅ := by
  by_contra h
  obtain ⟨x, hx⟩ := nonempty_def hI
  have : x ∈ I ∪ J := by simp [hx]
  rw [h] at this
  have := not_mem_empty x
  contradiction

theorem SetTheory.Set.inter_iInter {I J : Set} (hI : I ≠ ∅) (hJ : J ≠ ∅) (A : (I ∪ J : Set) → Set) :
    iInter I hI (fun α ↦ A ⟨α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
  ext; constructor
  · intro h
    rw [mem_inter] at h
    simp only [mem_iInter] at h
    simp only [mem_iInter]
    intro α
    obtain ⟨h1, h2⟩ := h
    have := α.property
    rw [mem_union] at this
    obtain (h | h) := this
    · exact h1 ⟨α, h⟩
    · exact h2 ⟨α, h⟩
  · intro h
    rw [mem_inter]
    simp only [mem_iInter] at h
    simp only [mem_iInter]
    constructor <;> intro α <;> exact h _

/--
习题 3.4.11
-/
theorem SetTheory.Set.compl_iUnion {X I : Set} (hI : I ≠ ∅) (A : I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
  ext x; constructor
  · intro h
    rw [mem_sdiff] at h
    rw [mem_iInter]
    intro α
    rw [mem_sdiff]
    obtain ⟨h1, h2⟩ := h
    constructor
    · assumption
    · by_contra h'
      have : x ∈ I.iUnion A := by
        rw [mem_iUnion]; use α
      contradiction
  · intro h
    rw [mem_iInter] at h
    rw [mem_sdiff]
    obtain ⟨α, hα⟩ := nonempty_def hI
    have h' := h ⟨α, hα⟩
    rw [mem_sdiff] at h'
    constructor
    · exact h'.1
    · by_contra h
      rw [mem_iUnion] at h
      obtain ⟨α, hα⟩ := h
      have := h α
      rw [mem_sdiff] at this
      have := this.2
      contradiction

theorem SetTheory.Set.compl_iInter {X I : Set} (hI : I ≠ ∅) (A : I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
  ext x; constructor
  · intro h
    rw [mem_sdiff] at h
    rw [mem_iUnion]
    obtain ⟨h1, h2⟩ := h
    by_contra h'
    simp_all
  · intro h
    rw [mem_iUnion] at h
    obtain ⟨α, hα⟩ := h
    rw [mem_sdiff] at hα
    obtain ⟨h1, h2⟩ := hα
    rw [mem_sdiff]
    constructor
    · assumption
    · by_contra h'
      rw [mem_iInter] at h'
      have := h' α
      contradiction

end Chapter3
