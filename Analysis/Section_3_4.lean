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

end Chapter3
