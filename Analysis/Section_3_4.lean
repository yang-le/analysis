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

end Chapter3
