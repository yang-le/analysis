import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Tools.ExistsUnique

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/--
定义 3.3.1 函数

设`X, Y`是集合。令`P(x, y)`表示关于对象`x ∈ X`和对象`y ∈ Y`的一个性质，
并且`P(x, y)`满足对于任意的`x ∈ X`，恰好存在一个`y ∈ Y`使得`P(x, y)`为真（有时这被称为垂线测试）。
-/
@[ext]
structure Function (X Y : Set) where
  P : X → Y → Prop
  unique : ∀ x : X, ∃! y : Y, P x y

#check Function.mk

noncomputable def Function.to_fn {X Y : Set} (f : Function X Y) : X → Y :=
  fun x ↦ (f.unique x).choose

noncomputable instance Function.inst_coefn (X Y : Set) : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := Function.to_fn

theorem Function.to_fn_eval {X Y : Set} (f : Function X Y) (x : X) : f.to_fn x = f x := rfl

abbrev Function.mk_fn {X Y : Set} (f : X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by simp)

/--
定义 3.3.1 函数

我们定义由`P`在定义域`X`和值域`Y`上确定的函数`f : X → Y`为下述事物。
对于给定的任意输入`x ∈ X`，`f`指定了一个输出`f(x) ∈ Y`与其对应，并且`f(x)`是使得`P(x, f(x))`为真的唯一一个对象。
因此，对任意的`x ∈ X`和`y ∈ Y`，
`y = f(x) ↔ P(x, y)`
-/
theorem Function.eval {X Y : Set} (f : Function X Y) (x : X) (y : Y) : y = f x ↔ f.P x y := by
  convert ((f.unique x).choose_iff y).symm; rfl

@[simp]
theorem Function.eval_of {X Y : Set} (f : X → Y) (x : X) : (Function.mk_fn f) x = f x := by
  symm; rw[eval]

end Chapter3
