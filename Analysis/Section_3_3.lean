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

/--
例 3.3.2
-/

-- 令`P(x, y)`表示性质`y = x++`
abbrev P_3_3_3a : Nat → Nat → Prop := fun x y ↦ (y : ℕ) = (x : ℕ) + 1

-- 对任意一个`x ∈ ℕ`，恰好存在一个`y`使得`P(x, y)`为真
theorem SetTheory.Set.P_3_3_3a_existsUnique (x : Nat) : ∃! y : Nat, P_3_3_3a x y := by
  apply ExistsUnique.intro ((x + 1 : ℕ) : Nat)
  · simp [P_3_3_3a]
  intro y h
  -- simpa [P_3_3_3a, Equiv.symm_apply_eq] using h
  refine (nat_equiv_symm_inj y ↑(nat_equiv.symm x + 1)).mp ?_
  simpa

-- 于是我们可以定义与该性质有关的一个函数`f : ℕ → ℕ`
abbrev SetTheory.Set.f_3_3_3a : Function Nat Nat := Function.mk P_3_3_3a P_3_3_3a_existsUnique

-- 使得对任意的`x`有`f(x) = x++`
theorem SetTheory.Set.f_3_3_3a_eval (x y : Nat) : y = f_3_3_3a x ↔ (y : ℕ) = (x + 1 : ℕ) :=
  Function.eval _ _ _

theorem SetTheory.Set.f_3_3_3a_eval' (n : ℕ) : f_3_3_3a (n : Nat) = (n + 1 : ℕ) := by
  symm
  simp only [f_3_3_3a_eval, nat_equiv_coe_of_coe]

theorem SetTheory.Set.f_3_3_3a_eval'' : f_3_3_3a 4 = 5 := f_3_3_3a_eval' 4

theorem SetTheory.Set.f_3_3_3a_eval''' (n : ℕ) : f_3_3_3a (2 * n + 3 : ℕ) = (2 * n + 4 : ℕ) := by
  convert f_3_3_3a_eval' _

-- 人们或许还希望定义一个与性质`P(x, y)`有关的减少函数`g`
abbrev SetTheory.Set.P_3_3_3b : Nat → Nat → Prop := fun x y ↦ (y + 1 : ℕ) = (x : ℕ)

-- 遗憾的是，这无法定义为一个函数，原因在于当`x = 0`时，不存在自然数`y`使得`y`增长之后的数字等于`x`
theorem SetTheory.Set.not_P_3_3_3b_existsUnique : ¬ ∀ x, ∃! y : Nat, P_3_3_3b x y := by
  by_contra h
  choose _ hn _ using h (0 : Nat)
  -- have : ((0 : Nat) : ℕ) = 0 := by simp [OfNat.ofNat]
  -- 使用`P_3_3_3b`的定义展开hn，得到`n + 1 = 0`，自然得出矛盾
  simp [P_3_3_3b] at hn

-- 另外，我们能够合理地定义这样一个与性质`P(x, y)`有关的减少函数`h : ℕ \ {0} → ℕ`
abbrev SetTheory.Set.P_3_3_3c : (Nat \ {(0 : Object)} : Set) → Nat → Prop :=
  fun x y ↦ ((y + 1 : ℕ) : Object) = x

-- 因为利用引理2.2.10可知，当`x ∈ ℕ \ {0}`时，确实恰好存在一个自然数`y`使得`y++ = x`
theorem SetTheory.Set.P_3_3_3c_existsUnique (x : (Nat \ {(0 : Object)} : Set)) :
    ∃! y : Nat, P_3_3_3c x y := by
  obtain ⟨x, hx⟩ := x; simp at hx; obtain ⟨hx1, hx2⟩ := hx
  set n := ((⟨x, hx1⟩ : Nat) : ℕ)
  have : x = (n : Nat) := by simp [n]
  simp [P_3_3_3c, this, Object.ofnat_eq'] at hx2 ⊢
  replace hx2 : n = (n - 1) + 1 := by omega
  apply ExistsUnique.intro ((n - 1 : ℕ) : Nat)
  · simp [← hx2]
  intro y hy; simp [← hy]

abbrev SetTheory.Set.f_3_3_3c : Function (Nat \ {(0 : Object)} : Set) Nat := Function.mk P_3_3_3c P_3_3_3c_existsUnique

theorem SetTheory.Set.f_3_3_3c_eval (x : (Nat \ {(0 : Object)} : Set)) (y : Nat) :
    y = f_3_3_3c x ↔ ((y + 1 : ℕ) : Object) = x := Function.eval _ _ _

abbrev SetTheory.Set.coe_nonzero (n : ℕ) (h : n ≠ 0) : (Nat \ {(0 : Object)} : Set) :=
  ⟨((n : ℕ) : Object), by
    simp [Object.ofnat_eq', h]
    rw [← Object.ofnat_eq]
    exact Subtype.property _
  ⟩

theorem SetTheory.Set.f_3_3_3c_eval' (n : ℕ) : f_3_3_3c (coe_nonzero (n + 1) (by positivity)) = n := by
  symm; simp [f_3_3_3c_eval]

theorem SetTheory.Set.f_3_3_3c_eval'' : f_3_3_3c (coe_nonzero 4 (by positivity)) = 3 := by
  convert f_3_3_3c_eval' 3

theorem SetTheory.Set.f_3_3_3c_eval''' (n : ℕ) : f_3_3_3c (coe_nonzero (2 * n + 3) (by positivity)) = (2 * n + 2 : ℕ) := by
  convert f_3_3_3c_eval' (2 * n + 2)

/--
例 3.3.3
-/
example : ¬ ∃ f : ℝ → ℝ, ∀ x y, y = f x ↔ y ^ 2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; set y := f (-1)
  have h1 := (hf _ y).mp (by rfl)
  have h2 := sq_nonneg y
  linarith

example : ¬ ∃ f : NNReal → ℝ, ∀ x y, y = f x ↔ y ^ 2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; specialize hf 4; set y := f 4
  -- have hy := (hf y).mp (by rfl)
  have h1 : 2 = y := (hf 2).mpr (by norm_num)
  have h2 : -2 = y := (hf (-2)).mpr (by norm_num)
  linarith

example : ∃ f : NNReal → NNReal, ∀ x y, y = f x ↔ y ^ 2 = x := by
  use NNReal.sqrt; intro x y
  constructor <;> intro h
  · rw [h, NNReal.sq_sqrt]
  · rw [← h, NNReal.sqrt_sq]

/--
例 3.3.4
-/
abbrev SetTheory.Set.P_3_3_5 : Nat → Nat → Prop := fun _x y ↦ y = 7

theorem SetTheory.Set.P_3_3_5_existsUnique (x : Nat) : ∃! y : Nat, P_3_3_5 x y := by
  apply ExistsUnique.intro 7 <;> simp [P_3_3_5]

abbrev SetTheory.Set.f_3_3_5 : Function Nat Nat := Function.mk P_3_3_5 P_3_3_5_existsUnique

theorem SetTheory.Set.f_3_3_5_eval (x : Nat) : f_3_3_5 x = 7 := by
  symm; rw [Function.eval]

/--
定义 3.3.7 函数的相等

两个具有相同定义域和值域的函数`f : X → Y`和`g : X → Y`被称为是相等的，记作`f = g`，当且仅当对任意的`x ∈ X`均有`f(x) = g(x)`
-/
theorem Function.eq_iff {X Y : Set} (f g : Function X Y) : f = g ↔ ∀ x : X, f x = g x := by
  constructor <;> intro h
  · simp [h]
  ext x y; constructor <;> intros
  · rwa [← Function.eval, ← h x, Function.eval]
  rwa [← Function.eval, h x, Function.eval]

/--
例 3.3.8
-/
abbrev SetTheory.Set.f_3_3_10a : Function Nat Nat := Function.mk_fn (fun x ↦ (x ^ 2 + 2 * x + 1 : ℕ))
abbrev SetTheory.Set.f_3_3_10b : Function Nat Nat := Function.mk_fn (fun x ↦ ((x + 1) ^ 2 : ℕ))

theorem SetTheory.Set.f_3_3_10_eq : f_3_3_10a = f_3_3_10b := by
  simp_rw [Function.eq_iff, Function.eval_of]
  intros; simp; ring

example : (fun x : NNReal ↦ (x : ℝ)) = (fun x : NNReal ↦ |(x : ℝ)|) := by
  simp_rw [NNReal.abs_eq]

example : (fun x : ℝ ↦ (x : ℝ)) ≠ (fun x : ℝ ↦ |(x : ℝ)|) := by
  intro h
  let a := (fun x : ℝ ↦ (x : ℝ)) (-1)
  let b := (fun x : ℝ ↦ |(x : ℝ)|) (-1)
  have hab : a = b := by unfold a; rw [h]
  norm_num [a, b] at hab

/--
例 3.3.9
-/
abbrev SetTheory.Set.f_3_3_11 (X : Set) : Function (∅ : Set) X :=
  Function.mk (fun _ _ ↦ true) (by intro ⟨x, hx⟩; simp at hx)

theorem SetTheory.Set.empty_function_unique {X : Set} (f g : Function (∅ : Set) X) : f = g := by
  simp_rw [Function.eq_iff]
  intro x
  have := x.property
  simp at this

/--
定义 3.3.10 复合

令`f : X → Y`和`g : Y → Z`为两个函数，并且满足`f`的值域与`g`的定义域是同一个集合。
那么我们定义两个函数`g`和`f`的复合`g ∘ f : X → Z`为一个函数，并由下面的式子来显式定义
`(g ∘ f)(x) := g(f(x))`
-/
noncomputable abbrev Function.comp {X Y Z : Set} (g : Function Y Z) (f : Function X Y) :
    Function X Z := Function.mk_fn (fun x ↦ g (f x))

infix:90 "○" => Function.comp

theorem Function.comp_eval {X Y Z : Set} (g : Function Y Z) (f : Function X Y) (x : X) :
    (g ○ f) x = g (f x) := Function.eval_of _ _

theorem Function.comp_eq_comp {X Y Z : Set} (g : Function Y Z) (f : Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn := by
  ext; simp only [Function.comp_eval, Function.comp_apply]

/--
例 3.3.11
-/
abbrev SetTheory.Set.f_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (2 * x : ℕ))
abbrev SetTheory.Set.g_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (x + 3 : ℕ))

theorem SetTheory.Set.g_circ_f_3_3_14 :
    g_3_3_14 ○ f_3_3_14 = Function.mk_fn (fun x ↦ ((2 * (x : ℕ) + 3 : ℕ) : Nat)) := by
  simp [Function.eq_iff, Function.eval_of]

theorem SetTheory.Set.f_circ_g_3_3_14 :
    f_3_3_14 ○ g_3_3_14 = Function.mk_fn (fun x ↦ ((2 * (x : ℕ) + 6 : ℕ) : Nat)) := by
  simp [Function.eq_iff, Function.eval_of]
  intros; ring

/--
引理 3.3.12 复合是可结合的

设`f : Z → W, g : Y → Z`和`h : X → Y`是三个函数，那么`f ∘ (g ∘ h) = (f ∘ g) ∘ h`
-/
theorem SetTheory.Set.comp_assoc {W X Y Z : Set} (h : Function X Y) (g : Function Y Z) (f : Function Z W) :
    f ○ (g ○ h) = (f ○ g) ○ h := by
  simp [Function.eq_iff]

/--
定义 3.3.14 一对一函数

如果函数`f`把不同的元素映射到不同的元素：
`x ≠ x' → f(x) ≠ f(x')`
则函数`f`是一对一的（或单射的）。即如果函数`f`满足
`f(x) = f(x') → x = x'`
则函数`f`是一对一的
-/
abbrev Function.one_to_one {X Y : Set} (f : Function X Y) : Prop := ∀ x x' : X, x ≠ x' → f x ≠ f x'

theorem Function.one_to_one_iff {X Y : Set} (f : Function X Y) :
    f.one_to_one ↔ ∀ x x' : X, f x = f x' → x = x' := by
  congr! 2 with x x'; tauto

theorem Function.one_to_one_iff' {X Y : Set} (f : Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn := by
  rw [one_to_one_iff, Function.Injective]

/--
例 3.3.15
-/
theorem SetTheory.Set.f_3_3_18_one_to_one :
    (Function.mk_fn (fun (n : Nat) ↦ ((n ^ 2 : ℕ) : Nat))).one_to_one := by
  rw [Function.one_to_one_iff]
  intro _ _ h
  simpa [Function.eval, Function.eval_of] using h

example : ¬ Function.Injective (fun (n : ℤ) ↦ n ^ 2) := by
  intro h
  have h1 : (fun n ↦ n ^ 2) 1 = (1 : ℤ) := by norm_num
  have h2 : (fun n ↦ n ^ 2) (-1) = (1 : ℤ) := by norm_num
  nth_rewrite 2 [← h1] at h2
  specialize h h2
  contradiction

example : Function.Injective (fun (n : ℕ) ↦ n ^ 2) := by
  intro _ _ _; rwa [← pow_left_inj₀ (by norm_num) (by norm_num) (show 2 ≠ 0 by norm_num)]

/--
注 3.3.16

如果函数`f : X → Y`不是一对一的，那么在定义域`X`中可以找到两个不相等的元素`x`和`x'`使得`f(x) = f(x')`,
因此我们能够找到被映射到同一个输出的两个输入。正因如此，我们称`f`是二对一的。
-/
theorem SetTheory.Set.two_to_one {X Y : Set} {f : Function X Y} (h : ¬ f.one_to_one) :
    ∃ x x' : X, x ≠ x' ∧ f x = f x' := by
  rw [Function.one_to_one] at h; simp_all

/--
定义 3.3.17 映上函数

如果`f(X) = Y`，即`Y`中每一个元素都能通过`f`对`X`中某个元素起作用得到，那么函数`f`是映上的（或满射的）
`∀ y ∈ Y, ∃ x ∈ X, f(x) = y`
-/
abbrev Function.onto {X Y : Set} (f : Function X Y) : Prop := ∀ y : Y, ∃ x : X, f x = y

theorem Function.onto_iff {X Y : Set} (f : Function X Y) : f.onto ↔ Function.Surjective f.to_fn := by rfl

/--
例 3.3.18
-/
example : ¬ Function.Surjective (fun (n : ℤ) ↦ n ^ 2) := by
  unfold Function.Surjective; push Not
  use -1; intro a
  linarith [sq_nonneg a]

abbrev A_3_3_21 := {m : ℤ // ∃ n : ℤ, m = n ^ 2}
example : Function.Surjective (fun (n : ℤ) ↦ ⟨n ^ 2, by use n⟩ : ℤ → A_3_3_21) := by
  rintro ⟨b, ⟨a, ha⟩⟩; use a
  simp only [ha]

/--
定义 3.3.20 双射函数

既是一对一的又是映上的函数`f : X → Y`也被称为双射函数或可逆函数。
-/
abbrev Function.bijective {X Y : Set} (f : Function X Y) : Prop := f.one_to_one ∧ f.onto

theorem Function.bijective_iff {X Y : Set} (f : Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn := by
  rw [Function.bijective, Function.Bijective, one_to_one_iff', onto_iff]

/--
例 3.3.21
-/
abbrev f_3_3_24 : Fin 3 → ({3, 4} : _root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨3, by norm_num⟩
| 1 => ⟨3, by norm_num⟩
| 2 => ⟨4, by norm_num⟩

example : ¬ Function.Injective f_3_3_24 := by decide
example : ¬ Function.Bijective f_3_3_24 := by decide

abbrev g_3_3_24 : Fin 2 → ({2, 3, 4} : _root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨2, by norm_num⟩
| 1 => ⟨3, by norm_num⟩

example : ¬ Function.Surjective g_3_3_24 := by decide
example : ¬ Function.Bijective g_3_3_24 := by decide

abbrev h_3_3_24 : Fin 3 → ({3, 4, 5} : _root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨3, by norm_num⟩
| 1 => ⟨4, by norm_num⟩
| 2 => ⟨5, by norm_num⟩

example : Function.Bijective h_3_3_24 := by decide

/--
例 3.3.22
-/
example : Function.Bijective (fun n ↦ ⟨n + 1, by omega⟩ : ℕ → {n : ℕ // n ≠ 0}) := by
  constructor
  · intro _ _
    simp only [Subtype.mk.injEq]; omega
  intro ⟨x, hx⟩; use x - 1
  simp only [Subtype.mk.injEq]; omega

example : ¬ Function.Bijective (fun n ↦ n + 1) := by
  suffices h : ¬ Function.Surjective (fun n ↦ n + 1) by unfold Function.Bijective; tauto
  unfold Function.Surjective; push Not
  use 0; intros
  symm; apply Nat.zero_ne_add_one

/--
注 3.3.24
-/
theorem Function.bijective_incorrect_def :
    ∃ X Y : Set, ∃ f : Function X Y, (∀ x : X, ∃! y : Y, y = f x) ∧ ¬ f.bijective := by
  use Nat, Nat
  set f := mk_fn fun x ↦ (0 : Nat); use f
  constructor
  · intros
    apply existsUnique_of_exists_of_unique
    · use 0; rw [Function.eval]
    intros; rw [Function.eval] at *; simp_all only [f]
  rw [Function.bijective]
  suffices h : ¬ f.one_to_one by tauto
  rw [Function.one_to_one_iff]
  push Not; use 0, 1; simp [f]

abbrev Function.inverse {X Y : Set} (f : Function X Y) (h : f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intros
    apply existsUnique_of_exists_of_unique
    · simp_all only
    intro _ _ hx hx'
    rw [← hx'] at hx
    apply f.one_to_one_iff.mp h.1
    simp [hx]
  )

theorem Function.inverse_eval {X Y : Set} {f : Function X Y} (h : f.bijective) (y : Y) (x : X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval _ _ _

theorem Function.inverse_eq {X Y : Set} [Nonempty X] {f : Function X Y} (h : f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn := by
  ext y; congr; symm
  rw [inverse_eval]
  apply Function.rightInverse_invFun (f.bijective_iff.mp h).2

/--
习题 3.3.1

使用`Function.eq_iff`证明
-/
theorem Function.refl {X Y : Set} (f : Function X Y) : f = f := by
  rw [eq_iff]
  intro x; rfl

theorem Function.symm {X Y : Set} (f g : Function X Y) : f = g ↔ g = f := by
  constructor <;>
    rw [eq_iff, eq_iff] <;>
    intro h x <;>
    symm <;>
    exact h x

theorem Function.trans {X Y : Set} (f g h : Function X Y) (hfg : f = g) (hgh : g = h) : f = h := by
  rw [eq_iff] at *
  intro x
  have h1 := hfg x
  have h2 := hgh x
  rwa [h2] at h1

theorem Function.comp_congr {X Y Z : Set} {f f' : Function X Y} (hff' : f = f') {g g' : Function Y Z}
    (hgg' : g = g') : g ○ f = g' ○ f' := by
  rw [eq_iff] at *; intro
  rw [comp_eval, comp_eval, hff', hgg']

/--
习题 3.3.2
-/
theorem Function.comp_of_inj {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hf : f.one_to_one)
    (hg : g.one_to_one) : (g ○ f).one_to_one := by
  intro _ _ h
  rw [comp_eval, comp_eval]
  by_contra h'
  have := hg _ _ (hf _ _ h)
  contradiction

theorem Function.comp_of_surj {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hf : f.onto)
    (hg : g.onto) : (g ○ f).onto := by
  intro y
  obtain ⟨x, hx⟩ := hg y
  obtain ⟨x', hx'⟩ := hf x
  use x'
  rwa [comp_eval, hx']

/--
习题 3.3.3
-/
theorem empty_function_one_to_one_iff (X : Set) (f : Function ∅ X) : f.one_to_one := by
  intro x; simp

theorem empty_function_onto_iff (X : Set) (f : Function ∅ X) : f.onto ↔ X = ∅ := by
  constructor
  · intro h
    by_contra h'
    obtain ⟨x, hx⟩ := SetTheory.Set.nonempty_def h'
    obtain ⟨x', _⟩ := h ⟨x, hx⟩
    absurd x'.property; simp
  · intro h y
    rw [h] at y
    absurd y.property; simp

theorem empty_function_bijective_iff (X : Set) (f : Function ∅ X) : f.bijective ↔ X = ∅ := by
  constructor
  · rintro ⟨h1, h2⟩
    rwa [← empty_function_onto_iff]
  · intro h
    exact ⟨empty_function_one_to_one_iff _ _, (empty_function_onto_iff _ _).mpr h⟩

/--
习题 3.3.4
-/
theorem Function.comp_cancel_left {X Y Z : Set} {f f' : Function X Y} {g : Function Y Z}
    (heq : g ○ f = g ○ f') (hg : g.one_to_one) : f = f' := by
  rw [eq_iff]
  intro x
  apply (one_to_one_iff _).mp hg _ _
  rw [← comp_eval, ← comp_eval, heq]

theorem Function.comp_cancel_right {X Y Z : Set} {f : Function X Y} {g g' : Function Y Z}
    (heq : g ○ f = g' ○ f) (hf : f.onto) : g = g' := by
  rw [eq_iff]
  intro x
  obtain ⟨_, hy⟩ := hf x
  rw [← hy, ← comp_eval, ← comp_eval, heq]

def Function.comp_cancel_left_without_hg : Decidable (∀ (X Y Z : Set) (f f' : Function X Y) (g : Function Y Z) (_heq : g ○ f = g ○ f'), f = f') := by
  apply isFalse
  push Not
  use Nat, Nat, Nat
  let f : Function Nat Nat := mk_fn fun x ↦ 1
  let f' : Function Nat Nat := mk_fn fun x ↦ 2
  let g : Function Nat Nat := mk_fn fun x ↦ 3
  use f, f', g
  unfold f f' g;
  constructor
  · simp
  · by_contra h
    rw [eq_iff] at h
    aesop

def Function.comp_cancel_right_without_hg : Decidable (∀ (X Y Z : Set) (f : Function X Y) (g g' : Function Y Z) (_heq : g ○ f = g' ○ f), g = g') := by
  apply isFalse
  push Not
  use Nat, Nat, Nat
  let f : Function Nat Nat := mk_fn fun x ↦ 1
  let g' : Function Nat Nat := mk_fn fun x ↦ x
  let g : Function Nat Nat := mk_fn fun x ↦ 1
  use f, g, g'
  unfold f g g'
  constructor
  · simp
  · by_contra h
    rw [eq_iff] at h
    have := h 2
    simp at this

/--
习题 3.3.5
-/
theorem Function.comp_injective {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hinj : (g ○ f).one_to_one) : f.one_to_one := by
  intro x x' hne
  by_contra h
  have := hinj x x' hne
  rw [comp_eval, comp_eval, h] at this
  contradiction

theorem Function.comp_surjective {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hsurj : (g ○ f).onto) : g.onto := by
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  aesop

def Function.comp_injective' : Decidable (∀ (X Y Z : Set) (f : Function X Y) (g : Function Y Z) (_hinj : (g ○ f).one_to_one), g.one_to_one) := by
  apply isFalse
  push Not
  use Nat, Nat, Nat
  let f : Function Nat Nat := mk_fn fun x ↦ (x : ℕ) * (2 : ℕ)
  let g : Function Nat Nat := mk_fn fun x ↦ (x : ℕ) / (2 : ℕ)
  use f, g
  unfold f g
  constructor
  · simp
  · by_contra h
    have := h 2 3 (show 2 ≠ 3 by norm_num)
    simp at this

def Function.comp_surjective' : Decidable (∀ (X Y Z : Set) (f : Function X Y) (g : Function Y Z) (_hsurj : (g ○ f).onto), f.onto) := by
  apply isFalse
  push Not
  use Nat, Nat, Nat
  let f : Function Nat Nat := mk_fn fun x ↦ (x : ℕ) + (1 : ℕ)
  let g : Function Nat Nat := mk_fn fun x ↦ (x : ℕ) - (1 : ℕ)
  use f, g
  unfold f g
  constructor
  · simp
  · by_contra h
    obtain ⟨x, hx⟩ := h 0
    simp at hx
    have hx' : SetTheory.Set.nat_equiv.symm x + 1 = 0 :=
      (SetTheory.Set.nat_equiv_inj _ _).mp hx
    have := Nat.succ_ne_zero x
    contradiction

/--
习题 3.3.6
-/
theorem Function.inverse_comp_self {X Y : Set} {f : Function X Y} (h : f.bijective) (x : X) :
    (f.inverse h) (f x) = x := by
  symm; rw [inverse_eval]

theorem Function.self_comp_inverse {X Y : Set} {f : Function X Y} (h : f.bijective) (y : Y) :
    f ((f.inverse h) y) = y := by
  rw [← inverse_eval]

theorem Function.inverse_bijective {X Y : Set} {f : Function X Y} (h : f.bijective) :
    (f.inverse h).bijective := by
  constructor
  · intro x x' hne
    by_contra
    rw [inverse_eval, self_comp_inverse] at this
    contradiction
  · unfold onto at *
    intro x
    use f x
    exact inverse_comp_self _ _

theorem Function.inverse_inverse {X Y : Set} {f : Function X Y} (h : f.bijective) :
    (f.inverse h).inverse (f.inverse_bijective h) = f := by
  rw [eq_iff]
  intro x; symm
  rw [inverse_eval]
  exact inverse_comp_self _ _

/--
习题 3.3.7
-/
theorem Function.comp_bijective {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hf : f.bijective) (hg : g.bijective) :
    (g ○ f).bijective := by
  exact ⟨comp_of_inj hf.1 hg.1, comp_of_surj hf.2 hg.2⟩

theorem Function.inv_of_comp {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hf : f.bijective) (hg : g.bijective) :
    (g ○ f).inverse (Function.comp_bijective hf hg) = (f.inverse hf) ○ (g.inverse hg) := by
  rw [eq_iff]
  intro x
  symm
  rw [inverse_eval, comp_eval, comp_eval, self_comp_inverse, self_comp_inverse]

/--
习题 3.3.8
-/
abbrev Function.inclusion {X Y : Set} (h : X ⊆ Y) :
    Function X Y := Function.mk_fn (fun x ↦ ⟨x.val, h x.val x.property⟩)

abbrev Function.id (X : Set) : Function X X := Function.mk_fn (fun x ↦ x)

theorem Function.inclusion_id (X : Set) :
    Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by rfl

theorem Function.inclusion_comp (X Y Z : Set) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    Function.inclusion hYZ ○ Function.inclusion hXY = Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) := by simp

theorem Function.comp_id {A B : Set} (f : Function A B) : f ○ Function.id A = f := by
  rw [eq_iff]; simp

theorem Function.id_comp {A B : Set} (f : Function A B) : Function.id B ○ f = f := by
  rw [eq_iff]; simp

theorem Function.comp_inv {A B : Set} (f : Function A B) (hf : f.bijective) :
    f ○ f.inverse hf = Function.id B := by
  simp [self_comp_inverse]

theorem Function.inv_comp {A B : Set} (f : Function A B) (hf : f.bijective) :
    f.inverse hf ○ f = Function.id A := by
  simp [inverse_comp_self]

open Classical in
theorem Function.glue {X Y Z : Set} (hXY : Disjoint X Y) (f : Function X Z) (g : Function Y Z) :
    ∃! h : Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by sorry
  -- h在X上定义为f, 在其余部分定义为g即可

open Classical in
theorem Function.glue' {X Y Z : Set} (f : Function X Z) (g : Function Y Z)
    (hfg : ∀ x : ((X ∩ Y) : Set), f ⟨x.val, by aesop⟩ = g ⟨x.val, by aesop⟩) :
    ∃! h : Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by sorry
  -- h在X-Y上定义为f, 在其余部分定义为g即可

end Chapter3
