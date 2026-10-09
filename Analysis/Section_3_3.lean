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

end Chapter3
