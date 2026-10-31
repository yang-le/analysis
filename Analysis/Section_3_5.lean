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

若$`x`和$`y`是任意两个对象（它们有可能相等），那么我们把*有序对*$`(x, y)`定义为一个把$`x`作为第一个分量，$`y`作为第二个分量的新对象。
-/
@[ext]
structure OrderedPair where
  fst : Object
  snd : Object

#check OrderedPair.ext

/--
定义 3.5.1 有序对

两个有序对$`(x, y)`和$`(x', y')`被认为是相当的，当且仅当它们的两个分量都相等，即
$`(x, y) = (x', y') ↔ (x = x' ∧ y = y')`
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

如果$`X`和$`Y`是集合，那么我们定义*笛卡儿积*$`X × Y`为第一个分量在$`X`中且第二个分量在$`Y`中的全体有序对的集合，因此
$`X × Y = \{(x, y) : x ∈ X, y ∈ Y\}`
或等价地，
$`a ∈ (X × Y) ↔ ∃ x ∈ X, ∃ y ∈ Y, a = (x, y)`
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

/-- 例 3.5.6 -/
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
定义 3.5.7 有序$`n`元组

设$`n`是一个自然数，*有序$`n`元组*$`(xᵢ)_{1 ≤ i ≤ n}`（也记作$`(x₁, ⋯, xₙ)`）是由对象$`x₁, ⋯, xₙ`按次序构成的一个组，
我们把$`xᵢ`称为有序$`n`元组的第$`i`个分量。
-/
abbrev SetTheory.Set.tuple {I : Set} {X : I → Set} (x : ∀ i, X i) : Object :=
  ((fun i ↦ ⟨x i, by rw [mem_iUnion]; use i; exact (x i).property⟩) : I → iUnion I X)

/--
定义 3.5.7 $`n`重笛卡儿积

如果$`(Xᵢ)_{1 ≤ i ≤ n}`是集合的有序$`n`元组，我们定义它们的*笛卡儿积*$`Π_{1 ≤ i ≤ n} Xᵢ`（也记作$`Πⁿ_{i = 1} Xᵢ`或$`X₁ × ⋯ × Xₙ`）为
$$`Π_{1 ≤ i ≤ n} Xᵢ := \{(xᵢ)_{1 ≤ i ≤ n} : ∀ 1 ≤ i ≤ n, xᵢ ∈ Xᵢ\}`
-/
abbrev SetTheory.Set.iProd {I : Set} (X : I → Set) : Set :=
  ((iUnion I X) ^ I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

theorem SetTheory.Set.mem_iProd {I : Set} {X : I → Set} (t : Object) :
    t ∈ iProd X ↔ ∃ x : ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  · intro ⟨ht, x, h⟩; use x
  intro ⟨x, hx⟩
  have h : t ∈ (I.iUnion X) ^ I := by simp [hx]
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I : Set} {X : I → Set} (x : ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

@[simp]
theorem SetTheory.Set.tuple_inj {I : Set} {X : I → Set} (x y : ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
  constructor <;> intro h
  · ext i
    simp at h
    have : ((fun i ↦ ⟨x i, by rw [mem_iUnion]; use i; exact (x i).property⟩) : I → iUnion I X) i =
        ((fun i ↦ ⟨y i, by rw [mem_iUnion]; use i; exact (y i).property⟩) : I → iUnion I X) i := by
      rw [h]
    simp at this
    assumption
  · rw [h]

/--
例 3.5.9
-/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z : Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
例 3.5.11
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i : Object) (X : Set) :
    iProd (fun _ : ({i} : Set) ↦ X) ≃ X where
  toFun p := ((mem_iProd _).mp p.property).choose ⟨i, by simp⟩
  invFun x := ⟨tuple (fun _ : ({i} : Set) ↦ x), tuple_mem_iProd (fun _ : ({i} : Set) ↦ x)⟩
  left_inv p := by
    ext
    rw [((mem_iProd _).mp p.property).choose_spec, tuple_inj]
    ext j
    rw [show j = ⟨i, by simp⟩ by aesop]
  right_inv x := by
    ext; dsimp
    generalize_proofs h _
    rw [← (tuple_inj _ _).mp h.choose_spec]

abbrev SetTheory.Set.empty_iProd_equiv (X : (∅ : Set) → Set) : iProd X ≃ Unit where
  toFun _ := ()
  invFun _ := by
    let f : (i : (∅ : Set).toSubtype) → {x // x ∈ X i} :=
      fun i ↦ ⟨X i, by have := i.property; simp_all only [not_mem_empty i]⟩
    exact ⟨tuple f, tuple_mem_iProd f⟩
  left_inv p := by
    ext; simp
    obtain ⟨_, h⟩ := (mem_iProd _).mp p.property
    rw [h]; apply congrArg tuple
    ext i
    have := i.property
    simp_all only [not_mem_empty i]
  right_inv _ := by dsimp

noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I : Set) (X : Set) :
    iProd (fun _ : I ↦ X) ≃ (I → X) where
  toFun p := ((mem_iProd _).mp p.property).choose
  invFun x := ⟨tuple x, tuple_mem_iProd x⟩
  left_inv p := by ext; rw [((mem_iProd _).mp p.property).choose_spec]
  right_inv x := by
    ext; dsimp
    generalize_proofs h
    rw [← (tuple_inj _ _).mp h.choose_spec]

noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X : ({0, 1} : Set) → Set) :
    iProd X ≃ (X ⟨0, by simp⟩) ×ˢ (X ⟨1, by simp⟩) where
  toFun p := by
    let x := ((mem_iProd _).mp p.property).choose
    exact mk_cartesian (x ⟨0, by simp⟩) (x ⟨1, by simp⟩)
  invFun x := by
    let f : (i : ({0, 1} : Set)) → X i := fun i ↦ by
      by_cases h : i.val = 0
      · have hi : i = ⟨0, by simp⟩ := by ext; rw [h]
        exact hi ▸ fst x
      · have hi : i = ⟨1, by simp⟩ := by aesop
        exact hi ▸ snd x
    exact ⟨tuple f, tuple_mem_iProd f⟩
  left_inv p := by
    ext
    rw [((mem_iProd _).mp p.property).choose_spec, tuple_inj]
    ext i
    by_cases h : i.val = 0 <;> simp [h]
    · have hi : i = ⟨0, by simp⟩ := by ext; rw [h]
      subst hi
      simp_all only
    · have hi : i = ⟨1, by simp⟩ := by aesop
      subst hi
      simp_all only
  right_inv x := by
    let f : (i : ({0, 1} : Set)) → X i := fun i ↦ by
      by_cases h : i.val = 0
      · have hi : i = ⟨0, by simp⟩ := by ext; rw [h]
        exact hi ▸ fst x
      · have hi : i = ⟨1, by simp⟩ := by aesop
        exact hi ▸ snd x
    let h := (mem_iProd _).mp (tuple_mem_iProd f)
    have : h.choose = f := by
      have := h.choose_spec
      rw [tuple_inj] at this
      rw [← this]
    simp; rw [this]; aesop

noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X : ({0, 1, 2} : Set) → Set) :
    iProd X ≃ (X ⟨0, by simp⟩) ×ˢ (X ⟨1, by simp⟩) ×ˢ (X ⟨2, by simp⟩) where
  toFun p := by
    let x := ((mem_iProd _).mp p.property).choose
    exact mk_cartesian (x ⟨0, by simp⟩) (mk_cartesian (x ⟨1, by simp⟩) (x ⟨2, by simp⟩))
  invFun x := by
    let f : (i : ({0, 1, 2} : Set)) → X i := fun i ↦ by
      by_cases h : i.val = 0
      · have hi : i = ⟨0, by simp⟩ := by ext; rw [h]
        exact hi ▸ fst x
      · by_cases h : i.val = 1
        · have hi : i = ⟨1, by simp⟩ := by ext; rw [h]
          exact hi ▸ fst (snd x)
        · have hi : i = ⟨2, by simp⟩ := by aesop
          exact hi ▸ snd (snd x)
    exact ⟨tuple f, tuple_mem_iProd f⟩
  left_inv p := by
    ext
    rw [((mem_iProd _).mp p.property).choose_spec, tuple_inj]
    ext i
    by_cases h : i.val = 0 <;> simp [h]
    · have hi : i = ⟨0, by simp⟩ := by ext; rw [h]
      subst hi
      simp_all only
    · by_cases h : i.val = 1 <;> simp [h]
      · have hi : i = ⟨1, by simp⟩ := by ext; rw [h]
        subst hi
        simp_all only
      · have hi : i = ⟨2, by simp⟩ := by aesop
        subst hi
        simp_all only
  right_inv x := by
    let f : (i : ({0, 1, 2} : Set)) → X i := fun i ↦ by
      by_cases h : i.val = 0
      · have hi : i = ⟨0, by simp⟩ := by ext; rw [h]
        exact hi ▸ fst x
      · by_cases h : i.val = 1
        · have hi : i = ⟨1, by simp⟩ := by ext; rw [h]
          exact hi ▸ fst (snd x)
        · have hi : i = ⟨2, by simp⟩ := by aesop
          exact hi ▸ snd (snd x)
    let h := (mem_iProd _).mp (tuple_mem_iProd f)
    have : h.choose = f := by
      have := h.choose_spec
      rw [tuple_inj] at this
      rw [← this]
    simp; rw [this]; aesop

noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I : Set) (X : I → Set) :
    iProd X ≃ Set.pi .univ (fun i : I ↦ ((X i) : _root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x := ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [← (tuple_inj _ _).mp h.choose_spec]

abbrev SetTheory.Set.Fin (n : ℕ) : Set := nat.specify (fun m ↦ (m : ℕ) < n)

theorem SetTheory.Set.mem_Fin (n : ℕ) (x : Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  · intro ⟨h1, h2⟩; use ↑(⟨x, h1⟩ : nat); simp [h2]
  intro ⟨m, hm, h⟩
  use (by rw [h, ← Object.ofnat_eq]; exact (m : nat).property)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m : ℕ) (h : m < n) : Fin n := ⟨m, by rw [mem_Fin]; use m⟩

theorem SetTheory.Set.mem_Fin' {n : ℕ} (x : Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ← Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n : ℕ} (i : Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n : ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n : ℕ} (i : Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n : ℕ} (i : Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n : ℕ} (i : Fin n) : ((i : ℕ) : Object) = (i : Object) := by
  set j := (i : ℕ); obtain ⟨h, h' : i = Fin_mk n j h⟩ := toNat_spec i; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n : ℕ} {i j : Fin n} : i = j ↔ (i : ℕ) = (j : ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n : ℕ} (i : Fin n) {j : ℕ} : (i : Object) = (j : Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [← Object.natCast_inj]
  aesop

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m : ℕ} (i : Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m) : ℕ) = (i : ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose : Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n : ℕ} (m : ℕ) (h : m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N : ℕ) (h : n ≤ N) (i : Fin n) : Fin N := ⟨i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n : ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/--
引理 3.5.12 有限选取

设$`n ≥ 1`是自然数，并且对任意自然数$`1 ≤ i ≤ n`，令$`Xᵢ`为一个非空集合。
那么存在一个$`n`元组$`(xᵢ)_{1 ≤ i ≤ n}`使得对所有的$`1 ≤ i ≤ n`均有$`xᵢ ∈ Xᵢ`。
换言之，如果每一个$`Xᵢ`都是非空集合，那么集合$`Π_{1 ≤ i ≤ n} Xᵢ`也是非空的。
-/
theorem SetTheory.Set.finite_choice {n : ℕ} {X : Fin n → Set} (h : ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  induction' n with n hn
  · have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i : Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n + 1) (by linarith) i)
  have hX' (i : Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨x', rfl⟩ := hx'
  set last : Fin (n + 1) := Fin_mk (n + 1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [← Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/--
习题 3.5.1
-/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({p.fst, (({p.fst, p.snd} : Set) : Object)} : Set)
  inj' := by
    intro x y h
    rw [eq]
    simp at h
    obtain (⟨h1, h2⟩ | ⟨h1, h2⟩) := pair_eq_pair h <;> simp_all
    · obtain (⟨h21, h22⟩ | ⟨h21, h22⟩) := pair_eq_pair h2
      · assumption
      · rw [← h21, h22]
    · obtain (_ | _) := not_mem_mem ({x.fst, x.snd} : Set) ({y.fst, y.snd} : Set)
      · rw [← h1] at h2
        have : SetTheory.set_to_object {x.fst, x.snd} ≠ y.fst := by aesop
        contradiction
      · have : x.fst ≠ SetTheory.set_to_object {y.fst, y.snd} := by aesop
        contradiction

structure SetTheory.Set.Tuple (n : ℕ) where
  X : Set
  x : Fin n → X
  surj : Function.Surjective x

@[ext]
lemma SetTheory.Set.Tuple.ext {n : ℕ} {t t' : Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n) : Object) = ((t'.x n) : Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/--
习题 3.5.2
-/
theorem SetTheory.Set.Tuple.eq {n : ℕ} (t t' : Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n) : Object) = ((t'.x n) : Object) := by
  refine ⟨by aesop, ?_⟩
  intro h
  ext x
  · constructor
    · intro h'
      obtain ⟨y, hy⟩ := t.surj ⟨x, h'⟩
      have := h y
      have hx : x = t'.x y := by aesop
      have := (t'.x y).property
      rwa [← hx] at this
    · intro h'
      obtain ⟨y, hy⟩ := t'.surj ⟨x, h'⟩
      have := h y
      have hx : x = t.x y := by aesop
      have := (t.x y).property
      rwa [← hx] at this
  · exact h x

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n : ℕ) (X : Fin n → Set) :
    iProd X ≃ {t : Tuple n // ∀ i, (t.x i : Object) ∈ X i} where
  toFun p := by
    have x := ((mem_iProd _).mp p.property).choose
    let f' (i : Fin n) : iUnion _ X :=
      ⟨x i, by rw [mem_iUnion]; exact ⟨i, (x i).property⟩⟩
    let U := image f' (Fin n)
    let f (i : Fin n) : U :=
      ⟨x i, by rw [mem_image]; exact ⟨i, i.property, rfl⟩⟩
    let t : Tuple n := ⟨U, f, by
      intro b
      obtain ⟨x, _, _⟩ := (mem_image _ _ _).mp b.property
      use x; aesop
    ⟩
    exact ⟨t, by
      intro i
      simp only [t, f]
      exact (x i).property
    ⟩
  invFun t := by
    let f (i : Fin n) : X i := ⟨t.val.x i, t.property i⟩
    exact ⟨tuple f, tuple_mem_iProd f⟩
  left_inv p := by
    ext; simp
    generalize_proofs h
    exact h.choose_spec.symm
  right_inv t := by
    ext x <;> dsimp <;>
    generalize_proofs _ h1 <;>
    have h1 := h1.choose_spec <;>
    rw [tuple_inj] at h1
    · constructor <;> intro h
      · rw [mem_image] at h
        obtain ⟨i, _, h2⟩ := h
        simp [← h2, ← h1]
        exact (t.val.x i).property
      · rw [mem_image]
        obtain ⟨a, ha⟩ := t.val.surj ⟨x, h⟩
        exact ⟨a, a.property, by simp [← h1, ha]⟩
    · rw [← h1]

/--
习题 3.5.3

使用{lean}`OrderedPair.eq`或{lean}`SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p : OrderedPair) : p = p := by
  rw [eq]
  constructor <;> rfl

theorem OrderedPair.symm (p q : OrderedPair) : p = q ↔ q = p := by
  constructor
  all_goals
  · intro h
    rw [eq] at *
    exact ⟨h.1.symm, h.2.symm⟩

theorem OrderedPair.trans {p q r : OrderedPair} (hpq : p = q) (hqr : q = r) : p = r := by
  rw [eq] at *
  constructor
  · rw [hpq.1, hqr.1]
  · rw [hpq.2, hqr.2]

theorem SetTheory.Set.tuple_refl {I : Set} {X : I → Set} (a : ∀ i, X i) :
    tuple a = tuple a := by
  rw [tuple_inj]

theorem SetTheory.Set.tuple_symm {I : Set} {X : I → Set} (a b : ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by
  constructor
  all_goals
  · intro h
    rw [tuple_inj] at *
    exact h.symm

theorem SetTheory.Set.tuple_trans {I : Set} {X : I → Set} {a b c : ∀ i, X i}
  (hab : tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
  rw [tuple_inj] at *
  rw [hab, hbc]

/--
习题 3.5.4
-/
theorem SetTheory.Set.prod_union (A B C : Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  ext x
  constructor <;> intro h <;> simp at *
  · obtain ⟨a, ha, b, (hb | hb), hx⟩ := h
    · left; exact ⟨a, ha, b, hb, hx⟩
    · right; exact ⟨a, ha, b, hb, hx⟩
  · obtain (⟨a, ha, b, hb, hx⟩ | ⟨a, ha, b, hb, hx⟩) := h
    · exact ⟨a, ha, b, Or.inl hb, hx⟩
    · exact ⟨a, ha, b, Or.inr hb, hx⟩

theorem SetTheory.Set.prod_inter (A B C : Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  ext x
  constructor <;> intro h <;> simp at *
  · obtain ⟨a, ha, b, ⟨hb1, hb2⟩, hx⟩ := h
    constructor
    · exact ⟨a, ha, b, hb1, hx⟩
    · exact ⟨a, ha, b, hb2, hx⟩
  · obtain ⟨⟨a, ha, b, hb, hx⟩, ⟨_, _, _, _, hx'⟩⟩ := h
    use a, ha, b
    split_ands
    · assumption
    · simp [hx'] at hx
      rwa [← hx.2]
    · simp [hx'] at hx
      rwa [← hx.1, ← hx.2]

theorem SetTheory.Set.prod_diff (A B C : Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  ext x
  constructor <;> intro h <;> simp at *
  · obtain ⟨a, ha, b, ⟨hb1, hb2⟩, hx⟩ := h
    constructor
    · exact ⟨a, ha, b, hb1, hx⟩
    · by_contra! h
      obtain ⟨_, _, _, hb', hx'⟩ := h
      simp [hx'] at hx
      rw [hx.2] at hb'
      contradiction
  · obtain ⟨⟨a, ha, b, _, _⟩, h⟩ := h
    use a, ha, b
    split_ands
    · assumption
    · by_contra! hb
      have := h a ha b hb
      contradiction
    · assumption

theorem SetTheory.Set.union_prod (A B C : Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by
  ext x
  constructor <;> intro h <;> simp at *
  · obtain ⟨a, (ha | ha), b, hb, hx⟩ := h
    · left; exact ⟨a, ha, b, hb, hx⟩
    · right; exact ⟨a, ha, b, hb, hx⟩
  · obtain (⟨a, ha, b, hb, hx⟩ | ⟨a, ha, b, hb, hx⟩) := h
    · exact ⟨a, Or.inl ha, b, hb, hx⟩
    · exact ⟨a, Or.inr ha, b, hb, hx⟩

theorem SetTheory.Set.inter_prod (A B C : Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by
  ext x
  constructor <;> intro h <;> simp at *
  · obtain ⟨a, ⟨ha1, ha2⟩, b, hb, hx⟩ := h
    constructor
    · exact ⟨a, ha1, b, hb, hx⟩
    · exact ⟨a, ha2, b, hb, hx⟩
  · obtain ⟨⟨a, ha, b, hb, hx⟩, ⟨_, _, _, _, hx'⟩⟩ := h
    use a
    split_ands
    · assumption
    · simp [hx'] at hx
      rwa [← hx.1]
    · use b

theorem SetTheory.Set.diff_prod (A B C : Set) : (A \ B) ×ˢ C= (A ×ˢ C) \ (B ×ˢ C) := by
  ext x
  constructor <;> intro h <;> simp at *
  · obtain ⟨a, ⟨ha1, ha2⟩, b, hb, hx⟩ := h
    constructor
    · exact ⟨a, ha1, b, hb, hx⟩
    · by_contra! h
      obtain ⟨_, ha', _, _, hx'⟩ := h
      simp [hx'] at hx
      rw [hx.1] at ha'
      contradiction
  · obtain ⟨⟨a, _, b, hb, _⟩, h⟩ := h
    use a
    split_ands
    · assumption
    · by_contra! ha
      have := h a ha b hb
      contradiction
    · use b

/--
习题 3.5.5
-/
theorem SetTheory.Set.inter_of_prod (A B C D : Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  ext x
  constructor <;> intro h <;> simp at *
  · obtain ⟨⟨a, ha, b, hb, hx⟩, ⟨_, hc, _, hd, hx'⟩⟩ := h
    simp [hx] at hx'
    rw [← hx'.1] at hc
    rw [← hx'.2] at hd
    exact ⟨a, ⟨ha, hc⟩, ⟨b, ⟨hb, hd⟩, hx⟩⟩
  · obtain ⟨a, ⟨ha, hc⟩, ⟨b, ⟨hb, hd⟩, hx⟩⟩ := h
    exact ⟨⟨a, ha, b, hb, hx⟩, ⟨a, hc, b, hd, hx⟩⟩

def SetTheory.Set.union_of_prod :
    Decidable (∀ (A B C D : Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  apply isFalse
  push Not
  use ({1} : Set), ({2} : Set), ({3} : Set), ({4} : Set)
  by_contra! h
  have h1 : ({1} : Set) ×ˢ ({2} : Set) ∪ ({3} : Set)×ˢ ({4} : Set) = {
      ((mk_cartesian (1 : Nat) (2 : Nat)) : Object),
      ((mk_cartesian (3 : Nat) (4 : Nat)) : Object)} := by
    ext x
    refine ⟨?_, by aesop⟩
    intro hx
    simp at *
    assumption
  have h2 : (({1} : Set) ∪ ({3} : Set)) ×ˢ (({2} : Set) ∪ ({4} : Set)) = {
      ((mk_cartesian (1 : Nat) (2 : Nat)) : Object),
      ((mk_cartesian (1 : Nat) (4 : Nat)) : Object),
      ((mk_cartesian (3 : Nat) (2 : Nat)) : Object),
      ((mk_cartesian (3 : Nat) (4 : Nat)) : Object)} := by
    ext x; aesop
  rw [h1, h2] at h
  have : ((mk_cartesian (1 : Nat) (4 : Nat)) : Object) ∈ ({
    ((mk_cartesian (1 : Nat) (2 : Nat)) : Object),
    ((mk_cartesian (3 : Nat) (4 : Nat)) : Object)} : Set) := by aesop
  simp at this
  obtain (h' | h') := this <;>
  unfold mk_cartesian at h' <;>
  simp at h'
  · change 4 = 2 at h'
    norm_num at h'
  · change 1 = 3 at h'
    norm_num at h'

def SetTheory.Set.diff_of_prod :
    Decidable (∀ (A B C D : Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  apply isFalse
  push Not
  use ({1} : Set), ({2} : Set), ({1} : Set), ({3} : Set)
  by_contra h
  have h1 : (({1} : Set) ×ˢ ({2} : Set)) \ (({1} : Set) ×ˢ ({3} : Set)) = {((mk_cartesian (1 : Nat) (2 : Nat)) : Object)} := by
    ext x
    refine ⟨by aesop, ?_⟩
    intro hx
    simp at *
    constructor
    · assumption
    · by_contra
      rw [this] at hx
      unfold mk_cartesian at hx
      simp at hx
      change 1 = 1 ∧ 3 = 2 at hx
      norm_num at hx
  have h2 : (({1} : Set) \ ({1} : Set)) ×ˢ (({2} : Set) \ ({3} : Set)) = ∅ := by aesop
  rw [h1, h2] at h
  have : ((mk_cartesian (1 : Nat) (2 : Nat)) : Object) ∈ (∅ : Set) := by rw [← h]; simp
  exact not_mem_empty _ this

/--
习题 3.5.6
-/
theorem SetTheory.Set.prod_subset_prod {A B C D : Set} (hA : A ≠ ∅) (hB : B ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
  constructor
  · intro h
    constructor
    · intro x hx
      obtain ⟨y, hy⟩ := nonempty_def hB
      have : (mk_cartesian ⟨x, hx⟩ ⟨y, hy⟩).val ∈ A ×ˢ B := by aesop
      obtain ⟨x', y', h'⟩ := (mem_cartesian _ _ _).mp (h _ this)
      unfold mk_cartesian at h'
      simp at h'
      rw [h'.1]
      exact x'.property
    · intro y hy
      obtain ⟨x, hx⟩ := nonempty_def hA
      have : (mk_cartesian ⟨x, hx⟩ ⟨y, hy⟩).val ∈ A ×ˢ B := by aesop
      obtain ⟨x', y', h'⟩ := (mem_cartesian _ _ _).mp (h _ this)
      unfold mk_cartesian at h'
      simp at h'
      rw [h'.2]
      exact y'.property
  · intro ⟨h1, h2⟩ x hx
    obtain ⟨x1, x2, _⟩ := (mem_cartesian _ _ _).mp hx
    rw [mem_cartesian]
    use ⟨x1, h1 _ x1.property⟩, ⟨x2, h2 _ x2.property⟩

def SetTheory.Set.prod_subset_prod' :
    Decidable (∀ (A B C D : Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  apply isFalse
  push Not
  use (∅ : Set), ({1} : Set), ({2} : Set), ({3} : Set)
  left
  constructor
  · intro x h
    simp at h
  · intro
    by_contra h
    have : 1 ∈ ({1} : Set) := by simp
    have := (mem_singleton _ _).mp (h _ this)
    simp at this

/--
习题 3.5.7
-/
theorem SetTheory.Set.direct_sum {X Y Z : Set} (f : Z → X) (g : Z → Y) :
    ∃! h : Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
  use fun z ↦ mk_cartesian (f z) (g z)
  split_ands
  · ext; simp
  · ext; simp
  · intro h' hh'
    ext x; aesop

/--
习题 3.5.8
-/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n : ℕ} {X : Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
  · constructor
    · intro h
      by_contra! h'
      let f (i : Fin n) : X i :=⟨(nonempty_def (h' i)).choose, (nonempty_def (h' i)).choose_spec⟩
      have := tuple_mem_iProd f
      simp [h] at this
    · intro ⟨i, h⟩
      by_contra! h'
      obtain ⟨x, hx⟩ := nonempty_def h'
      obtain ⟨x', _⟩ := (mem_iProd _).mp hx
      have := (x' i).property
      simp [h] at this

/--
习题 3.5.9
-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J : Set} (A : I → Set) (B : J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by
  ext x
  constructor
  · intro h
    simp [mem_iUnion] at *
    obtain ⟨⟨a, ha, hx⟩, ⟨b, hb, hx'⟩⟩ := h
    use a, b, ⟨ha, hb⟩
    constructor <;>
    simpa [show OrderedPair.toObject ⟨a, b⟩ = mk_cartesian ⟨a, ha⟩ ⟨b, hb⟩ by rfl]
  · intro h
    simp [mem_iUnion] at *
    obtain ⟨a, b, ⟨ha, hb⟩, hx, hx'⟩ := h
    constructor
    · use a, ha
      simp [show OrderedPair.toObject ⟨a, b⟩ = mk_cartesian ⟨a, ha⟩ ⟨b, hb⟩ by rfl] at hx
      assumption
    · use b, hb
      simp [show OrderedPair.toObject ⟨a, b⟩ = mk_cartesian ⟨a, ha⟩ ⟨b, hb⟩ by rfl] at hx'
      assumption

/--
习题 3.5.10
-/
abbrev SetTheory.Set.graph {X Y : Set} (f : X → Y) : Set :=
    (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

theorem SetTheory.Set.graph_inj {X Y : Set} (f f' : X → Y) :
    graph f = graph f' ↔ f = f' := by
  refine ⟨?_, by aesop⟩
  intro h
  ext x
  have : (mk_cartesian x (f x)).val ∈ graph f := by
    simp
    use x, x.property, (f x), (f x).property
    rfl
  rw [h] at this
  simp at this
  simp only [this.2]

theorem SetTheory.Set.is_graph {X Y G : Set} (hG : G ⊆ X ×ˢ Y)
  (hvert : ∀ x : X, ∃! y : Y, ((⟨x, y⟩ : OrderedPair) : Object) ∈ G) :
    ∃! f : X → Y, G = graph f := by
  use fun x ↦ (hvert x).choose
  constructor
  · simp; ext x
    constructor
    · intro hx
      rw [specification_axiom'']
      use hG _ hx
      generalize_proofs h hx'
      obtain ⟨x1, x2, h1⟩ := (mem_cartesian _ _ _).mp hx'
      have hx1 : fst ⟨x, hx'⟩ = x1 := by
        simp [h1]
        change fst (mk_cartesian x1 x2) = x1
        simp
      have hx2 : snd ⟨x, hx'⟩ = x2 := by
        simp [h1]
        change snd (mk_cartesian x1 x2) = x2
        simp
      rw [hx1, hx2]
      obtain ⟨h2, h3⟩ := (hvert ⟨x1, x1.property⟩).choose_spec
      rw [h1] at hx
      rw [← h3 x2 hx] at h2
      simp [← (h x1).choose_spec.2 x2 x2.property h2]
    · intro hx
      rw [specification_axiom''] at hx
      obtain ⟨hx, h⟩ := hx
      obtain ⟨x1, x2, h1⟩ := (mem_cartesian _ _ _).mp hx
      have hx1 : x1 = fst ⟨x, hx⟩ := by
        simp [h1]
        change x1 = fst (mk_cartesian x1 x2)
        simp
      have hx2 : x2 = snd ⟨x, hx⟩ := by
        simp [h1]
        change x2 = snd (mk_cartesian x1 x2)
        simp
      generalize_proofs h2 at h
      obtain ⟨h3, _⟩ := (h2 x1).choose_spec
      simp only [h, hx1] at h3
      rwa [h1, hx1, hx2]
  · intro y rfl
    ext x
    generalize_proofs h
    have h1 := h.choose_spec.1
    simp [specification_axiom''] at h1
    obtain ⟨_, _, hy⟩ := hvert x
    simp [specification_axiom''] at hy
    have := hy h.choose (h.choose).property
    simp at this
    simp [this h1]
    have := hy (y x) (y x).property
    generalize_proofs h2 at this
    have h3 : y (fst ⟨OrderedPair.toObject { fst := ↑x, snd := ↑(y x) }, h2⟩) =
        snd ⟨OrderedPair.toObject { fst := ↑x, snd := ↑(y x) }, h2⟩ := by
      change y (fst (mk_cartesian x (y x))) = snd (mk_cartesian x (y x))
      simp
    simp at this
    simp [this h3]

end Chapter3
