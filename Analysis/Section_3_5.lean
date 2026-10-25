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

设`n ≥ 1`是自然数，并且对任意自然数`1 ≤ i ≤ n`，令`Xᵢ`为一个非空集合。
那么存在一个`n`元组`(xᵢ)_{1 ≤ i ≤ n}`使得对所有的`1 ≤ i ≤ n`均有`xᵢ ∈ Xᵢ`。
换言之，如果每一个`Xᵢ`都是非空集合，那么集合`Π_{1 ≤ i ≤ n} Xᵢ`也是非空的。
-/
theorem SetTheory.Set.finite_choice {n : ℕ} {X : Fin n → Set} (h : ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  sorry

end Chapter3
