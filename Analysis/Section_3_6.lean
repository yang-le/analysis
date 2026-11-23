import Mathlib.Tactic
import Analysis.Section_3_3
import Analysis.Section_3_5

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/--
定义 3.6.1 相等的基数

我们称两个集合$`X`和$`Y`有*相等的基数*，当且仅当存在从$`X`到$`Y`的一个双射：$`f : X → Y`
-/
abbrev SetTheory.Set.EqualCard (X Y : Set) : Prop := ∃ f : X → Y, Function.Bijective f

/--
例 3.6.2
-/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0, 1, 2} {3, 4, 5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3 : Object) ∨ y = (4 : Object) ∨ y = (5 : Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/--
注 3.6.3
-/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x : ℕ))) := by
  use fun x ↦ ⟨(x * 2 : ℕ), by simp [specification_axiom'']; exact ((x * 2 : ℕ) : nat).property⟩
  constructor
  · intro x y h
    aesop
  · intro y
    have := y.property
    simp [specification_axiom'', Even] at this
    obtain ⟨_, a, h⟩ :=this
    use a; simp; congr
    rw [mul_two, ← h]
    simp

/--
命题 3.6.4

“具有相等的基数”是一种等价关系
-/
@[refl]
theorem SetTheory.Set.EqualCard.refl (X : Set) : EqualCard X X := ⟨id, Function.bijective_id⟩

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y : Set} (h : EqualCard X Y) : EqualCard Y X := by
  obtain ⟨f, hf⟩ := h
  let g := (Equiv.ofBijective f hf).symm
  exact ⟨g, g.bijective⟩

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z : Set} (h1 : EqualCard X Y) (h2 : EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨f1, hf1⟩ := h1
  obtain ⟨f2, hf2⟩ := h2
  let g := Equiv.ofBijective (f2 ∘ f1) (hf2.comp hf1)
  exact ⟨g, g.bijective⟩

instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨EqualCard, {refl, symm, trans}⟩

/--
定义 3.6.5

设$`n`是一个自然数，称集合$`X`的*基数*为$`n`，当且仅当$`X`和集合$`\{i ∈ ℕ : 1 ≤ i ≤ n\}`有相等的基数。
我们也称$`X`中*有$`n`个元素*，当且仅当$`X`的基数为$`n`.
-/
abbrev SetTheory.Set.has_card (X : Set) (n : ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X : Set) (n : ℕ) :
    X.has_card n ↔ ∃ f : X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, EqualCard]

/--
注 3.6.6
-/
theorem SetTheory.Set.Remark_3_6_6 (n : ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x : ℕ) ∧ (x : ℕ) ≤ n)).has_card n := by
  rw [has_card_iff]
  use fun x ↦ by
    have prop := x.property
    simp [specification_axiom''] at prop
    have : ∃ x' : nat, x' = x.val := by
      use ⟨x.val, prop.choose⟩
    let x := (this.choose : ℕ)
    have h := prop.choose_spec
    rw! [← this.choose_spec] at h
    change 1 ≤ x ∧ x ≤ n at h
    exact match x with
    | 0 => Fin_mk _ 0 (by absurd h.1; simp)
    | Nat.succ n => Fin_mk _ n (by aesop)
  constructor
  · intro x1 x2 h
    simp at h
    by_cases h' : x1.val = 0
    · have prop := x1.property
      simp at prop
      have := prop.choose_spec.1
      simp [Object.ofnat_eq', h'] at this
    · split at h
      · rename_i h1 _ _
        absurd h1.1
        simp
      · split at h
        · rename_i h1 _ _
          absurd h1.1
          simp
        · ext
          simp at h
          rename_i _ _ _ ha _ _ _ _ _ _ hb _
          simp at ha hb
          simp [h, ← hb] at ha
          generalize_proofs h1 h2 at ha
          exact (ha ▸ h1.choose_spec) ▸ h2.choose_spec
  · intro y
    use ⟨(y : ℕ).succ, by simp; exact ⟨((y : ℕ).succ : nat).property, Fin.toNat_lt y⟩⟩
    simp
    generalize_proofs h
    split
    · rename_i h1 _ _
      absurd h1.1
      simp
    · simp
      rename_i n _ h1 _
      have := h1 ▸ nat_coe_eq_iff'.mp h.choose_spec
      change n.succ = (y + 1 : ℕ) at this
      simpa

/--
例 3.6.7
-/
theorem SetTheory.Set.Example_3_6_7a (a : Object) : ({a} : Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d : Object} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if  x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0 : ℕ) ∨ y = (1 : ℕ) ∨ y = (2 : ℕ) ∨ y = (3 : ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/--
引理 3.6.9

假设$`n ≥ 1`，且$`X`的基数为$`n`. 那么$`X`是非空的。
-/
theorem SetTheory.Set.pos_card_nonempty {n : ℕ} (h : n ≥ 1) {X : Set} (hX : X.has_card n) : X ≠ ∅ := by
  by_contra h
  rw [has_card_iff] at hX
  choose f hf using hX
  have := ((Equiv.ofBijective f hf).symm ⟨0, by rw [mem_Fin]; use 0, (by omega); rfl⟩).property
  simp [h] at this

/--
习题 3.6.2
-/
theorem SetTheory.Set.has_card_zero {X : Set} : X.has_card 0 ↔ X = ∅ := by
  by_contra! (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rw [has_card_iff] at h1
  · choose f hf using h1
    obtain ⟨x, hx⟩ := nonempty_def h2
    obtain ⟨y, hy⟩ := (mem_Fin _ _).mp ((Equiv.ofBijective f hf) ⟨x, hx⟩).property
    linarith
  · push Not at h1
    let f : X.toSubtype → (Fin 0).toSubtype := fun x ↦ by absurd x.property; simp [h2]
    have f_bij : Function.Bijective f := by
      constructor
      · intro x1 _ _
        absurd x1.property
        simp [h2]
      · intro y
        obtain ⟨x, _⟩ := (mem_Fin _ _).mp y.property
        linarith
    have := h1 f
    contradiction

/--
引理 3.6.9

假设$`n ≥ 1`，且$`X`的基数为$`n`，如果$`x`是$`X`中任意一个元素，那么集合$`X - \{x\}`（即$`X`中去掉$`x`之后剩下的元素构成的集合）的基数为$`n - 1`.
-/
theorem SetTheory.Set.card_erase {n : ℕ} (h : n ≥ 1) {X : Set} (hX : X.has_card n) (x : X) :
    (X \ {x.val}).has_card (n - 1) := by
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨y, by aesop⟩
  observe hι : ∀ x : X', (ι x : Object) = x
  choose m0 hm0 hm0f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n - 1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x') : ℕ) ≠ m0 := by
      by_contra; simp [← this, Subtype.val_inj, hf.1.eq_iff, ι] at hm0f
      have := x'.property; aesop
    if h' : f (ι x') < m0 then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x' : X') : if (f (ι x') : ℕ) < m0 then (g x' : ℕ) = f (ι x') else (g x' : ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g, h']
  have hg : Function.Bijective g := by
    constructor
    · intro x1 x2 h
      by_cases h1 : f (ι x1) < m0 <;>
      by_cases h2 : f (ι x2) < m0 <;>
      have hg1 := hg_def x1 <;>
      simp [h1, h] at hg1 <;>
      have hg2 := hg_def x2 <;>
      simp [h2, hg1, ι] at hg2 <;>
      generalize_proofs hx1 hx2 at hg2 <;>
      simp at hm0f <;>
      (have : f ⟨x1, hx1⟩ ≠ f x := by
        by_contra
        have := hf.1 this
        have := x1.property
        rw [mem_sdiff] at this
        have := this.2
        simp at this
        have : ⟨x1, hx1⟩ ≠ x := by grind
        contradiction) <;>
      have : f ⟨x2, hx2⟩ ≠ f x := by
        by_contra
        have := hf.1 this
        have := x2.property
        rw [mem_sdiff] at this
        have := this.2
        simp at this
        have : ⟨x2, hx2⟩ ≠ x := by grind
        contradiction
      · rw [← Fin.coe_inj] at hg2
        have := hf.1 hg2; aesop
      · have : (f x : ℕ) ≤ f ⟨x2, hx2⟩ - 1 := by grind
        linarith
      · have : (f x : ℕ) ≤ f ⟨x1, hx1⟩ - 1 := by grind
        linarith
      · have : (f x : ℕ) < f ⟨x1, hx1⟩ := by grind
        have : (f x : ℕ) < f ⟨x2, hx2⟩ := by grind
        have := hf.1 (show f ⟨x1, hx1⟩ = f ⟨x2, hx2⟩ by grind)
        simp at this; aesop
    · intro y
      by_cases h : y < m0
      · let a := (Equiv.ofBijective f hf).symm (Fin_embed (n - 1) n (by simp) y)
        have ha : (y : ℕ) = f a := by
          have := (Equiv.ofBijective f hf).right_inv (Fin_embed (n - 1) n (by simp) y)
          change f a = Fin_embed (n - 1) n (by simp) y at this
          simp [this]
        use ⟨a, by
          rw [mem_sdiff]
          constructor
          · exact a.property
          · by_contra h
            simp at hm0f; aesop
        ⟩
        simp [g, ι, ← ha, h]
      · let a := (Equiv.ofBijective f hf).symm (Fin_mk n (y + 1 : ℕ) (by grind))
        have ha : (y + 1 : ℕ) = f a := by
          have := (Equiv.ofBijective f hf).right_inv (Fin_mk n (y + 1 : ℕ) (by grind))
          change f a = Fin_mk n (y + 1 : ℕ) (by grind) at this
          simp [this]
        use ⟨a, by
          rw [mem_sdiff]
          constructor
          · exact a.property
          · by_contra h
            simp at hm0f
            rw [mem_singleton] at h
            rw [show a = x by grind, hm0f] at ha
            linarith
        ⟩
        simp [g, ι, ← ha, show ¬y + (1 : ℕ) < m0 by grind]
  use g

/--
命题 3.6.8 基数的唯一性

设$`X`是一个基数为$`n`的集合，那么$`X`不可能还有任何其他基数。
也就是说，对任意的$`m ≠ n`，$`m`不可能是$`X`的基数。
-/
theorem SetTheory.Set.card_uniq {X : Set} {n m : ℕ} (h1 : X.has_card n) (h2 : X.has_card m) : n = m := by
  revert X m; induction' n with n hn
  · intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨_, hx⟩) (card_erase ?_ h2 ⟨_, hx⟩) <;> omega

/--
例 3.6.11
-/
lemma SetTheory.Set.Example_3_6_8_a : ({0, 1, 2} : Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2} : Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b : ({3, 4} : Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3 : Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0 : ℕ) ∨ y = (1 : ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0, 1, 2} : Set) ≈ ({3, 4} : Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

/--
定义 3.6.10 有限集

一个集合是*有限*的，当且仅当它的基数是某个自然数$`n`；否则，我们称该集合为*无限*的。
-/
abbrev SetTheory.Set.finite (X : Set) : Prop := ∃ n : ℕ, X.has_card n
abbrev SetTheory.Set.infinite (X : Set) : Prop := ¬ finite X

/--
习题 3.6.3
-/
theorem SetTheory.Set.bounded_on_finite {n : ℕ} (f : Fin n → nat) : ∃ M, ∀ i, (f i : ℕ) ≤ M := by
  induction' n with n hn
  · use 0
    intro i
    obtain ⟨_, h⟩ := (mem_Fin _ _).mp i.property
    omega
  · obtain ⟨M, hM⟩ := hn fun x ↦ f (Fin_embed n (n + 1) (by simp) x)
    use M + f (Fin_mk (n + 1) n (by simp))
    intro i
    by_cases h : i < n
    · have := hM (Fin_mk n i h)
      grind
    · grind

/--
定理 3.6.12

自然数集$`ℕ`是无限的
-/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M + 1); contrapose! hf
  intro a; have hi := hM a; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
noncomputable def SetTheory.Set.card (X : Set) : ℕ := if h : X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X : Set} (hX : X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X : Set} {n : ℕ} : X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨n, h⟩ : X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X : Set} {n : ℕ} (hn : n ≠ 0) : X.card = n → X.has_card n := by
  simp [card]; intro h
  by_cases hX : X.finite <;> simp [hX] at h
  · exact h ▸ hX.choose_spec
  · simp [h] at hn

theorem SetTheory.Set.card_fin_eq (n : ℕ) : (Fin n).has_card n := (has_card_iff _ _).mp ⟨id, Function.bijective_id⟩

theorem SetTheory.Set.Fin_card (n : ℕ) : (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n : ℕ) : (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y : Set} {n : ℕ} (h : X ≈ Y) : X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  · use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  · use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y : Set} (h : X ≈ Y) : X.card = Y.card := by
  by_cases hX : X.finite <;> by_cases hY : Y.finite <;> rw [finite] at hX hY
  · choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  · choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  · choose nY hYn using hY; rw [← EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/--
习题 3.6.2
-/
theorem SetTheory.Set.empty_iff_card_eq_zero {X : Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  simp [← has_card_zero]
  constructor
  · intro h
    exact ⟨⟨0, h⟩, has_card_to_card h⟩
  · intro ⟨h1, h2⟩
    exact h2 ▸ has_card_card h1

lemma SetTheory.Set.empty_of_card_eq_zero {X : Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X : Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X : Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅ : Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅ : Set).card = 0 := card_eq_zero_of_empty rfl

/--
习题 3.6.4
-/
theorem SetTheory.Set.card_insert {X : Set} (hX : X.finite) {x : Object} (hx : x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  obtain ⟨n, hXn⟩ := hX
  rw [has_card_iff] at hXn
  obtain ⟨f, hf⟩ := hXn
  let g := open Classical in fun i : (X ∪ {x} : Set) ↦
    if h : i.val ∈ X then
      Fin_embed n (n + 1) (by simp) (f ⟨i.val, h⟩)
    else
      Fin_mk (n + 1) n (by simp)
  have g_bijective : Function.Bijective g := by
    constructor
    · intro x1 x2 h
      by_cases hx1 : x1.val ∈ X <;>
      by_cases hx2 : x2.val ∈ X <;>
      simp [g, hx1, hx2] at h
      · have := hf.1
        grind
      · grind
      · have : n = (f ⟨x2, hx2⟩ : ℕ) := by
          rw [← Object.natCast_inj _ _]
          simp_all only [Fin.coe_toNat]
        have := Fin.toNat_lt (f ⟨x2, hx2⟩)
        omega
      · aesop
    · intro y
      by_cases h : n = y
      · use ⟨x, by aesop⟩
        simpa [g, hx]
      · obtain ⟨x, hx⟩ := hf.2 ⟨y, by rw [mem_Fin]; grind⟩
        use ⟨x, by aesop⟩
        simp_all only [g, x.property, Fin.coe_inj]
  constructor
  · use n + 1
    rw [has_card_iff]
    exact ⟨g, g_bijective⟩
  · rw [has_card_to_card ((has_card_iff _ _).mpr ⟨f, hf⟩)]
    apply has_card_to_card
    rw [has_card_iff]
    exact ⟨g, g_bijective⟩

section helpers
-- 一些有用的引理
lemma SetTheory.Set.sdiff_union {X : Set} {x : Object} (hx : x ∈ X) : X \ {x} ∪ {x} = X := by
  ext x'
  refine ⟨by aesop, ?_⟩
  intro hx; simp [mem_union, mem_sdiff]
  by_cases hxy : x' = x
  · right; assumption
  · left; exact ⟨hx, hxy⟩

lemma SetTheory.Set.sdiff_subset {X Y : Set} {x : Object} (hXY : X ⊆ Y) :
    X \ {x} ⊆ Y \ {x} := by
  intro x' hx'
  simp_all [mem_sdiff]
  apply hXY
  exact hx'.1

lemma SetTheory.Set.sdiff_ssubset {X Y : Set} {x : Object} (hX : x ∈ X) (hY : x ∈ Y) (hXY : X ⊂ Y) :
    X \ {x} ⊂ Y \ {x} := by
  constructor
  · exact sdiff_subset hXY.1
  · by_contra
    have : X = Y := by
      ext x'
      constructor <;> intro hx'
      · exact hXY.1 _ hx'
      by_cases h : x = x'
      · simpa [← h]
      · have : x' ∈ X \ {x} := by aesop
        simp at this
        exact this.1
    have := hXY.2
    contradiction

lemma SetTheory.Set.image_of_empty {X Y : Set} (f : X → Y) (hX : X.has_card 0) : image f X = ∅ := by
  by_contra!
  obtain ⟨y, hy⟩ := nonempty_def this
  simp at hy
  obtain ⟨x, ⟨h1, _⟩⟩ := hy
  have := empty_of_card_eq_zero ⟨0, hX⟩ (has_card_to_card hX)
  have := this ▸ not_mem_empty x
  contradiction

lemma SetTheory.Set.singleton_card {x : Object} : ({x} : Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk 1 0 (by simp)
  constructor
  · intro x1 x2 _
    have h1 := x1.property
    have h2 := x2.property
    simp at h1 h2
    ext; simp [h1, h2]
  · intro y
    use ⟨x, by simp⟩
    simp
    have := Fin.toNat_lt y
    grind only

lemma SetTheory.Set.image_singleton_card {X Y : Set} (f : X → Y) {x : Object} (hx : x ∈ X) :
    (image f {x}).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk 1 0 (by simp)
  constructor
  · intro x1 x2 _
    have := x1.property
    simp at this
    obtain ⟨_, h1⟩ := this
    have := x2.property
    simp at this
    obtain ⟨_, h2⟩ := this
    rw [h1] at h2
    ext; assumption
  · intro y
    use ⟨f ⟨x, hx⟩, by aesop⟩
    simp
    have := Fin.toNat_lt y
    grind only

end helpers

theorem SetTheory.Set.card_union {X Y : Set} (hX : X.finite) (hY : Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  obtain ⟨nY, _⟩ := hY
  revert Y
  induction' nY with nY h <;> intro Y hY
  · rw [has_card_zero] at hY; simpa [hY]
  · have : Y ≠ ∅ := by
      by_contra
      have := card_uniq hY ((card_eq_zero_of_empty this) ▸ has_card_card ⟨nY + 1, hY⟩)
      linarith
    obtain ⟨y, hy⟩ := nonempty_def this
    have hCard := card_erase (by simp) hY ⟨y, hy⟩
    obtain ⟨h1, h2⟩ := h hCard
    by_cases hy' : y ∈ X
    · have : X ∪ Y \ {y} = X ∪ Y := by
        ext x
        refine ⟨by aesop, ?_⟩
        intro hx; rw [mem_union] at *
        rcases hx with (hx | hx)
        · left; assumption
        · by_cases hxy : y = x
          · rw [hxy] at hy'
            left; assumption
          · right; aesop
      rw [← this]
      constructor
      · assumption
      · trans X.card + (Y \ {y}).card
        · assumption
        · simp [has_card_to_card hCard, has_card_to_card hY]
    · have : X ∪ Y \ {y} ∪ {y} = X ∪ Y := by
        rw [union_assoc, sdiff_union hy]
      rw [← this]
      obtain ⟨_, _⟩ := card_insert h1 (x := y) (by simpa)
      constructor
      · assumption
      · have := sdiff_union hy
        have := card_insert ⟨nY, hCard⟩ (x := y) (by simp)
        grind -- using this and h2

theorem SetTheory.Set.card_union_disjoint {X Y : Set} (hX : X.finite) (hY : Y.finite)
    (hdisj : Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  obtain ⟨nY, _⟩ := hY
  revert Y
  induction' nY with nY h <;> intro Y hdisj hY
  · rw [has_card_zero] at hY; simp [hY]
  · by_cases hempty : X = ∅
    · simp [hempty]
    have : Y ≠ ∅ := by
      by_contra
      have := card_uniq hY ((card_eq_zero_of_empty this) ▸ has_card_card ⟨nY + 1, hY⟩)
      linarith
    obtain ⟨y, hy⟩ := nonempty_def this
    have hCard := card_erase (by simp) hY ⟨y, hy⟩
    have hdisj' : Disjoint X (Y \ {y}) := by
      rw [disjoint_iff]
      by_contra!
      have : X ∩ Y ≠ ∅ := by
        obtain ⟨x, hx⟩ := nonempty_def this
        rw [mem_inter, mem_sdiff] at hx
        apply nonempty_of_inhabited (x := x)
        rw [mem_inter]; exact ⟨hx.1, hx.2.1⟩
      rw [disjoint_iff] at hdisj
      contradiction
    rw [← sdiff_union hy, ← union_assoc]
    have := card_insert ⟨nY, hCard⟩ (x := y) (by simp)
    have : X.card ≠ 0 := by
      by_contra
      have := empty_of_card_eq_zero hX this
      contradiction
    let card := X.card + (Y \ {y}).card
    have := card_to_has_card (X := X ∪ Y \ {y}) (n := card) (by aesop) (h (hdisj') hCard)
    have := card_insert ⟨card, this⟩ (x := y) (by
      simp; by_contra
      have : y ∈ X ∩ Y := by aesop
      have := nonempty_of_inhabited this
      rw [disjoint_iff] at hdisj
      contradiction
    )
    grind

theorem SetTheory.Set.card_subset {X Y : Set} (hX : X.finite) (hY : Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  obtain ⟨nX, _⟩ := hX
  revert X Y
  induction' nX with nX h <;> intro X Y hY hnX
  · have := empty_of_card_eq_zero ⟨0, hnX⟩ (has_card_to_card hnX)
    have : Y = ∅ := by
      by_contra!
      obtain ⟨y, hy⟩ := nonempty_def this
      have := hY _ hy
      aesop
    constructor <;> simp [this]
  · have : X ≠ ∅ := by
      by_contra
      have := card_uniq hnX ((card_eq_zero_of_empty this) ▸ has_card_card ⟨nX + 1, hnX⟩)
      linarith
    obtain ⟨x, hx⟩ := nonempty_def this
    by_cases hxY : x ∈ Y
    · have hX'card := card_erase (by simp) hnX ⟨x, hx⟩
      have := h (sdiff_subset hY) hX'card
      rw [← sdiff_union hx, ← sdiff_union hxY]
      have hY' := card_insert this.1 (x := x) (by aesop)
      have hX' := card_insert ⟨nX, hX'card⟩ (x := x) (by aesop)
      constructor
      · exact hY'.1
      · rw [hY'.2, hX'.2]
        simp_all
    · have hX'card := card_erase (by simp) hnX ⟨x, hx⟩
      have := card_insert ⟨nX, hX'card⟩ (x := x) (by aesop)
      have := h (show Y ⊆ X \ {x} by intro x' hx'; aesop) hX'card
      rw [← sdiff_union hx]
      constructor
      · exact this.1
      · trans (X \ {x}).card
        · exact this.2
        · simp_all

theorem SetTheory.Set.card_ssubset {X Y : Set} (hX : X.finite) (hY : Y ⊂ X) :
    Y.card < X.card := by
  obtain ⟨nX, _⟩ := hX
  revert X Y
  induction' nX with nX h <;> intro X Y hY hnX
  · rw [ssubset_def, empty_of_card_eq_zero ⟨0, hnX⟩ (has_card_to_card hnX)] at hY
    have : Y = ∅ := by
      by_contra!
      obtain ⟨y, hy⟩ := nonempty_def this
      have := hY.1 _ hy
      aesop
    have := hY.2
    contradiction
  · have : X ≠ ∅ := by
      by_contra
      have := card_uniq hnX ((card_eq_zero_of_empty this) ▸ has_card_card ⟨nX + 1, hnX⟩)
      linarith
    obtain ⟨x, hx⟩ := nonempty_def this
    rw [ssubset_def] at hY
    by_cases hxY : x ∈ Y
    · have hX'card := card_erase (by simp) hnX ⟨x, hx⟩
      have := h (sdiff_ssubset hxY hx hY) hX'card
      rw [← sdiff_union hx, ← sdiff_union hxY]
      have hY' := card_insert (card_subset ⟨nX, hX'card⟩ (sdiff_ssubset hxY hx hY).1).1 (x := x) (by aesop)
      have hX' := card_insert ⟨nX, hX'card⟩ (x := x) (by aesop)
      rw [hX'.2, hY'.2]
      simp_all
    · by_cases hYempty : Y = ∅
      · rw [card_eq_zero_of_empty, has_card_to_card hnX]
        simp; assumption
      · obtain ⟨y, hy⟩ := nonempty_def hYempty
        have hyX := hY.1 _ hy
        have hX'card := card_erase (by simp) hnX ⟨y, hyX⟩
        have := h (sdiff_ssubset hy hyX hY) hX'card
        rw [← sdiff_union hy, ← sdiff_union hyX]
        have hY' := card_insert (card_subset ⟨nX, hX'card⟩ (sdiff_ssubset hy hyX hY).1).1 (x := y) (by aesop)
        have hX' := card_insert ⟨nX, hX'card⟩ (x := y) (by aesop)
        rw [hX'.2, hY'.2]
        simp_all

theorem SetTheory.Set.card_image {X Y : Set} (hX : X.finite) (f : X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  obtain ⟨nX, _⟩ := hX
  revert X
  induction' nX with nX h <;> intro X f hX
  · constructor <;> simp [image_of_empty f hX]
  · have : X ≠ ∅ := by
      by_contra
      have := card_uniq hX ((card_eq_zero_of_empty this) ▸ has_card_card ⟨nX + 1, hX⟩)
      linarith
    obtain ⟨x, hx⟩ := nonempty_def this
    let X' := X \ {x}
    have h1 := h (X := X') (fun x ↦ f ⟨x.val, by aesop⟩) (card_erase (by simp) hX ⟨x, hx⟩)
    have h2 : image (X := X') (fun x ↦ f ⟨x.val, by aesop⟩) X' = image f X' := by
      ext x
      refine ⟨?_, by aesop⟩
      intro hx
      simp_all
      obtain ⟨a, ⟨h1, h2⟩⟩ := hx
      use a, (by grind only)
    rw [h2] at h1
    nth_rw 2 4 5 [← sdiff_union hx]
    rw [image_of_union]
    have := card_union h1.1 ⟨1, image_singleton_card f hx⟩
    constructor
    · exact this.1
    · trans (image f X').card + (image f {x}).card
      · exact this.2
      · rw [has_card_to_card (image_singleton_card f hx), card_union_disjoint ⟨nX, card_erase (by simp) hX ⟨x, hx⟩⟩ ⟨1, singleton_card⟩ (by rw [disjoint_iff]; aesop), has_card_to_card singleton_card]
        grind only

theorem SetTheory.Set.card_image_inj {X Y : Set} (hX : X.finite) {f : X → Y}
    (hf : Function.Injective f) : (image f X).card = X.card := by
  obtain ⟨nX, _⟩ := hX
  revert X
  induction' nX with nX h <;> intro X f hf hX
  · simp [image_of_empty f hX, has_card_to_card hX]
  · have : X ≠ ∅ := by
      by_contra
      have := card_uniq hX ((card_eq_zero_of_empty this) ▸ has_card_card ⟨nX + 1, hX⟩)
      linarith
    obtain ⟨x, hx⟩ := nonempty_def this
    let X' := X \ {x}
    have h1 := h (X := X') (f := fun x ↦ f ⟨x.val, by aesop⟩) (by
      intro x1 x2 h
      have := hf h
      simp at this
      ext; assumption
    ) (card_erase (by simp) hX ⟨x, hx⟩)
    have h2 : image (X := X') (fun x ↦ f ⟨x.val, by aesop⟩) X' = image f X' := by
      ext x
      refine ⟨?_, by aesop⟩
      intro hx
      simp_all
      obtain ⟨a, ⟨h1, h2⟩⟩ := hx
      use a, (by grind only)
    rw [h2] at h1
    nth_rw 2 3 [← sdiff_union hx]
    rw [image_of_union]
    have := card_union_disjoint (card_image ⟨nX, card_erase (by simp) hX ⟨x, hx⟩⟩ fun x ↦ f ⟨x.val, by aesop⟩).1 ⟨1, image_singleton_card f hx⟩ (by
      rw [disjoint_iff]
      by_contra!
      obtain ⟨a, ha⟩ := nonempty_def this
      obtain ⟨ha1, ha2⟩ := (mem_inter _ _ _).mp ha
      simp at ha2
      simp at ha1
      grind
    )
    simp [h2, X'] at this
    rw [this, card_union_disjoint ⟨nX, card_erase (by simp) hX ⟨x, hx⟩⟩ ⟨1, singleton_card⟩ (by rw [disjoint_iff]; aesop), has_card_to_card singleton_card, has_card_to_card (image_singleton_card f hx)]
    simp [h1, X']

theorem SetTheory.Set.card_prod {X Y : Set} (hX : X.finite) (hY : Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  obtain ⟨nX, ⟨f, hf⟩⟩ := hX
  obtain ⟨nY, ⟨g, hg⟩⟩ := hY
  let h' (z : X ×ˢ Y) : Fin (nX * nY) := Fin_mk (nX * nY) (f (fst z) * nY + g (snd z)) (by
    calc f (fst z) * nY + g (snd z)
      < f (fst z) * nY + nY := add_lt_add_right (Fin.toNat_lt _) _
    _ = (f (fst z) + 1) * nY := by nth_rw 2 [← one_mul nY]; rw [← add_mul]
    _ ≤ nX * nY := mul_le_mul_left (Fin.toNat_lt _) nY
  )
  have h'Bijective : Function.Bijective h' := by
    constructor
    · intro x1 x2 h
      simp at h
      by_cases hnY : nY = 0
      · subst hnY
        have := x1.property
        simp [empty_of_card_eq_zero ⟨0, ⟨g, hg⟩⟩ (has_card_to_card ⟨g, hg⟩)] at this
      · let m := g (snd x1) + nY * f (fst x1)
        have hm : g (snd x2) + nY * f (fst x2) = m := by rw [add_comm, mul_comm, ← h, add_comm, mul_comm]
        have h1 := (Nat.div_mod_unique (by omega)).mpr ⟨hm, Fin.toNat_lt _⟩
        have h2 := (Nat.div_mod_unique (by omega)).mpr ⟨show g (snd x1) + nY * f (fst x1) = m by rfl, Fin.toNat_lt _⟩
        have h1' := hf.1 (show f (fst x1) = f (fst x2) by simp [← h1.1, ← h2.1])
        have h2' := hg.1 (show g (snd x1) = g (snd x2) by simp [← h1.2, ← h2.2])
        grind
    · intro y
      have hy := Fin.toNat_lt y
      by_cases hnY : nY = 0
      · subst hnY
        linarith
      · let x' := (Equiv.ofBijective f hf).invFun (Fin_mk nX (y / nY) (by rwa [← Nat.div_lt_div_right hnY (by simp), Nat.mul_div_cancel nX (by omega)] at hy))
        let y' := (Equiv.ofBijective g hg).invFun (Fin_mk nY (y % nY) (Nat.mod_lt y (show 0 < nY by omega)))
        use mk_cartesian x' y'; simp
        change (Equiv.ofBijective f hf).toFun ((Equiv.ofBijective f hf).invFun _) * nY + (Equiv.ofBijective g hg).toFun ((Equiv.ofBijective g hg).invFun _) = y
        rw [(Equiv.ofBijective f hf).right_inv, (Equiv.ofBijective g hg).right_inv]; simp
        rw [mul_comm]; apply Nat.div_add_mod
  constructor
  · use nX * nY, h'
  · rw [has_card_to_card ⟨f, hf⟩, has_card_to_card ⟨g, hg⟩, has_card_to_card ⟨h', h'Bijective⟩]

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun x := ((powerset_axiom x).mp x.property).choose
  invFun f := ⟨f, (powerset_axiom f).mpr ⟨f, by rfl⟩⟩
  left_inv x := by simp [((powerset_axiom x).mp x.property).choose_spec]
  right_inv f := by simp

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [← pow_fun_equiv.apply_eq_iff_eq]

theorem SetTheory.Set.card_pow {X Y : Set} (hY : Y.finite) (hX : X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
  obtain ⟨nX, _⟩ := hX
  obtain ⟨nY, ⟨fy, hfy⟩⟩ := hY
  revert X
  induction' nX with nX h <;> intro X hX
  · simp [empty_of_card_eq_zero ⟨0, hX⟩ (has_card_to_card hX)]
    have : (Y ^ (∅ : Set)).has_card 1 := by
      rw [has_card_iff]
      use fun _ ↦ Fin_mk 1 0 (by simp)
      constructor
      · intro _ _ _
        rw [pow_fun_eq_iff]
        ext x
        have := x.property
        have := not_mem_empty x
        contradiction
      · intro y
        let f (x : (∅ : Set)) : Y := by
          have := x.property
          have := not_mem_empty x
          contradiction
        use pow_fun_equiv.invFun f
        grind [Fin.toNat_lt y]
    exact ⟨⟨1, this⟩, has_card_to_card this⟩
  · have : X ≠ ∅ := by
      by_contra
      have := card_uniq hX ((card_eq_zero_of_empty this) ▸ has_card_card ⟨nX + 1, hX⟩)
      linarith
    obtain ⟨x, hx⟩ := nonempty_def this
    let X' := X \ {x}
    have := h (card_erase (by simp) hX ⟨x, hx⟩)
    obtain ⟨n', ⟨g, hg⟩⟩ := this.1
    let f' (x' : ↑(Y ^ X)) : Fin (n' * nY) := by
      let x'' (i : X') : Y := pow_fun_equiv x' ⟨i, ((mem_sdiff _ _ _).mp i.property).1⟩
      let j := fy (pow_fun_equiv x' ⟨x, hx⟩)
      let base := g (pow_fun_equiv.symm x'')
      exact ⟨base * nY + (j : ℕ), by
        rw [mem_Fin]
        use base * nY + j; simp
        calc base * nY + j
          < base * nY + nY := add_lt_add_right (Fin.toNat_lt _) _
        _ = (base + 1) * nY := by nth_rw 2 [← one_mul nY]; rw [← add_mul]
        _ ≤ n' * nY := mul_le_mul_left (Fin.toNat_lt _) nY
      ⟩
    have f'Bijective : Function.Bijective f' := by
      constructor
      · intro x1 x2 h
        simp [f', pow_fun_equiv] at h
        generalize_proofs h1 h2 h3 h4 h5 at h
        by_cases hnY : nY = 0
        subst hnY
        · have := x1.property
          simp [empty_of_card_eq_zero ⟨0, ⟨fy, hfy⟩⟩ (has_card_to_card ⟨fy, hfy⟩)] at this
          obtain ⟨f, _⟩ := this
          have := (f ⟨x, hx⟩).property
          have := not_mem_empty (f ⟨x, hx⟩)
          contradiction
        · let m := fy (h1.choose ⟨x, hx⟩) + nY * g ⟨fun i : X' ↦ h1.choose ⟨i, h2 i⟩, h3⟩
          have hm : fy (h4.choose ⟨x, hx⟩) + nY * g ⟨fun i : X' ↦ h4.choose ⟨i, h2 i⟩, h5⟩ = m := by rw [add_comm, mul_comm, ← h, add_comm, mul_comm]
          have h1' := (Nat.div_mod_unique (by omega)).mpr ⟨hm, Fin.toNat_lt _⟩
          have h2' := (Nat.div_mod_unique (by omega)).mpr ⟨show fy (h1.choose ⟨x, hx⟩) + nY * g ⟨fun i : X' ↦ h1.choose ⟨i, h2 i⟩, h3⟩ = m by rfl, Fin.toNat_lt _⟩
          have h1'' := hg.1 (show g ⟨fun i : X' ↦ h4.choose ⟨i, h2 i⟩, h5⟩ = g ⟨fun i : X' ↦ h1.choose ⟨i, h2 i⟩, h3⟩ by simp [← h1'.1, ← h2'.1])
          have h2'' := hfy.1 (show fy (h4.choose ⟨x, hx⟩) = fy (h1.choose ⟨x, hx⟩) by simp [← h1'.2, ← h2'.2])
          have : h1.choose = h4.choose := by
            ext i
            by_cases hi : i = x
            · subst hi
              rw [h2''.symm]
            · have : i.val ∈ X' := by
                rw [mem_sdiff]; simp
                exact ⟨i.property, hi⟩
              have : h1.choose ⟨i, h2 ⟨i, this⟩⟩ = h4.choose ⟨i, h2 ⟨i, this⟩⟩ := by
                change (fun i : X' ↦ h1.choose ⟨i, h2 i⟩) ⟨i, this⟩ = (fun i : X' ↦ h4.choose ⟨i, h2 i⟩) ⟨i, this⟩
                rw [show (fun i : X' ↦ h1.choose ⟨i, h2 i⟩) = fun i : X' ↦ h4.choose ⟨i, h2 i⟩ by simp_all]
              simp only [this]
          ext; rw [← h1.choose_spec, ← h4.choose_spec]; simpa
      · intro y
        have hy := Fin.toNat_lt y
        by_cases hnY : nY = 0
        · subst hnY
          linarith
        · let j := (Equiv.ofBijective fy hfy).invFun (Fin_mk nY (y % nY) (Nat.mod_lt y (show 0 < nY by omega)))
          let base := (Equiv.ofBijective g hg).invFun (Fin_mk n' (y / nY) (by rwa [← Nat.div_lt_div_right hnY (by simp), Nat.mul_div_cancel n' (by omega)] at hy))
          open Classical in
          let f (i : X) := if h : i.val = x then j else (pow_fun_equiv base ⟨i, by simp; exact ⟨i.property, h⟩⟩)
          use pow_fun_equiv.symm f
          simp [f, f']
          congr; symm; rw [Fin.coe_eq_iff]
          have : (fun i : X' ↦ if i = x then j else pow_fun_equiv base i) = fun i : X' ↦ pow_fun_equiv base i := by
            ext i; simp [show ¬i.val = x by aesop]
          simp [this]
          change y = (g (pow_fun_equiv.invFun (pow_fun_equiv.toFun base)) : ℕ) * nY + fy j
          rw [pow_fun_equiv.left_inv]; simp [base, j]
          generalize_proofs h1 h2
          change y = ((Equiv.ofBijective g hg).toFun ((Equiv.ofBijective g hg).invFun (Fin_mk n' (y / nY) h1)) : ℕ) * nY + (Equiv.ofBijective fy hfy).toFun ((Equiv.ofBijective fy hfy).invFun (Fin_mk nY (y % nY) h2))
          rw [(Equiv.ofBijective g hg).right_inv, (Equiv.ofBijective fy hfy).right_inv]; simp
          symm; rw [mul_comm]; apply Nat.div_add_mod
    constructor
    · use n' * nY, f'
    · nth_rw 2 [← sdiff_union hx]
      rw [has_card_to_card ⟨f', f'Bijective⟩, ← has_card_to_card ⟨g, hg⟩, ← has_card_to_card ⟨fy, hfy⟩, card_union_disjoint ⟨nX, (card_erase (by simp) hX ⟨x, hx⟩)⟩ ⟨1, singleton_card⟩ (by rw [disjoint_iff]; aesop), has_card_to_card singleton_card]
      grind

/--
习题 3.6.5
-/
theorem SetTheory.Set.prod_EqualCard_prod (A B : Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
  let f := prod_commutator A B
  exact ⟨f, f.bijective⟩

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A := A) (B := B)

/--
习题 3.6.6
-/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C : Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
  let e1 : (C → (A ^ B : Set)) ≃ (C → B → A) := {
    toFun f c := (SetTheory.Set.pow_fun_equiv' A B).toFun (f c)
    invFun f c := (SetTheory.Set.pow_fun_equiv' A B).invFun (f c)
    left_inv _ := by simp
    right_inv _ := by simp
  }
  let e2 : (C ×ˢ B → A) ≃ (B ×ˢ C → A) := {
    toFun f b := f ((prod_commutator B C).toFun b)
    invFun f c := f ((prod_commutator B C).invFun c)
    left_inv _ := by simp
    right_inv _ := by simp
  }
  let f : ((A ^ B) ^ C : Set) ≃ (A ^ (B ×ˢ C) : Set) :=
    calc ((A ^ B) ^ C : Set)
      ≃ (C → (A ^ B : Set)) := pow_fun_equiv' (A ^ B) C
    _ ≃ (C → B → A) := e1
    _ ≃ (C ×ˢ B → A) := curry_equiv
    _ ≃ (B ×ˢ C → A) := e2
    _ ≃ (A ^ (B ×ˢ C) : Set) := (pow_fun_equiv' A (B ×ˢ C)).symm
  exact ⟨f, f.bijective⟩

theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c : ℕ) : (a ^ b) ^ c = a ^ (b * c) := by
  let A := Fin a
  let B := Fin b
  let C := Fin c
  have h1 : ((A ^ B) ^ C : Set).has_card ((a ^ b) ^ c : ℕ) := by
    have hab := card_pow (Fin_finite a) (Fin_finite b)
    have habc := card_pow hab.1 (Fin_finite c)
    have := has_card_card habc.1
    rwa [habc.2, hab.2, Fin_card a, Fin_card b, Fin_card c] at this
  have h2 : (A ^ (B ×ˢ C)).has_card (a ^ (b * c)) := by
    have hbc := card_prod (Fin_finite b) (Fin_finite c)
    have habc := card_pow (Fin_finite a) hbc.1
    have := has_card_card habc.1
    rwa [habc.2, hbc.2, Fin_card a, Fin_card b, Fin_card c] at this
  have h1' := (pow_pow_EqualCard_pow_prod A B C).trans ((has_card_iff _ _).mp h2)
  exact card_uniq h1 h1'

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C : Set) (hd : Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
  let f : ((A ^ B) ×ˢ (A ^ C)) ≃ (A ^ (B ∪ C) : Set) := {
    toFun p := by
      let f1 := pow_fun_equiv (fst p)
      let f2 := pow_fun_equiv (snd p)
      open Classical in let g (x : (B ∪ C : Set)) : A := if h : x.val ∈ B then f1 ⟨x, h⟩ else f2 ⟨x, by aesop⟩
      exact pow_fun_equiv.symm g
    invFun g := by
      let g' := pow_fun_equiv g
      let f1 (x : B) : A := g' ⟨x, by aesop⟩
      let f2 (x : C) : A := g' ⟨x, by aesop⟩
      exact mk_cartesian (pow_fun_equiv.symm f1) (pow_fun_equiv.symm f2)
    left_inv x := by
      simp
      nth_rw 10 [← mk_cartesian_fst_snd_eq x]
      congr <;> simp [pow_fun_equiv]
      · generalize_proofs h1 h2 h3 h4
        have : (open Classical in fun x' : B ↦ if h : x'.val ∈ B then h2.choose x' else h3.choose ⟨x', h4 x' h⟩) = h2.choose := by
          ext i; simp [i.property]
        simp [this, h2.choose_spec]
      · generalize_proofs h1 h2 h3 h4
        have : (open Classical in fun x' : C ↦ if h : x'.val ∈ B then h2.choose ⟨x', h⟩ else h3.choose x') = h3.choose := by
          ext i
          have : ¬i.val ∈ B := by
            by_contra
            rw [disjoint_iff] at hd
            have : i.val ∈ (∅ : Set) := by
              rw [← hd]; simp [i.property, this]
            have := not_mem_empty i.val
            contradiction
          simp [this]
        simp [this, h3.choose_spec]
    right_inv _ := by simp
  }
  exact ⟨f, f.bijective⟩

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c : ℕ) : (a ^ b) * a ^ c = a ^ (b + c) := by
  let A := Fin a
  let B := Fin b
  let C := Fin c
  let C' := C.replace (P := fun c c' ↦ ∃ n : ℕ, n = c' ∧ n = (c : ℕ) + b) (by simp)
  have hC'ard : C'.has_card c := by
    let f (c' : C') : Fin c := by
      have := c'.property
      rw [replacement_axiom] at this
      exact this.choose
    use f
    constructor
    · intro x1 x2 h
      simp at h; grind
    · intro y
      use ⟨(y : ℕ) + b, by rw [replacement_axiom]; use y, y + b⟩
      simp [f]; grind
  have hdisj : Disjoint B C' := by
    rw [disjoint_iff]
    by_contra! h
    have := nonempty_def h
    aesop
  have h1 : ((A ^ B) ×ˢ (A ^ C')).has_card ((a ^ b) * a ^ c) := by
    have hab := card_pow (Fin_finite a) (Fin_finite b)
    have hac := card_pow (Fin_finite a) ⟨c, hC'ard⟩
    have habac := card_prod hab.1 hac.1
    have := has_card_card habac.1
    rwa [habac.2, hab.2, hac.2, Fin_card a, Fin_card b, has_card_to_card hC'ard] at this
  have h2 : (A ^ (B ∪ C')).has_card (a ^ (b + c)) := by
    have hbc := card_union_disjoint (Fin_finite b) ⟨c, hC'ard⟩ hdisj
    have habc := card_pow (Fin_finite a) (card_union (Fin_finite b) ⟨c, hC'ard⟩).1
    have := has_card_card habc.1
    rwa [habc.2, hbc, Fin_card a, Fin_card b, has_card_to_card hC'ard] at this
  have h1' := (pow_prod_pow_EqualCard_pow_union A B C' hdisj).trans ((has_card_iff _ _).mp h2)
  exact card_uniq h1 h1'

/--
习题 3.6.7
-/
theorem SetTheory.Set.injection_iff_card_le {A B : Set} (hA : A.finite) (hB : B.finite) :
    (∃ f : A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  constructor
  · intro ⟨f, hf⟩
    have h1 := card_image_inj hA hf
    have h2 := image_in_codomain f A
    have h3 := (card_subset hB h2).2
    rwa [h1] at h3
  · intro h
    have h1 := has_card_card hA
    have h2 := has_card_card hB
    rw [has_card_iff] at h1 h2
    obtain ⟨f, hf⟩ := h1
    obtain ⟨g, hg⟩ := h2
    use fun x ↦ (Equiv.ofBijective g hg).invFun (Fin_embed A.card B.card h (f x))
    intro x1 x2 hx
    simp at hx
    have : f x1 = f x2 := by grind only
    exact hf.1 this

/--
习题 3.6.8
-/
theorem SetTheory.Set.surjection_from_injection {A B : Set} (hA : A ≠ ∅) (f : A → B)
    (hf : Function.Injective f) : ∃ g : B → A, Function.Surjective g := by
  let B' := image f A
  obtain ⟨y', hy'⟩ := nonempty_def hA
  open Classical in
  use fun x ↦ if h : x.val ∈ B' then ((mem_image f A x).mp h).choose else ⟨y', hy'⟩
  intro y
  use f y
  have : (f y).val ∈ B' := by
    rw [mem_image]
    use y; simp
    exact y.property
  grind

/--
习题 3.6.9
-/
theorem SetTheory.Set.card_union_add_card_inter {A B : Set} (hA : A.finite) (hB : B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
  obtain ⟨nB, _⟩ := hB
  revert B
  induction' nB with nB h <;> intro B hB
  · rw [has_card_zero] at hB; simp [hB, show A ∩ ∅ = ∅ by aesop];
  · by_cases hAB : A ∩ B = ∅
    · have := card_union_disjoint hA ⟨nB + 1, hB⟩ ((disjoint_iff A B).mpr hAB)
      symm; simpa [hAB]
    have : B ≠ ∅ := by
      by_contra
      have := card_uniq hB ((card_eq_zero_of_empty this) ▸ has_card_card ⟨nB + 1, hB⟩)
      linarith
    obtain ⟨y, hy⟩ := nonempty_def hAB
    rw [mem_inter] at hy
    have hCard := card_erase (by simp) hB ⟨y, hy.2⟩
    rw [← sdiff_union hy.2, ← union_assoc, (card_insert ⟨nB, hCard⟩ (x := y) (by simp)).2, show A ∪ B \ {y} ∪ {y} = A ∪ B \ {y} by aesop, show A ∩ (B \ {y} ∪ {y}) = A ∩ (B \ {y}) ∪ {y} by aesop]
    have hfinite : (A ∩ (B \ {y})).finite := by
      have : A ∩ (B \ {y}) ⊆ B \ {y} := by
        intro x hx
        rw [mem_inter] at hx
        exact hx.2
      exact (card_subset ⟨nB, hCard⟩ this).1
    rw [(card_insert hfinite (x := y) (by simp)).2]
    grind

/--
习题 3.6.10
-/
lemma SetTheory.Set.iUnion_finite {n : ℕ} {A : Fin n → Set}
    (hA : ∀ i, (A i).finite) : (iUnion _ A).finite := by
  induction' n with n h
  · have : (iUnion _ A) = ∅ := by
      ext x
      refine ⟨?_, by simp⟩
      intro hx
      simp [iUnion, union_axiom] at hx
    simp [this]
  · let A' : Fin n → Set := fun i ↦ A (Fin_embed n (n + 1) (by simp) i)
    have hA' : ∀ i, (A' i).finite := by intro i; simp [A', hA]
    have h1 : (iUnion _ A) = (iUnion _ A') ∪ (A (Fin_mk (n + 1) n (by simp))) := by
        ext x
        simp [iUnion, union_axiom, A']
        constructor
        · intro ⟨a, ⟨h1a, h1b⟩, h2⟩
          by_cases h : nat_equiv.symm ⟨a, h1a⟩ = n
          · right
            generalize_proofs h3 at h2
            rwa [show Fin_mk (n + 1) n (by simp) = ⟨a, h3⟩ by aesop]
          · left
            use a, ⟨h1a, by grind⟩
        · rintro (⟨a, ⟨h1a, h1b⟩, h2⟩ | h)
          · use a, ⟨h1a, by grind⟩
          · use nat_equiv n, ⟨by grind, by grind⟩
            assumption
    have := (card_union (h hA') (hA (Fin_mk (n + 1) n (by simp)))).1
    rwa [← h1] at this

theorem SetTheory.Set.pigeonhole_principle {n : ℕ} {A : Fin n → Set}
    (hA : ∀ i, (A i).finite) (hAcard : (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
  induction' n with n hind
  · have : (iUnion _ A) = ∅ := by
      ext x
      refine ⟨?_, by simp⟩
      intro hx
      simp [iUnion, union_axiom] at hx
    rw [this] at hAcard
    have := empty_card_eq_zero
    linarith
  · by_contra! h
    let A' : Fin n → Set := fun i ↦ A (Fin_embed n (n + 1) (by simp) i)
    have hA' : ∀ i, (A' i).finite := by intro i; simp [A', hA]
    have hA'card : (iUnion _ A').card > n := by
      have h1 : (iUnion _ A) = (iUnion _ A') ∪ (A (Fin_mk (n + 1) n (by simp))) := by
        ext x
        simp [iUnion, union_axiom, A']
        constructor
        · intro ⟨a, ⟨h1a, h1b⟩, h2⟩
          by_cases h : nat_equiv.symm ⟨a, h1a⟩ = n
          · right
            generalize_proofs h3 at h2
            rwa [show Fin_mk (n + 1) n (by simp) = ⟨a, h3⟩ by aesop]
          · left
            use a, ⟨h1a, by grind⟩
        · rintro (⟨a, ⟨h1a, h1b⟩, h2⟩ | h)
          · use a, ⟨h1a, by grind⟩
          · use nat_equiv n, ⟨by grind, by grind⟩
            assumption
      have h2 := (card_union (iUnion_finite hA') (hA (Fin_mk (n + 1) n (by simp)))).2
      rw [← h1] at h2
      by_contra
      have : (iUnion _ A).card ≤ n + 1 := by nlinarith [h (Fin_mk (n + 1) n (by simp))]
      linarith
    obtain ⟨i, hi⟩ := hind hA' hA'card
    have := h (Fin_embed n (n + 1) (by simp) i)
    linarith

/--
习题 3.6.11
-/
theorem SetTheory.Set.two_to_two_iff {X Y : Set} (f : X → Y) : Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  constructor
  · intro finj S hS hSCard
    let f' : S → Y := fun i ↦ f ⟨i, hS _ i.property⟩
    have h1 : Function.Injective f' := by
      intro x1 x2 hx
      have := finj hx
      simp at this
      ext; assumption
    rw [← hSCard, show image f S = image f' S by aesop]
    exact card_image_inj ⟨2, (card_to_has_card (by simp) hSCard)⟩ h1
  · intro hS x1 x2 hx
    by_contra
    let S := ({x1.val, x2.val} : Set)
    have hSCard : S.card = 2 := by
      apply has_card_to_card
      open Classical in
      use fun i ↦ if h : i = x1.val then Fin_mk 2 0 (by simp) else Fin_mk 2 1 (by simp)
      constructor
      · intro a b hab
        by_cases ha : a = x1.val <;> simp [ha] at hab <;> ext
        · rw [ha, hab]
        · rw [show a = x2.val by aesop, show b = x2.val by aesop]
      · intro y
        by_cases hy : y = Fin_mk 2 0 (by simp)
        · use ⟨x1.val, by aesop⟩; aesop
        · use ⟨x2.val, by aesop⟩
          simp [show ¬x2.val = x1.val by aesop]
          have : (y : ℕ) ≠ 0 := by aesop
          grind
    have := hS _ (by intro; aesop) hSCard
    have : (image f S).card = 1 := by
      rw [show image f S = ({(f x1).val} : Set) by aesop]
      apply has_card_to_card
      exact singleton_card
    linarith

/--
习题 3.6.12
-/
def SetTheory.Set.Permutations (n : ℕ) : Set := (Fin n ^ Fin n).specify (fun F ↦ Function.Bijective (pow_fun_equiv F))

/--
习题 3.6.12 (i) 第一部分
-/
theorem SetTheory.Set.Permutations_finite (n : ℕ) : (Permutations n).finite := by
  have h1 : Permutations n ⊆ Fin n ^ Fin n := specify_subset _
  have h2 := (card_pow (Fin_finite n) (Fin_finite n)).1
  exact (card_subset h2 h1).1

noncomputable def SetTheory.Set.Permutations_toFun {n : ℕ} (p : Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n : ℕ} (p : Permutations n) :
    Function.Bijective (Permutations_toFun p) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose_spec

theorem SetTheory.Set.Permutations_inj {n : ℕ} (p1 p2 : Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by
  refine ⟨?_, by aesop⟩
  intro h
  unfold Permutations_toFun at h
  grind

noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun e := by
    let f := pow_fun_equiv.symm e
    exact ⟨f.val, by
      simp only [Permutations, specification_axiom'']
      use f.property; simp [f]
      exact e.bijective
    ⟩
  left_inv p := by
    simp [pow_fun_equiv, Permutations_toFun]
    generalize_proofs _ h1
    simp [h1.choose_spec]
  right_inv e := by
    simp [pow_fun_equiv, Permutations_toFun]
}

def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) := Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by grind [castSucc]

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by
  have := Fin.toNat_lt x
  simp [castSucc]; omega

noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
  castSucc (castPred x h) = x := by simp [castSucc, castPred]

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
  castPred (castSucc x) h = x := by simp [castSucc, castPred]

def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

theorem SetTheory.Set.card_iUnion_card_disjoint {n m : ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by
  induction' n with n hind
  · have : ((Fin 0).iUnion S).has_card 0 := by
      let f (x : (Fin 0).iUnion S) : Fin 0 := by
        have := x.property
        rw [mem_iUnion] at this
        exact this.choose
      use f
      constructor
      · intro _ _ h
        simp [f] at h
        generalize_proofs h1 _ at h
        have := Fin.toNat_lt h1.choose
        omega
      · intro y
        have := Fin.toNat_lt y
        omega
    simp; exact ⟨⟨0, this⟩, has_card_to_card this⟩
  · let S' := fun i : Fin n ↦ S (Fin.castSucc i)
    have hS'c : ∀ i, (S' i).has_card m := by
      intro i
      simp [S']
      exact hSc _
    have hS'd : Pairwise fun i j => Disjoint (S' i) (S' j) := by
      simp only [S', Pairwise]
      intro i j hij
      have : Fin.castSucc i ≠ Fin.castSucc j := by
        by_contra h
        rw [Fin.castSucc_inj] at h
        contradiction
      exact hSd this
    have := hind hS'c hS'd
    constructor
    · have : ∀ i, (S i).finite := by
        intro i
        exact ⟨m, hSc i⟩
      exact iUnion_finite this
    · have h1 : (Fin (n + 1)).iUnion S = (Fin n).iUnion S' ∪ (S (Fin.last n)) := by
        ext x
        rw [mem_union, mem_iUnion, mem_iUnion]
        constructor <;> intro hx
        · obtain ⟨a, ha⟩ := hx
          by_cases h : a = n
          · right
            grind [Fin.last]
          · left
            use Fin.castPred a h
            simpa [S']
        · obtain (⟨a, ha⟩ | hx) := hx
          · use Fin.castSucc a
          · use Fin.last n
      have h2 : Disjoint ((Fin n).iUnion S') (S (Fin.last n)) := by
        rw [disjoint_iff]
        simp [S']
        by_contra
        obtain ⟨x, hx⟩ := nonempty_def this
        rw [mem_inter] at hx
        obtain ⟨hx1, hx2⟩ := hx
        rw [mem_iUnion] at hx1
        obtain ⟨a, ha⟩ := hx1
        have h : x ∈ S (Fin.last n) ∩ S (Fin.castSucc a) := by simp [hx2, ha]
        have : S (Fin.last n) ∩ S (Fin.castSucc a) = ∅ := by
          rw [← disjoint_iff]
          exact hSd (by
            by_contra
            simp [Fin.last] at this
            have := Fin.castSucc_ne a
            omega
          )
        simp [this] at h
      rw [h1, card_union_disjoint this.1 ⟨m, (hSc (Fin.last n))⟩ h2, this.2, has_card_to_card (hSc (Fin.last n))]
      ring

noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x : ℕ) < i then
    Fin_mk _ (x : ℕ) (by grind)
  else
    Fin_mk _ ((x : ℕ) - 1) (Nat.sub_lt_right_of_lt_add (by
      have : i < (x : ℕ) := by grind
      grind
    ) (Fin.toNat_lt x))

noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x : ℕ) < i then
    Fin_embed _ _ (by simp) x
  else
    Fin_mk _ ((x : ℕ) + 1) (by grind)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by
  simp only [succAbove]
  by_cases h : (x : ℕ) < i <;> simp [h] <;> omega

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by
  simp only [succAbove, predAbove]
  by_cases h : (x : ℕ) < i <;> simp [h]
  by_cases h' : ((x : ℕ) - 1) < i <;> simp [h']
  · grind
  · apply Nat.sub_add_cancel
    have : (x : ℕ) > i := by grind
    grind

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by
  simp only [predAbove, succAbove]
  by_cases h : (x : ℕ) < i <;> simp [h]
  by_cases h' : ((x : ℕ) + 1) < i <;> simp [h']
  omega

/--
习题 3.6.12 (i) 第二部分
-/
theorem SetTheory.Set.Permutations_ih (n : ℕ) :
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  -- 根据p把n++映射到哪个值，把S_{n++}划分成n++个子集
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    have equiv : S i ≃ Permutations n := {
      toFun s := by
        have h1 := s.property
        rw [specification_axiom''] at h1
        have h2 := h1.choose
        simp only [Permutations, specification_axiom''] at h2
        have h3 := h2.choose
        rw [powerset_axiom] at h3
        let f := h3.choose
        let fbij := h2.choose_spec
        let f' (x : Fin n) : Fin n := Fin.predAbove i (f (Fin.castSucc x)) (by
          by_contra h
          rw [← h1.choose_spec] at h
          have := fbij.1 h
          simp [Fin.last] at this
        )
        have hf : ∀ x : Fin n, ¬f (Fin.castSucc x) < (i : ℕ) → f (Fin.castSucc x) > (i : ℕ) := by
          intro x hx
          have : ¬f (Fin.castSucc x) = i := by
            by_contra h
            rw [← h1.choose_spec] at h
            have := fbij.1 h
            simp [Fin.last] at this
          simp at this
          omega
        have : Function.Bijective f' := by
          constructor
          · intro x1 x2 hx
            simp [f', Fin.predAbove] at hx
            by_cases hx1 : f (Fin.castSucc x1) < (i : ℕ) <;> simp [hx1] at hx <;>
            by_cases hx2 : f (Fin.castSucc x2) < (i : ℕ) <;> simp [hx2] at hx
            · exact Fin.castSucc_inj.mp (fbij.1 (by simpa))
            · have := hf x2 hx2; omega
            · have := hf x1 hx1; omega
            · have : (f (Fin.castSucc x1) : ℕ) = f (Fin.castSucc x2) := by
                have := hf x1 hx1
                have := hf x2 hx2
                omega
              exact Fin.castSucc_inj.mp (fbij.1 (by simpa))
          · intro y
            simp [f']
            let a := Fin.castPred ((Equiv.ofBijective f fbij).symm (Fin.succAbove i y)) (by
              by_contra h
              have : Fin.succAbove i y = f (Fin.last n) := by
                have : ((Equiv.ofBijective f fbij).symm (Fin.succAbove i y)) = Fin.last n := by simp [h, Fin.last]
                rw [← this]
                change Fin.succAbove i y = (Equiv.ofBijective f fbij).toFun ((Equiv.ofBijective f fbij).invFun (Fin.succAbove i y))
                rw [(Equiv.ofBijective f fbij).right_inv]
              have := Fin.succAbove_ne i y
              nth_rw 2 [← h1.choose_spec] at this
              change Fin.succAbove i y ≠ f (Fin.last n) at this
              contradiction
            )
            use a
            obtain ⟨m, hm⟩ := (mem_Fin _ _).mp a.property
            rw [hm.2]
            use ⟨(m : nat).property, by simp [hm.1]⟩
            simp [← hm.2, a]
            generalize_proofs h4
            change Fin.predAbove i ((Equiv.ofBijective f fbij).toFun ((Equiv.ofBijective f fbij).invFun (Fin.succAbove i y))) h4 = (y : ℕ)
            simp
        exact perm_equiv_equiv.symm (Equiv.ofBijective f' this)
      invFun p := by
        have := perm_equiv_equiv p
        -- 构建f : Fin (n + 1) → Fin (n + 1)，满足f (Fin.last n) = i
        open Classical in
        let f (x : Fin (n + 1)) : Fin (n + 1) := if h : x = n then i else Fin.succAbove i (perm_equiv_equiv p (Fin.castPred x h))
        have fbij : Function.Bijective f := by
          constructor
          · intro x1 x2 hx
            simp only [f] at hx
            by_cases hx1 : x1 = n <;> simp [hx1] at hx <;>
            by_cases hx2 : x2 = n <;> simp [hx2] at hx
            · grind
            · simp only [Fin.succAbove] at hx
              generalize_proofs h1 h2 h3 at hx
              by_cases hi : perm_equiv_equiv p (Fin.castPred x2 h1) < (i : ℕ) <;>
              simp [hi] at hx <;> omega
            · simp only [Fin.succAbove] at hx
              generalize_proofs h1 h2 h3 at hx
              by_cases hi : perm_equiv_equiv p (Fin.castPred x1 h1) < (i : ℕ) <;>
              simp [hi] at hx <;> omega
            · simp only [Fin.succAbove] at hx
              generalize_proofs h1 h2 h3 h4 h5 at hx
              by_cases hi1 : perm_equiv_equiv p (Fin.castPred x1 h1) < (i : ℕ) <;> simp [hi1] at hx <;>
              by_cases hi2 : perm_equiv_equiv p (Fin.castPred x2 h4) < (i : ℕ) <;> simp [hi2] at hx
              on_goal 1 4 =>
                simp only [Fin.castPred] at hx
                generalize_proofs hx1 hx2 at hx
                have : (perm_equiv_equiv p) (Fin_mk n ↑x1 hx1) = (perm_equiv_equiv p) (Fin_mk n ↑x2 hx2) := by grind
                simp at this; grind
              all_goals omega
          · intro y
            by_cases h : y = i
            · use Fin.last n
              simp [f, Fin.last, h]
            · use Fin.castSucc ((perm_equiv_equiv p).symm (Fin.predAbove i y h))
              simp [f]
        let p' : Permutations (n + 1) := ⟨pow_fun_equiv.symm f, by
          simp only [Permutations, specification_axiom'']
          exact ⟨(pow_fun_equiv.symm f).property, by simpa⟩
        ⟩
        exact ⟨p', by
          simp only [S, specification_axiom'']
          exact ⟨p'.property, by
            simp [p', perm_equiv_equiv, Permutations_toFun]
            generalize_proofs h1
            simp [(coe_of_fun_inj _ _).mp h1.choose_spec, f, Fin.last]
          ⟩
        ⟩
      left_inv s := by
        have hsS := s.property
        rw [specification_axiom''] at hsS
        have hlast := hsS.choose_spec
        simp
        generalize_proofs h1 h2 h3 h4 h5
        simp [pow_fun_equiv]
        congr
        have hfun : (open Classical in fun x : Fin (n + 1) ↦ if x = n then i else h1.choose x) = h1.choose := by
          ext x
          by_cases hx : x = n <;> simp [hx]
          simp [← hlast, perm_equiv_equiv, Permutations_toFun, show Fin.last n = x by simp [Fin.last, hx]]
        simp [hfun, h1.choose_spec]
      right_inv p := by
        simp [perm_equiv_equiv, pow_fun_equiv]
        generalize_proofs h1 h2 h3 h4 h5 h6 h7
        congr
        sorry
    }
    use equiv, equiv.injective, equiv.surjective

  have hSc : ∀ i, (S i).has_card (Permutations n).card := by
    intro i
    have := has_card_card (Permutations_finite n)
    rwa [EquivCard_to_has_card_eq (hSe i)]

  have hSd : Pairwise fun i j ↦ Disjoint (S i) (S j) := by
    simp only [Pairwise]
    intro i j hij
    rw [disjoint_iff]
    by_contra h
    obtain ⟨_, hx⟩ := nonempty_def h
    obtain ⟨hx1, hx2⟩ := (mem_inter _ _ _).mp hx
    rw [specification_axiom''] at hx1 hx2
    have : i = j := by rw [← hx1.choose_spec, ← hx2.choose_spec]
    contradiction

  have : (iUnion _ S) = Permutations (n + 1) := by
    simp only [S]; ext x
    constructor
    · intro h
      obtain ⟨a, ha⟩ := (mem_iUnion _ _).mp h
      exact specification_axiom ha
    · intro h
      rw [mem_iUnion]
      use perm_equiv_equiv ⟨x, h⟩ (Fin.last n)
      simpa
  rw [← (card_iUnion_card_disjoint hSc hSd).2, this]

end Chapter3
