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
  by_contra! h
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
theorem SetTheory.Set.card_earse {n : ℕ} (h : n ≥ 1) {X : Set} (hX : X.has_card n) (x : X) :
    (X \ {x.val}).has_card (n - 1) := by
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨y, by aesop⟩
  observe hι : ∀ x : X', (ι x : Object) = x
  choose m0 hm0 hm0f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n - 1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x') : ℕ) ≠ m0 := by
      by_contra!; simp [← this, Subtype.val_inj, hf.1.eq_iff, ι] at hm0f
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
        by_contra!
        have := hf.1 this
        have := x1.property
        rw [mem_sdiff] at this
        have := this.2
        simp at this
        have : ⟨x1, hx1⟩ ≠ x := by grind
        contradiction) <;>
      have : f ⟨x2, hx2⟩ ≠ f x := by
        by_contra!
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
          · by_contra! h
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
          · by_contra! h
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
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_earse ?_ h1 ⟨_, hx⟩) (card_earse ?_ h2 ⟨_, hx⟩) <;> omega

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

end Chapter3
