import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.Cofinal

/-!
  A local formalization of the Tukey obstruction behind Question 3.17 of
  Benhamou, *Scales in the Point Spectrum*.  `CofinalMap` is deliberately
  defined with the paper's cofinal-subset convention, also for a target
  preorder which need not be directed.
-/

namespace OpenProblemFormalizations.IdealSpectra

namespace CohesiveIdeal

open Set

universe u v w

def CofinalMap {α : Type u} {β : Type v} [LE α] [LE β] (f : α → β) : Prop :=
  ∀ s : Set α, IsCofinal s → IsCofinal (f '' s)

def TukeyLE (P : Type u) (Q : Type v) [LE P] [LE Q] : Prop :=
  ∃ f : Q → P, CofinalMap f

theorem top_of_two_tukey_bounds
    {P : Type u} {κ : Type v} {lam : Type w}
    [Preorder P] [Preorder κ] [Preorder lam]
    (hκ : TukeyLE P κ) (hlam : TukeyLE P lam)
    (hfiber : ∀ h : lam → κ, ∃ k : κ, IsCofinal {l : lam | h l = k}) :
    ∃ top : P, ∀ p : P, p ≤ top := by
  obtain ⟨u, hu⟩ := hκ
  obtain ⟨v, hv⟩ := hlam
  have hu_cof : IsCofinal (range u) := by
    simpa [CofinalMap] using hu univ IsCofinal.univ
  have hcover (l : lam) : ∃ k : κ, v l ≤ u k := by
    obtain ⟨p, ⟨k, rfl⟩, hp⟩ := hu_cof (v l)
    exact ⟨k, hp⟩
  let chooseIndex (l : lam) : κ := Classical.choose (hcover l)
  obtain ⟨k, hk⟩ := hfiber chooseIndex
  have hv_cof : IsCofinal (v '' {l : lam | chooseIndex l = k}) := hv _ hk
  refine ⟨u k, ?_⟩
  intro p
  obtain ⟨q, ⟨l, hl, rfl⟩, hpq⟩ := hv_cof p
  have hvl : v l ≤ u (chooseIndex l) := Classical.choose_spec (hcover l)
  exact hpq.trans (hl ▸ hvl)

def Cohesive {X : Type u} (Q : Type v) [LE Q] (positive : Set X → Prop) : Prop :=
  ∃ f : X → Q, ∀ a : Set X, positive a → ¬ BddAbove (f '' a)

def RectPositive {κ : Type u} {lam : Type v} [LE κ] [LE lam]
    (a : Set (κ × lam)) : Prop := IsCofinal a

theorem fst_cohesive {κ : Type u} {lam : Type v}
    [Preorder κ] [Preorder lam] [NoMaxOrder κ] [Nonempty lam] :
    Cohesive κ (RectPositive (κ := κ) (lam := lam)) := by
  refine ⟨Prod.fst, ?_⟩
  intro a ha
  have hcof : IsCofinal (Prod.fst '' a) := by
    intro k
    obtain ⟨p, hp, hkp⟩ := ha (k, Classical.choice inferInstance)
    exact ⟨p.1, ⟨p, hp, rfl⟩, hkp.1⟩
  rintro ⟨b, hb⟩
  obtain ⟨k, hbk⟩ := exists_gt b
  obtain ⟨c, hc, hkc⟩ := hcof k
  exact (not_le_of_gt hbk) (hkc.trans (hb hc))

theorem snd_cohesive {κ : Type u} {lam : Type v}
    [Preorder κ] [Preorder lam] [NoMaxOrder lam] [Nonempty κ] :
    Cohesive lam (RectPositive (κ := κ) (lam := lam)) := by
  refine ⟨Prod.snd, ?_⟩
  intro a ha
  have hcof : IsCofinal (Prod.snd '' a) := by
    intro l
    obtain ⟨p, hp, hlp⟩ := ha (Classical.choice inferInstance, l)
    exact ⟨p.2, ⟨p, hp, rfl⟩, hlp.2⟩
  rintro ⟨b, hb⟩
  obtain ⟨l, hbl⟩ := exists_gt b
  obtain ⟨c, hc, hlc⟩ := hcof l
  exact (not_le_of_gt hbl) (hlc.trans (hb hc))

theorem unit_not_cohesive {X : Type u} [Preorder X] :
    ¬ Cohesive PUnit.{1} (fun a : Set X => IsCofinal a) := by
  rintro ⟨f, hf⟩
  have hpos : (fun a : Set X => IsCofinal a) univ := IsCofinal.univ
  apply hf univ hpos
  refine ⟨PUnit.unit, ?_⟩
  rintro q ⟨x, -, rfl⟩
  trivial

theorem no_representative
    {P : Type u} {κ : Type v} {lam : Type w}
    [Preorder P] [Preorder κ] [Preorder lam]
    [NoMaxOrder κ] [NoMaxOrder lam] [Nonempty κ] [Nonempty lam]
    (hfiber : ∀ h : lam → κ, ∃ k : κ, IsCofinal {l : lam | h l = k})
    (hκ : TukeyLE P κ ↔ Cohesive κ (RectPositive (κ := κ) (lam := lam)))
    (hlam : TukeyLE P lam ↔ Cohesive lam (RectPositive (κ := κ) (lam := lam)))
    (hunit : TukeyLE P PUnit.{1} ↔ Cohesive PUnit.{1} (RectPositive (κ := κ) (lam := lam))) :
    False := by
  obtain ⟨top, htop⟩ := top_of_two_tukey_bounds
    (hκ.mpr fst_cohesive) (hlam.mpr snd_cohesive) hfiber
  have hu : TukeyLE P PUnit.{1} := by
    refine ⟨fun _ => top, ?_⟩
    intro s hs
    have hmem : PUnit.unit ∈ s := (hs PUnit.unit).choose_spec.1
    intro p
    exact ⟨top, ⟨PUnit.unit, hmem, rfl⟩, htop p⟩
  exact unit_not_cohesive (hunit.mp hu)

end CohesiveIdeal

namespace CohesiveIdeal

abbrev OmegaOne : Type 1 := Set.Iio (Ordinal.omega (1 : Ordinal.{0}))

instance : Nonempty OmegaOne := ⟨⟨0, Ordinal.omega_pos 1⟩⟩

instance : NoMaxOrder OmegaOne :=
  (Cardinal.isSuccLimit_omega 1).isSuccPrelimit.noMaxOrder_Iio

/-- Every coloring of `ω₁` with natural numbers has a cofinal monochromatic fiber. -/
theorem omegaOne_cofinal_fiber (f : OmegaOne → ℕ) :
    ∃ n : ℕ, IsCofinal {x : OmegaOne | f x = n} := by
  classical
  by_contra h
  have hn (n : ℕ) : ¬ IsCofinal {x : OmegaOne | f x = n} :=
    (not_exists.mp h) n
  have hb (n : ℕ) : ∃ b : OmegaOne, ∀ x : OmegaOne, f x = n → x < b := by
    obtain ⟨b, hb⟩ := (not_isCofinal_iff).mp (hn n)
    exact ⟨b, fun x hx => hb x hx⟩
  let b (n : ℕ) : OmegaOne := Classical.choose (hb n)
  have hbx (n : ℕ) (x : OmegaOne) (hx : f x = n) : x < b n :=
    Classical.choose_spec (hb n) x hx
  have hsup : (⨆ n : ℕ, (b n : Ordinal)) < Ordinal.omega 1 :=
    Ordinal.iSup_lt_omega_one (fun n => (b n).2)
  let x : OmegaOne := ⟨⨆ n : ℕ, (b n : Ordinal), hsup⟩
  have hlt : (x : Ordinal) < (b (f x) : Ordinal) := hbx (f x) x rfl
  have hle : (b (f x) : Ordinal) ≤ (x : Ordinal) := by
    exact Ordinal.le_iSup (fun n : ℕ => (b n : Ordinal)) (f x)
  exact (not_lt_of_ge hle) hlt

theorem no_omega_omegaOne_representative
    {P : Type u} [Preorder P]
    (hnat : TukeyLE P ℕ ↔
      Cohesive ℕ (RectPositive (κ := ℕ) (lam := OmegaOne)))
    (hone : TukeyLE P OmegaOne ↔
      Cohesive OmegaOne (RectPositive (κ := ℕ) (lam := OmegaOne)))
    (hunit : TukeyLE P PUnit.{1} ↔
      Cohesive PUnit.{1} (RectPositive (κ := ℕ) (lam := OmegaOne))) :
    False :=
  no_representative (κ := ℕ) (lam := OmegaOne)
    omegaOne_cofinal_fiber hnat hone hunit

/-- The ideal of non-cofinal subsets of a product order. -/
def NoncofinalIdeal {κ : Type u} {lam : Type v}
    [LE κ] [LE lam] : Set (Set (κ × lam)) :=
  {a | ¬ IsCofinal a}

theorem noncofinalIdeal_downward
    {κ : Type u} {lam : Type v} [LE κ] [LE lam]
    {a b : Set (κ × lam)}
    (hab : a ⊆ b) (hb : b ∈ NoncofinalIdeal) :
    a ∈ NoncofinalIdeal := by
  intro ha
  exact hb (ha.mono hab)

theorem noncofinalIdeal_union
    {κ : Type u} {lam : Type v}
    [LinearOrder κ] [LinearOrder lam]
    {a b : Set (κ × lam)}
    (ha : a ∈ NoncofinalIdeal) (hb : b ∈ NoncofinalIdeal) :
    a ∪ b ∈ NoncofinalIdeal := by
  have ha' : ∃ r : κ × lam, ∀ x ∈ a, ¬ r ≤ x := by
    simpa [NoncofinalIdeal, IsCofinal] using ha
  have hb' : ∃ r : κ × lam, ∀ x ∈ b, ¬ r ≤ x := by
    simpa [NoncofinalIdeal, IsCofinal] using hb
  obtain ⟨ra, hra⟩ := ha'
  obtain ⟨rb, hrb⟩ := hb'
  intro hcof
  let r : κ × lam := (max ra.1 rb.1, max ra.2 rb.2)
  obtain ⟨x, hx, hrx⟩ := hcof r
  rcases hx with hx | hx
  · exact hra x hx ((show ra ≤ r from ⟨le_max_left _ _, le_max_left _ _⟩).trans hrx)
  · exact hrb x hx ((show rb ≤ r from ⟨le_max_right _ _, le_max_right _ _⟩).trans hrx)


theorem noncofinalIdeal_empty :
    (∅ : Set (ℕ × OmegaOne)) ∈ NoncofinalIdeal := by
  change ¬ IsCofinal (∅ : Set (ℕ × OmegaOne))
  intro h
  obtain ⟨x, hx, _⟩ := h (0, Classical.choice inferInstance)
  exact hx

theorem noncofinalIdeal_singleton (x : ℕ × OmegaOne) :
    ({x} : Set (ℕ × OmegaOne)) ∈ NoncofinalIdeal := by
  change ¬ IsCofinal ({x} : Set (ℕ × OmegaOne))
  intro h
  obtain ⟨y, hy, hxy⟩ := h (x.1 + 1, x.2)
  have hyx : y = x := by simpa using hy
  subst y
  exact Nat.not_succ_le_self x.1 hxy.1

theorem noncofinalIdeal_proper :
    (Set.univ : Set (ℕ × OmegaOne)) ∉ NoncofinalIdeal := by
  change ¬ ¬ IsCofinal (Set.univ : Set (ℕ × OmegaOne))
  intro h
  apply h
  intro x
  exact ⟨x, Set.mem_univ x, le_rfl⟩

theorem noncofinalIdeal_space :
    ⋃₀ (NoncofinalIdeal (κ := ℕ) (lam := OmegaOne)) = (Set.univ : Set (ℕ × OmegaOne)) := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    exact ⟨{x}, noncofinalIdeal_singleton x, by simp⟩

theorem rectPositive_iff_not_small (a : Set (ℕ × OmegaOne)) :
    RectPositive a ↔ a ∉ NoncofinalIdeal := by
  simp [RectPositive, NoncofinalIdeal]

theorem no_omega_omegaOne_ideal_representative
    {P : Type u} [Preorder P]
    (hnat : TukeyLE P ℕ ↔
      Cohesive ℕ (fun a : Set (ℕ × OmegaOne) => a ∉ NoncofinalIdeal))
    (hone : TukeyLE P OmegaOne ↔
      Cohesive OmegaOne (fun a : Set (ℕ × OmegaOne) => a ∉ NoncofinalIdeal))
    (hunit : TukeyLE P PUnit.{1} ↔
      Cohesive PUnit.{1} (fun a : Set (ℕ × OmegaOne) => a ∉ NoncofinalIdeal)) :
    False := by
  apply no_omega_omegaOne_representative (P := P)
  · simpa [Cohesive, RectPositive, NoncofinalIdeal] using hnat
  · simpa [Cohesive, RectPositive, NoncofinalIdeal] using hone
  · simpa [Cohesive, RectPositive, NoncofinalIdeal] using hunit

end CohesiveIdeal


end OpenProblemFormalizations.IdealSpectra
