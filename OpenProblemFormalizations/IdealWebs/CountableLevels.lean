import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation
import Mathlib.Order.Interval.Set.Basic

/-! A countable-level confinement lemma for weakly bounded families of an ideal.

This is an auxiliary statement, not a formal proof of Conjecture 4.14. The
sequence version of weak boundedness is convenient for finite repetitions.
-/

namespace OpenProblemFormalizations.IdealWebs

open Set

universe u

/-- Every sequence from `W` has an infinite subsequence whose union belongs to `I`. -/
def SeqWeb {α : Type u} (I W : Set (Set α)) : Prop :=
  ∀ f : ℕ → Set α, (∀ n, f n ∈ W) →
    ∃ a : Set ℕ, a.Infinite ∧ (⋃₀ (f '' a)) ∈ I

/-- A sequence-web in a countable increasing union of hereditary levels is
contained in one level. This is the fixed-level step in the flat-ideal audit. -/
theorem seqWeb_subset_level {α : Type u} (I W : Set (Set α))
    (F : ℕ → Set (Set α))
    (hmono : Monotone F)
    (hhered : ∀ (n : ℕ) (a b : Set α), a ⊆ b → b ∈ F n → a ∈ F n)
    (hcover : ∀ a ∈ I, ∃ n, a ∈ F n)
    (hweb : SeqWeb I W) :
    ∃ n, W ⊆ F n := by
  classical
  by_contra h
  have hbad : ∀ n, ∃ a : Set α, a ∈ W ∧ a ∉ F n := by
    intro n
    by_contra hn
    apply h
    exact ⟨n, by intro a ha; by_contra hna; exact hn ⟨a, ha, hna⟩⟩
  choose f hfW hfnot using hbad
  obtain ⟨a, ha, hunion⟩ := hweb f hfW
  obtain ⟨m, hm⟩ := hcover _ hunion
  have hlarge : ∃ n ∈ a, m < n := by
    by_contra hn
    have hsub : a ⊆ Iic m := by
      intro n hna
      exact Nat.le_of_not_gt (by intro hgt; exact hn ⟨n, hna, hgt⟩)
    exact ha ((finite_le_nat m).subset hsub)
  obtain ⟨n, hn, hmn⟩ := hlarge
  have hsub : f n ⊆ ⋃₀ (f '' a) := by
    intro x hx
    exact ⟨f n, ⟨n, hn, rfl⟩, hx⟩
  have hfm : f n ∈ F m := hhered m (f n) (⋃₀ (f '' a)) hsub hm
  exact hfnot n (hmono (Nat.le_of_lt hmn) hfm)

/-- The direct images of a sequence-web in a pulled-back ideal form a
sequence-web in the original ideal. This is the combinatorial first step of
the surjective-pullback web-closure argument. -/
theorem seqWeb_image_of_pullback {α : Type u} {β : Type*}
    (f : α → β) (I : Set (Set β)) (W : Set (Set α))
    (hweb : SeqWeb {a | f '' a ∈ I} W) :
    SeqWeb I {b | ∃ a ∈ W, f '' a = b} := by
  classical
  intro g hg
  choose a ha heq using hg
  obtain ⟨s, hs, hbound⟩ := hweb a ha
  refine ⟨s, hs, ?_⟩
  have hEq : (⋃₀ (g '' s)) = f '' (⋃₀ (a '' s)) := by
    ext y
    constructor
    · rintro ⟨b, ⟨n, hn, rfl⟩, hy⟩
      rw [← heq n] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, ⟨a n, ⟨n, hn, rfl⟩, hx⟩, rfl⟩
    · rintro ⟨x, ⟨b, ⟨n, hn, rfl⟩, hx⟩, rfl⟩
      exact ⟨g n, ⟨n, hn, rfl⟩, (heq n ▸ ⟨x, hx, rfl⟩)⟩
  rw [hEq]
  exact hbound

end OpenProblemFormalizations.IdealWebs
