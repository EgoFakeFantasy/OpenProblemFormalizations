import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation
import Mathlib.Order.Interval.Set.Basic

/-! A finite-selector consequence used in the audit of bounded-topology
Conjecture 4.14. This is an auxiliary combinatorial lemma, not a proof of
the conjecture. -/

namespace OpenProblemFormalizations.IdealWebs

open Set

universe u

/-- Every infinite subfamily indexed by natural numbers has unbounded union. -/
def SeqSun {α : Type u} (I : Set (Set α)) (S : ℕ → Set α) : Prop :=
  ∀ a : Set ℕ, a.Infinite → (⋃₀ (S '' a)) ∉ I

/-- Each family of finite selectors from an infinite subfamily can be thinned
to an infinite family whose union lies in the ideal. -/
def FiniteSelectorThin {α : Type u} (I : Set (Set α))
    (S : ℕ → Set α) : Prop :=
  ∀ (a : Set ℕ), a.Infinite → ∀ (D : ℕ → Set α),
    (∀ n ∈ a, D n ⊆ S n ∧ (D n).Finite) →
    ∃ b : Set ℕ, b ⊆ a ∧ b.Infinite ∧ (⋃₀ (D '' b)) ∈ I

/-- A finite-selector sun remains a sun after an arbitrary finite deletion
from each of its members. -/
theorem seqSun_diff_finite {α : Type u} (I : Set (Set α))
    (S D : ℕ → Set α)
    (hdown : ∀ x y : Set α, x ⊆ y → y ∈ I → x ∈ I)
    (hunion : ∀ x y : Set α, x ∈ I → y ∈ I → x ∪ y ∈ I)
    (hsun : SeqSun I S)
    (hthin : FiniteSelectorThin I S)
    (hD : ∀ n, D n ⊆ S n ∧ (D n).Finite) :
    SeqSun I (fun n => S n \ D n) := by
  intro a ha hres
  obtain ⟨b, hba, hb, hDb⟩ := hthin a ha D (by intro n hn; exact hD n)
  have hresb : (⋃₀ ((fun n => S n \ D n) '' b)) ∈ I := by
    apply hdown _ _ _ hres
    intro x hx
    obtain ⟨t, ⟨n, hn, rfl⟩, hxt⟩ := hx
    exact ⟨S n \ D n, ⟨n, hba hn, rfl⟩, hxt⟩
  apply hsun b hb
  apply hdown _ _ _ (hunion _ _ hresb hDb)
  intro x hx
  obtain ⟨t, ⟨n, hn, rfl⟩, hxn⟩ := hx
  by_cases hxd : x ∈ D n
  · exact Or.inr ⟨D n, ⟨n, hn, rfl⟩, hxd⟩
  · exact Or.inl ⟨S n \ D n, ⟨n, hn, rfl⟩, ⟨hxn, hxd⟩⟩

end OpenProblemFormalizations.IdealWebs
