import OpenProblemFormalizations.IdealWebs.FiniteSelectors
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Lattice

/-! The exact finite-selector meet used in the audit of the bounded-topology
conjecture. These are structural lemmas for one fixed row family, not a proof
of the conjecture. -/

namespace OpenProblemFormalizations.IdealWebs

open Set

universe u

/-- The ideal of row indices whose selected union lies in the ambient ideal. -/
def SelectorIdeal {α : Type u} (I : Set (Set α))
    (H : ℕ → Set α) : Set (Set ℕ) :=
  {a | ⋃₀ (H '' a) ∈ I}

theorem selectorIdeal_union {α : Type u} (I : Set (Set α))
    (H K : ℕ → Set α)
    (hdown : ∀ x y : Set α, x ⊆ y → y ∈ I → x ∈ I)
    (hunion : ∀ x y : Set α, x ∈ I → y ∈ I → x ∪ y ∈ I) :
    SelectorIdeal I (fun n => H n ∪ K n) =
      SelectorIdeal I H ∩ SelectorIdeal I K := by
  ext a
  have heq : (⋃₀ ((fun n => H n ∪ K n) '' a)) =
      (⋃₀ (H '' a)) ∪ (⋃₀ (K '' a)) := by
    ext x
    constructor
    · rintro ⟨t, ⟨n, hn, rfl⟩, hx⟩
      rcases hx with hx | hx
      · exact Or.inl ⟨H n, ⟨n, hn, rfl⟩, hx⟩
      · exact Or.inr ⟨K n, ⟨n, hn, rfl⟩, hx⟩
    · rintro (⟨t, ⟨n, hn, rfl⟩, hx⟩ | ⟨t, ⟨n, hn, rfl⟩, hx⟩)
      · exact ⟨H n ∪ K n, ⟨n, hn, rfl⟩, Or.inl hx⟩
      · exact ⟨H n ∪ K n, ⟨n, hn, rfl⟩, Or.inr hx⟩
  change (⋃₀ ((fun n => H n ∪ K n) '' a)) ∈ I ↔
    (⋃₀ (H '' a)) ∈ I ∧ (⋃₀ (K '' a)) ∈ I
  rw [heq]
  constructor
  · intro h
    exact ⟨hdown _ _ (by intro x hx; exact Or.inl hx) h,
      hdown _ _ (by intro x hx; exact Or.inr hx) h⟩
  · rintro ⟨hH, hK⟩
    exact hunion _ _ hH hK

/-- Robust finite-selector thinning makes each selector ideal tall. -/
theorem selectorIdeal_tall {α : Type u} (I : Set (Set α))
    (S H : ℕ → Set α)
    (hthin : FiniteSelectorThin I S)
    (hH : ∀ n, H n ⊆ S n ∧ (H n).Finite) :
    ∀ a : Set ℕ, a.Infinite →
      ∃ b : Set ℕ, b ⊆ a ∧ b.Infinite ∧ b ∈ SelectorIdeal I H := by
  intro a ha
  exact hthin a ha H (by intro n hn; exact hH n)

/-- Containment of selectors on all but finitely many rows reverses the
inclusion of their selector ideals. -/
theorem selectorIdeal_eventually_mono {α : Type u} (I : Set (Set α))
    (H K : ℕ → Set α)
    (hsmall : ∀ x : Set α, x.Finite → x ∈ I)
    (hdown : ∀ x y : Set α, x ⊆ y → y ∈ I → x ∈ I)
    (hunion : ∀ x y : Set α, x ∈ I → y ∈ I → x ∪ y ∈ I)
    (hH : ∀ n, (H n).Finite)
    (N : ℕ) (hcontain : ∀ n, N ≤ n → H n ⊆ K n) :
    SelectorIdeal I K ⊆ SelectorIdeal I H := by
  intro a ha
  let F : Set α := ⋃ n ∈ Set.Iio N, H n
  have hidx : (Set.Iio N : Set ℕ).Finite := Set.toFinite _
  have hF : F.Finite := hidx.biUnion (by
    intro n hn
    exact hH n)
  have hsub : (⋃₀ (H '' a)) ⊆ (⋃₀ (K '' a)) ∪ F := by
    intro x hx
    obtain ⟨t, ⟨n, hn, rfl⟩, hxt⟩ := hx
    by_cases hnN : n < N
    · apply Or.inr
      change x ∈ ⋃ k ∈ Set.Iio N, H k
      simp only [Set.mem_iUnion]
      exact ⟨n, hnN, hxt⟩
    · exact Or.inl ⟨K n, ⟨n, hn, rfl⟩,
        hcontain n (Nat.le_of_not_lt hnN) hxt⟩
  exact hdown _ _ hsub (hunion _ _ ha (hsmall F hF))

/-- Every countable family of finite selectors has a single finite-selector
lower bound in the selector-ideal order. -/
theorem selectorIdeal_countable_lower {α : Type u} (I : Set (Set α))
    (H : ℕ → ℕ → Set α)
    (hsmall : ∀ x : Set α, x.Finite → x ∈ I)
    (hdown : ∀ x y : Set α, x ⊆ y → y ∈ I → x ∈ I)
    (hunion : ∀ x y : Set α, x ∈ I → y ∈ I → x ∪ y ∈ I)
    (hfinite : ∀ j n, (H j n).Finite) :
    let K : ℕ → Set α := fun n => ⋃ j ∈ Set.Iic n, H j n
    (∀ n, (K n).Finite) ∧
      ∀ j, SelectorIdeal I K ⊆ SelectorIdeal I (H j) := by
  dsimp
  constructor
  · intro n
    have hidx : (Set.Iic n : Set ℕ).Finite := Set.toFinite _
    exact hidx.biUnion (by
      intro j hj
      exact hfinite j n)
  · intro j
    apply selectorIdeal_eventually_mono I (H j)
      (fun n => ⋃ k ∈ Set.Iic n, H k n)
      hsmall hdown hunion (hfinite j) j
    intro n hj x hx
    change x ∈ ⋃ k ∈ Set.Iic n, H k n
    simp only [Set.mem_iUnion]
    exact ⟨j, hj, hx⟩

end OpenProblemFormalizations.IdealWebs
