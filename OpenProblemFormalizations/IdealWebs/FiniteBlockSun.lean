import OpenProblemFormalizations.IdealWebs.FiniteSelectors

/-!
A finite-block consequence of an Fσ-level presentation. It is an auxiliary
combinatorial statement, not a proof of the web-closure dichotomy.
-/

namespace OpenProblemFormalizations.IdealWebs

open Set

universe u

/-- An increasing hereditary level cover whose failures have finite witnesses.
For closed hereditary levels in a Cantor power, the last condition follows
from compactness. -/
structure FinitaryLevelCover {α : Type u}
    (I : Set (Set α)) (D : ℕ → Set (Set α)) : Prop where
  monotone : Monotone D
  hereditary : ∀ (m : ℕ) (a b : Set α), a ⊆ b → b ∈ D m → a ∈ D m
  sub_ideal : ∀ (m : ℕ) (a : Set α), a ∈ D m → a ∈ I
  covers : ∀ a ∈ I, ∃ m, a ∈ D m
  finite_witness : ∀ (m : ℕ) (a : Set α), a ∉ D m →
    ∃ b : Set α, b.Finite ∧ b ⊆ a ∧ b ∉ D m

/-- A countable sun in an ideal with finitary levels yields a sun of finite
sets. Each finite witness comes from the union of a tail of the old sun, so
it is supported by a finite package of old members. -/
theorem seqSun_finite_block {α : Type u}
    (I : Set (Set α)) (D : ℕ → Set (Set α)) (S : ℕ → Set α)
    (hlevels : FinitaryLevelCover I D)
    (hfinite : ∀ a : Set α, a.Finite → a ∈ I)
    (hsun : SeqSun I S) :
    ∃ H : ℕ → Set α,
      (∀ m, (H m).Finite ∧ H m ∈ I ∧
        H m ⊆ ⋃₀ (S '' Ici m)) ∧
      SeqSun I H := by
  classical
  have htail (m : ℕ) : ⋃₀ (S '' Ici m) ∉ D m := by
    intro hm
    have htailinf : (Ici m : Set ℕ).Infinite := by
      have hr : (Set.range (fun n : ℕ => m + n)).Infinite :=
        Set.infinite_range_of_injective (by
          intro a b h
          exact Nat.add_left_cancel h)
      apply hr.mono
      rintro x ⟨n, rfl⟩
      exact Nat.le_add_right m n
    exact hsun (Ici m) htailinf
      (hlevels.sub_ideal m _ hm)
  choose H hHfinite hHsub hHnot using
    fun m => hlevels.finite_witness m _ (htail m)
  refine ⟨H, ?_, ?_⟩
  · intro m
    exact ⟨hHfinite m, hfinite _ (hHfinite m), hHsub m⟩
  · intro a ha hbound
    obtain ⟨k, hk⟩ := hlevels.covers _ hbound
    have hlarge : ∃ m ∈ a, k < m := by
      by_contra hn
      have hsub : a ⊆ Iic k := by
        intro m hm
        exact Nat.le_of_not_gt (by
          intro hgt
          exact hn ⟨m, hm, hgt⟩)
      exact ha ((finite_le_nat k).subset hsub)
    obtain ⟨m, hm, hkm⟩ := hlarge
    have hHm : H m ⊆ ⋃₀ (H '' a) := by
      intro x hx
      exact ⟨H m, ⟨m, hm, rfl⟩, hx⟩
    have hlevel : H m ∈ D k :=
      hlevels.hereditary k _ _ hHm hk
    exact hHnot m (hlevels.monotone (Nat.le_of_lt hkm) hlevel)

end OpenProblemFormalizations.IdealWebs
