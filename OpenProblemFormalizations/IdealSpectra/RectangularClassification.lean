import OpenProblemFormalizations.IdealSpectra.TukeyMaps

/-!
# Exact cohesive class of a rectangular noncofinal ideal

For nonempty linear orders `K` and `L` with no maximum and any target
preorder `Q`, cohesiveness for the noncofinal ideal on `K × L` is equivalent
to `K ≤_T Q` or `L ≤_T Q`. Regular-cardinal assumptions are unnecessary
for this classification. They enter the separate no-representative argument
through its cofinal-fiber hypothesis.
-/

namespace OpenProblemFormalizations.IdealSpectra.CohesiveIdeal

open Set

universe u v w

/-- The complete slice classification, beyond the three-test-object obstruction. -/
theorem rectangular_cohesive_iff
    {K : Type u} {L : Type v} {Q : Type w}
    [LinearOrder K] [LinearOrder L] [Preorder Q]
    [NoMaxOrder K] [NoMaxOrder L] [Nonempty K] [Nonempty L] :
    Cohesive Q (RectPositive (κ := K) (lam := L)) ↔
      TukeyLE K Q ∨ TukeyLE L Q := by
  classical
  constructor
  · rintro ⟨g, hg⟩
    by_contra h
    obtain ⟨hK, hL⟩ := not_or.mp h
    have hslices (l : L) :
        ∃ q : Q, ∃ s : Set K, IsCofinal s ∧ ∀ k ∈ s, g (k, l) ≤ q := by
      obtain ⟨s, hs, q, hq⟩ :=
        exists_unbounded_bounded_image hK (fun k : K => g (k, l))
      refine ⟨q, s, IsCofinal.of_not_bddAbove hs, ?_⟩
      intro k hk
      exact hq ⟨k, hk, rfl⟩
    choose q S hS hSq using hslices
    obtain ⟨T, hT, qstar, hqstar⟩ := exists_unbounded_bounded_image hL q
    let A : Set (K × L) := {p | p.2 ∈ T ∧ p.1 ∈ S p.2}
    have hA : RectPositive A := by
      intro p
      obtain ⟨l, hl, hpl⟩ := IsCofinal.of_not_bddAbove hT p.2
      obtain ⟨k, hk, hpk⟩ := hS l p.1
      exact ⟨(k, l), ⟨hl, hk⟩, ⟨hpk, hpl⟩⟩
    apply hg A hA
    refine ⟨qstar, ?_⟩
    rintro r ⟨⟨k, l⟩, ⟨hl, hk⟩, rfl⟩
    exact (hSq l k hk).trans (hqstar ⟨l, hl, rfl⟩)
  · rintro (hK | hL)
    · exact cohesive_of_tukeyLE hK fst_cohesive
    · exact cohesive_of_tukeyLE hL snd_cohesive

/-- The same classification stated directly in terms of ideal-positive sets. -/
theorem noncofinalIdeal_cohesive_iff
    {K : Type u} {L : Type v} {Q : Type w}
    [LinearOrder K] [LinearOrder L] [Preorder Q]
    [NoMaxOrder K] [NoMaxOrder L] [Nonempty K] [Nonempty L] :
    Cohesive Q (fun a : Set (K × L) => a ∉ NoncofinalIdeal) ↔
      TukeyLE K Q ∨ TukeyLE L Q := by
  simpa only [RectPositive, NoncofinalIdeal, Set.mem_setOf_eq, not_not] using
    (rectangular_cohesive_iff (K := K) (L := L) (Q := Q))

/-- Specialization to the concrete ideal used to refute Question 3.17. -/
theorem omega_omegaOne_cohesive_iff
    {Q : Type u} [Preorder Q] :
    Cohesive Q (fun a : Set (ℕ × OmegaOne) => a ∉ NoncofinalIdeal) ↔
      TukeyLE ℕ Q ∨ TukeyLE OmegaOne Q :=
  noncofinalIdeal_cohesive_iff

end OpenProblemFormalizations.IdealSpectra.CohesiveIdeal
