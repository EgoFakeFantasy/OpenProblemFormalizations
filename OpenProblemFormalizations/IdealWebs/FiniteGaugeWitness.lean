import OpenProblemFormalizations.IdealWebs.CrossingGauge
import Mathlib.Data.Set.Card

/-!
# A nonvacuous finite-row gauge interface

The original natural-valued interface imposed global monotonicity on all
subsets of `ℕ`. That is incompatible with divergence on initial segments.
The corrected interface only requires monotonicity with a finite upper set.
`Set.ncard` supplies a concrete witness to the corrected skeleton assumptions.
It does not supply the extra disjoint-block compression used in E05's
no-uncountable-sun argument.
-/

namespace OpenProblemFormalizations.IdealWebs

open Set

/-- The former global natural-valued monotonicity and divergence hypotheses
cannot hold together. This records the exact reason for the interface repair. -/
theorem not_globalMonotone_divergent_natGauge {rho : Set ℕ → ℕ}
    (hrho : Monotone rho) :
    ¬ (∀ s : Set ℕ, s.Infinite → ∀ C, ∃ m, C < rho (s ∩ Set.Iic m)) := by
  intro hunb
  obtain ⟨m, hm⟩ := hunb Set.univ Set.infinite_univ (rho Set.univ)
  exact (not_lt_of_ge (hrho Set.inter_subset_left)) hm

/-- Finite cardinality, with the mathlib value zero on infinite sets. -/
noncomputable def countingGauge (s : Set ℕ) : ℕ := s.ncard

theorem countingGauge_finiteMonotone : FiniteGaugeMonotone countingGauge := by
  intro s t ht hst
  exact Set.ncard_le_ncard hst ht

theorem countingGauge_subadditive (s t : Set ℕ) :
    countingGauge (s ∪ t) ≤ countingGauge s + countingGauge t :=
  Set.ncard_union_le s t

theorem countingGauge_singleton (n : ℕ) : countingGauge {n} = 1 := by
  simp [countingGauge]

theorem countingGauge_initial_divergence (s : Set ℕ) (hs : s.Infinite) (C : ℕ) :
    ∃ m, C < countingGauge (s ∩ Set.Iic m) := by
  classical
  obtain ⟨t, hts, ht, htcard⟩ := hs.exists_subset_ncard_eq (C + 1)
  let m := ht.toFinset.sup id
  have htm : t ⊆ Set.Iic m := by
    intro n hn
    exact Finset.le_sup (f := id) (ht.mem_toFinset.mpr hn)
  have hle : C + 1 ≤ countingGauge (s ∩ Set.Iic m) := by
    rw [← htcard]
    exact Set.ncard_le_ncard (fun n hn => ⟨hts hn, htm hn⟩)
      ((finite_le_nat m).subset Set.inter_subset_right)
  exact ⟨m, (Nat.lt_succ_self C).trans_le hle⟩

/-- The repaired algebraic and divergence assumptions have a concrete model. -/
theorem exists_finite_divergent_rowGauge :
    ∃ rho : Set ℕ → ℕ,
      FiniteGaugeMonotone rho ∧
      (∀ s t : Set ℕ, rho (s ∪ t) ≤ rho s + rho t) ∧
      (∀ n : ℕ, rho {n} = 1) ∧
      (∀ s : Set ℕ, s.Infinite → ∀ C, ∃ m, C < rho (s ∩ Set.Iic m)) :=
  ⟨countingGauge, countingGauge_finiteMonotone, countingGauge_subadditive,
    countingGauge_singleton, countingGauge_initial_divergence⟩

/-- A concrete instance of the finite-row web and finite-coordinate closure
obstruction; this does not assert the full E05 counterexample. -/
theorem countingGauge_web_and_closure_obstruction :
    SeqWeb {a | crossingBounded countingGauge a} finiteRowFamily ∧
      ¬ SeqWeb {a | crossingBounded countingGauge a}
        {a | FiniteCoordinateApprox finiteRowFamily a} := by
  constructor
  · exact finiteRowFamily_seqWeb countingGauge_finiteMonotone 1
      (fun n => (countingGauge_singleton n).le)
  · exact finiteCoordinateClosure_not_seqWeb countingGauge_initial_divergence

end OpenProblemFormalizations.IdealWebs
