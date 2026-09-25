import OpenProblemFormalizations

namespace OpenProblemAcceptance
open OpenProblemFormalizations.IdealSpectra.CohesiveIdeal
open OpenProblemFormalizations.IdealSpectra.EnhancedTukeyOmega
open OpenProblemFormalizations.IdealWebs

universe u

example {P : Type u} [Preorder P]
    (hnat : TukeyLE P ℕ ↔
      Cohesive ℕ (fun a : Set (ℕ × OmegaOne) => a ∉ NoncofinalIdeal))
    (hone : TukeyLE P OmegaOne ↔
      Cohesive OmegaOne (fun a : Set (ℕ × OmegaOne) => a ∉ NoncofinalIdeal))
    (hunit : TukeyLE P PUnit.{1} ↔
      Cohesive PUnit.{1} (fun a : Set (ℕ × OmegaOne) => a ∉ NoncofinalIdeal)) :
    False :=
  no_omega_omegaOne_ideal_representative hnat hone hunit

example {P : Type u} [Preorder P]
    (hdir : ∀ p q : P, ∃ r : P, p ≤ r ∧ q ≤ r)
    (s : ℕ → P) (hs : ¬ BddAbove (Set.range s)) :
    ∃ f : ℕ → P, ∀ a : Set ℕ, IsCofinal a → ¬ BddAbove (f '' a) :=
  cofinal_subsequence_unbounded hdir s hs

example {α : Type u} (I W : Set (Set α)) (F : ℕ → Set (Set α))
    (hmono : Monotone F)
    (hhered : ∀ (n : ℕ) (a b : Set α), a ⊆ b → b ∈ F n → a ∈ F n)
    (hcover : ∀ a ∈ I, ∃ n, a ∈ F n)
    (hweb : SeqWeb I W) :
    ∃ n, W ⊆ F n :=
  seqWeb_subset_level I W F hmono hhered hcover hweb

example {α : Type u} {β : Type*} (f : α → β)
    (I : Set (Set β)) (W : Set (Set α))
    (hweb : SeqWeb {a | f '' a ∈ I} W) :
    SeqWeb I {b | ∃ a ∈ W, f '' a = b} :=
  seqWeb_image_of_pullback f I W hweb

example {α : Type u} (I : Set (Set α)) (S D : ℕ → Set α)
    (hdown : ∀ x y : Set α, x ⊆ y → y ∈ I → x ∈ I)
    (hunion : ∀ x y : Set α, x ∈ I → y ∈ I → x ∪ y ∈ I)
    (hsun : SeqSun I S) (hthin : FiniteSelectorThin I S)
    (hD : ∀ n, D n ⊆ S n ∧ (D n).Finite) :
    SeqSun I (fun n => S n \ D n) :=
  seqSun_diff_finite I S D hdown hunion hsun hthin hD

#print axioms no_omega_omegaOne_ideal_representative
#print axioms cofinal_subsequence_unbounded
#print axioms seqWeb_subset_level
#print axioms seqWeb_image_of_pullback
#print axioms seqSun_diff_finite
#print axioms selectorIdeal_union
#print axioms selectorIdeal_tall
#print axioms selectorIdeal_eventually_mono
#print axioms selectorIdeal_countable_lower
#print axioms seqSun_finite_block
#print axioms OpenProblemFormalizations.IdealWebs.crossingRows_completeRows
#print axioms OpenProblemFormalizations.IdealWebs.crossingBounded_union
#print axioms OpenProblemFormalizations.IdealWebs.completeRows_not_crossingBounded
#print axioms OpenProblemFormalizations.IdealWebs.infiniteRows_finite_of_crossingBounded
#print axioms OpenProblemFormalizations.IdealWebs.fullRows_seqSun
#print axioms OpenProblemFormalizations.IdealWebs.fullRow_finiteCoordinateApprox
#print axioms OpenProblemFormalizations.IdealWebs.finiteCoordinateClosure_not_seqWeb
#print axioms OpenProblemFormalizations.CohenCoherence.cofinal_iUnion_index
#print axioms OpenProblemFormalizations.CohenCoherence.countable_graph_cover_cofinal_stars
end OpenProblemAcceptance
