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

#print axioms no_omega_omegaOne_ideal_representative
#print axioms cofinal_subsequence_unbounded
#print axioms seqWeb_subset_level
end OpenProblemAcceptance

