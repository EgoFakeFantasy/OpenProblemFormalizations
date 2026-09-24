import Mathlib.Order.Cofinal
import Mathlib.Order.Monotone.Basic

/-! A formalized countable boundary case of the enhanced Tukey-spectrum question. -/

namespace OpenProblemFormalizations.IdealSpectra

namespace EnhancedTukeyOmega

open Set

universe u

private noncomputable def increasingHull {P : Type u} [Preorder P]
    (s : ℕ → P) (hdir : ∀ p q : P, ∃ r : P, p ≤ r ∧ q ≤ r) : ℕ → P
  | 0 => s 0
  | n + 1 => Classical.choose (hdir (increasingHull s hdir n) (s (n + 1)))

private theorem hull_step {P : Type u} [Preorder P]
    (s : ℕ → P) (hdir : ∀ p q : P, ∃ r : P, p ≤ r ∧ q ≤ r) (n : ℕ) :
    increasingHull s hdir n ≤ increasingHull s hdir (n + 1) := by
  exact (Classical.choose_spec (hdir (increasingHull s hdir n) (s (n + 1)))).1

private theorem source_le_hull {P : Type u} [Preorder P]
    (s : ℕ → P) (hdir : ∀ p q : P, ∃ r : P, p ≤ r ∧ q ≤ r) (n : ℕ) :
    s n ≤ increasingHull s hdir n := by
  cases n with
  | zero => rfl
  | succ n =>
      exact (Classical.choose_spec (hdir (increasingHull s hdir n) (s (n + 1)))).2

/-- A countable unbounded family in a directed preorder has an increasing
    enumeration whose image on every cofinal subset of `ℕ` is unbounded. -/
theorem cofinal_subsequence_unbounded {P : Type u} [Preorder P]
    (hdir : ∀ p q : P, ∃ r : P, p ≤ r ∧ q ≤ r)
    (s : ℕ → P) (hs : ¬ BddAbove (range s)) :
    ∃ f : ℕ → P, ∀ a : Set ℕ, IsCofinal a → ¬ BddAbove (f '' a) := by
  let f := increasingHull s hdir
  have hmono : Monotone f := monotone_nat_of_le_succ (hull_step s hdir)
  refine ⟨f, ?_⟩
  intro a ha hbound
  obtain ⟨p, hp⟩ := hbound
  apply hs
  refine ⟨p, ?_⟩
  rintro q ⟨n, rfl⟩
  obtain ⟨m, hm, hnm⟩ := ha n
  have hfm : f m ≤ p := hp ⟨m, hm, rfl⟩
  exact (source_le_hull s hdir n).trans ((hmono hnm).trans hfm)

end EnhancedTukeyOmega

end OpenProblemFormalizations.IdealSpectra
