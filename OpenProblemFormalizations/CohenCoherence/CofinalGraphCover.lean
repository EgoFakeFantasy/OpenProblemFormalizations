import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation

/-! An abstract countable graph-cover lemma used in the audit of Cohen
preservation of two-coherent families. It does not settle that problem. -/

namespace OpenProblemFormalizations.CohenCoherence

open Set

universe u

/-- A subset is cofinal in the preorder. -/
def CofinalSet {P : Type u} [Preorder P] (A : Set P) : Prop :=
  ∀ p : P, ∃ a ∈ A, p ≤ a

/-- On a countably directed preorder, a countable union can be cofinal only
if one constituent is cofinal. -/
theorem cofinal_iUnion_index {P : Type u} [Preorder P]
    (hdirected : ∀ f : ℕ → P, ∃ u, ∀ n, f n ≤ u)
    (A : ℕ → Set P) (hunion : CofinalSet (⋃ n, A n)) :
    ∃ n, CofinalSet (A n) := by
  classical
  by_contra h
  push Not at h
  have hw : ∀ n, ∃ p : P, ∀ a ∈ A n, ¬ p ≤ a := by
    intro n
    simpa [CofinalSet, not_forall, not_exists] using h n
  choose p hp using hw
  obtain ⟨u, hu⟩ := hdirected p
  obtain ⟨a, ha, hua⟩ := hunion u
  obtain ⟨n, han⟩ := Set.mem_iUnion.mp ha
  exact hp n a han (le_trans (hu n) hua)

/-- A fixed graph from a countable edge cover has a cofinal star in every
eventual upper cone; the center may depend on the cone. -/
theorem countable_graph_cover_cofinal_stars {P : Type u} [Preorder P]
    (hdirected : ∀ f : ℕ → P, ∃ u, ∀ n, f n ≤ u)
    (E : ℕ → P → P → Prop)
    (hcover : ∀ x y : P, ∃ n, E n x y) :
    ∃ n, ∀ g : P, ∃ x : P, g ≤ x ∧
      CofinalSet {z : P | g ≤ z ∧ E n x z} := by
  classical
  have hlocal : ∀ g : P, ∃ n, ∃ x : P, g ≤ x ∧
      CofinalSet {z : P | g ≤ z ∧ E n x z} := by
    intro g
    let A : ℕ → Set P := fun n => {z | g ≤ z ∧ E n g z}
    have hA : CofinalSet (⋃ n, A n) := by
      intro p
      obtain ⟨u, hu⟩ := hdirected (fun n => if n = 0 then g else p)
      have hgu : g ≤ u := by simpa using hu 0
      have hpu : p ≤ u := by simpa using hu 1
      obtain ⟨n, hen⟩ := hcover g u
      exact ⟨u, Set.mem_iUnion.mpr ⟨n, ⟨hgu, hen⟩⟩, hpu⟩
    obtain ⟨n, hn⟩ := cofinal_iUnion_index hdirected A hA
    exact ⟨n, g, le_refl g, hn⟩
  by_contra h
  push Not at h
  choose g hg using h
  obtain ⟨u, hu⟩ := hdirected g
  obtain ⟨n, x, hux, hx⟩ := hlocal u
  have hcof : CofinalSet {z : P | g n ≤ z ∧ E n x z} := by
    intro p
    obtain ⟨z, ⟨huz, he⟩, hpz⟩ := hx p
    exact ⟨z, ⟨le_trans (hu n) huz, he⟩, hpz⟩
  exact (hg n x (le_trans (hu n) hux)) hcof

end OpenProblemFormalizations.CohenCoherence
