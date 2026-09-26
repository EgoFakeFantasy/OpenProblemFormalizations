import OpenProblemFormalizations.IdealSpectra.RectangularIdeal

/-!
# Cofinal maps and maps preserving unboundedness

These lemmas connect the cofinal-subset definition of `TukeyLE` used by
`RectangularIdeal` to the unbounded-set convention. The maps are constructed
in opposite directions. The proofs work for preorders, without assuming
directedness or nonemptiness.
-/

namespace OpenProblemFormalizations.IdealSpectra.CohesiveIdeal

open Set

universe u v w

/-- A map taking every unbounded set to an unbounded set. -/
def UnboundedMap {P : Type u} {Q : Type v} [LE P] [LE Q] (f : P → Q) : Prop :=
  ∀ a : Set P, ¬ BddAbove a → ¬ BddAbove (f '' a)

/-- A cofinal-subset map yields a reverse map preserving unbounded sets. -/
theorem exists_unboundedMap_of_cofinalMap
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    {f : Q → P} (hf : CofinalMap f) :
    ∃ g : P → Q, UnboundedMap g := by
  classical
  have htail (p : P) : ∃ q : Q, ∀ r : Q, q ≤ r → p ≤ f r := by
    by_contra! h
    have hc : IsCofinal {q : Q | ¬ p ≤ f q} := by
      intro q
      obtain ⟨r, hqr, hr⟩ := h q
      exact ⟨r, hr, hqr⟩
    obtain ⟨s, ⟨q, hq, rfl⟩, hps⟩ := hf _ hc p
    exact hq hps
  let g (p : P) : Q := Classical.choose (htail p)
  refine ⟨g, ?_⟩
  intro a ha hbound
  obtain ⟨q, hq⟩ := hbound
  apply ha
  refine ⟨f q, ?_⟩
  intro p hp
  exact Classical.choose_spec (htail p) q (hq ⟨p, hp, rfl⟩)

/-- A map preserving unbounded sets yields a reverse cofinal-subset map. -/
theorem exists_cofinalMap_of_unboundedMap
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    {f : P → Q} (hf : UnboundedMap f) :
    ∃ g : Q → P, CofinalMap g := by
  classical
  have hbound (q : Q) : BddAbove {p : P | f p ≤ q} := by
    by_contra h
    apply hf _ h
    refine ⟨q, ?_⟩
    rintro r ⟨p, hp, rfl⟩
    exact hp
  let g (q : Q) : P := Classical.choose (hbound q)
  refine ⟨g, ?_⟩
  intro s hs p
  obtain ⟨q, hq, hfpq⟩ := hs (f p)
  exact ⟨g q, ⟨q, hq, rfl⟩, Classical.choose_spec (hbound q) hfpq⟩

theorem tukeyLE_iff_exists_unboundedMap
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q] :
    TukeyLE P Q ↔ ∃ f : P → Q, UnboundedMap f := by
  constructor
  · rintro ⟨f, hf⟩
    exact exists_unboundedMap_of_cofinalMap hf
  · rintro ⟨f, hf⟩
    exact exists_cofinalMap_of_unboundedMap hf

/-- Failure of Tukey reduction produces a bad unbounded set for every proposed map. -/
theorem exists_unbounded_bounded_image
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    (h : ¬ TukeyLE P Q) (f : P → Q) :
    ∃ a : Set P, ¬ BddAbove a ∧ BddAbove (f '' a) := by
  classical
  have hn : ¬ UnboundedMap f := fun hf =>
    h (tukeyLE_iff_exists_unboundedMap.mpr ⟨f, hf⟩)
  simpa only [UnboundedMap, not_forall, Classical.not_imp, not_not, exists_prop] using hn

theorem UnboundedMap.comp
    {P : Type u} {Q : Type v} {R : Type w} [LE P] [LE Q] [LE R]
    {f : P → Q} {g : Q → R} (hg : UnboundedMap g) (hf : UnboundedMap f) :
    UnboundedMap (g ∘ f) := by
  intro a ha
  simpa only [Set.image_image] using hg (f '' a) (hf a ha)

/-- Cohesiveness is upward closed for the existing cofinal-map Tukey order. -/
theorem cohesive_of_tukeyLE
    {X : Type u} {P : Type v} {Q : Type w} [Preorder P] [Preorder Q]
    {positive : Set X → Prop} (hPQ : TukeyLE P Q)
    (hP : Cohesive P positive) : Cohesive Q positive := by
  obtain ⟨f, hf⟩ := tukeyLE_iff_exists_unboundedMap.mp hPQ
  obtain ⟨g, hg⟩ := hP
  refine ⟨f ∘ g, ?_⟩
  intro a ha
  simpa only [Set.image_image] using hf (g '' a) (hg a ha)

end OpenProblemFormalizations.IdealSpectra.CohesiveIdeal
