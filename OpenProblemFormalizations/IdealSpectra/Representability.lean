import OpenProblemFormalizations.IdealSpectra.RectangularClassification

/-!
# When a rectangular cohesive class has a representative

For two nonempty linear factors without greatest elements, a representative
exists exactly when the two factors are Tukey comparable. The representative
is not assumed directed: its reduction to either factor forces directedness.
This is a structural consequence of the already proved slice classification,
not a claim of literature priority or a solution of the enhanced-spectrum question.
-/

namespace OpenProblemFormalizations.IdealSpectra.CohesiveIdeal

open Set

universe u v w

theorem tukeyLE_refl (P : Type u) [Preorder P] : TukeyLE P P := by
  refine ⟨id, ?_⟩
  intro a ha
  simpa using ha

theorem tukeyLE_trans
    {P : Type u} {Q : Type v} {R : Type w}
    [Preorder P] [Preorder Q] [Preorder R]
    (hPQ : TukeyLE P Q) (hQR : TukeyLE Q R) : TukeyLE P R := by
  obtain ⟨f, hf⟩ := hPQ
  obtain ⟨g, hg⟩ := hQR
  refine ⟨f ∘ g, ?_⟩
  intro a ha
  simpa only [Set.image_image] using hf (g '' a) (hg a ha)

theorem nonempty_of_tukeyLE
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q] [Nonempty Q]
    (h : TukeyLE P Q) : Nonempty P := by
  obtain ⟨f, _⟩ := h
  exact ⟨f (Classical.choice inferInstance)⟩

theorem directed_of_tukeyLE
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    (h : TukeyLE P Q)
    (hQ : ∀ a b : Q, ∃ c : Q, a ≤ c ∧ b ≤ c) :
    ∀ a b : P, ∃ c : P, a ≤ c ∧ b ≤ c := by
  obtain ⟨f, hf⟩ := tukeyLE_iff_exists_unboundedMap.mp h
  intro a b
  by_contra hn
  have hu : ¬ BddAbove ({a, b} : Set P) := by
    rintro ⟨c, hc⟩
    exact hn ⟨c, hc (by simp), hc (by simp)⟩
  obtain ⟨q, haq, hbq⟩ := hQ (f a) (f b)
  apply hf _ hu
  refine ⟨q, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact haq
  · exact hbq

/-- Universality is tested on nonempty directed preorders in the representative's universe.
The proposed representative itself is allowed to be an arbitrary preorder. -/
def RepresentsCohesiveClass {X : Type u} (positive : Set X → Prop)
    (P : Type v) [Preorder P] : Prop :=
  ∀ (Q : Type v) [Preorder Q], Nonempty Q →
    (∀ a b : Q, ∃ c : Q, a ≤ c ∧ b ≤ c) →
    (TukeyLE P Q ↔ Cohesive Q positive)

theorem rectangular_representative_forces_comparable
    {K L P : Type u} [LinearOrder K] [LinearOrder L] [Preorder P]
    [NoMaxOrder K] [NoMaxOrder L] [Nonempty K] [Nonempty L]
    (hrep : RepresentsCohesiveClass (RectPositive (κ := K) (lam := L)) P) :
    TukeyLE K L ∨ TukeyLE L K := by
  have hK : TukeyLE P K :=
    (hrep K inferInstance (fun a b => ⟨max a b, le_max_left _ _, le_max_right _ _⟩)).mpr
      fst_cohesive
  have hL : TukeyLE P L :=
    (hrep L inferInstance (fun a b => ⟨max a b, le_max_left _ _, le_max_right _ _⟩)).mpr
      snd_cohesive
  have hnP : Nonempty P := nonempty_of_tukeyLE hK
  have hdP : ∀ a b : P, ∃ c : P, a ≤ c ∧ b ≤ c :=
    directed_of_tukeyLE hK (fun a b => ⟨max a b, le_max_left _ _, le_max_right _ _⟩)
  have hcP := (hrep P hnP hdP).mp (tukeyLE_refl P)
  rcases rectangular_cohesive_iff.mp hcP with hKP | hLP
  · exact Or.inl (tukeyLE_trans hKP hL)
  · exact Or.inr (tukeyLE_trans hLP hK)

theorem left_represents_rectangular_of_tukeyLE
    {K L : Type u} [LinearOrder K] [LinearOrder L]
    [NoMaxOrder K] [NoMaxOrder L] [Nonempty K] [Nonempty L]
    (hKL : TukeyLE K L) :
    RepresentsCohesiveClass (RectPositive (κ := K) (lam := L)) K := by
  intro Q _ _ _
  rw [rectangular_cohesive_iff]
  constructor
  · exact Or.inl
  · rintro (hK | hL)
    · exact hK
    · exact tukeyLE_trans hKL hL

theorem right_represents_rectangular_of_tukeyLE
    {K L : Type u} [LinearOrder K] [LinearOrder L]
    [NoMaxOrder K] [NoMaxOrder L] [Nonempty K] [Nonempty L]
    (hLK : TukeyLE L K) :
    RepresentsCohesiveClass (RectPositive (κ := K) (lam := L)) L := by
  intro Q _ _ _
  rw [rectangular_cohesive_iff]
  constructor
  · exact Or.inr
  · rintro (hK | hL)
    · exact tukeyLE_trans hLK hK
    · exact hL

theorem rectangular_representable_iff
    {K L : Type u} [LinearOrder K] [LinearOrder L]
    [NoMaxOrder K] [NoMaxOrder L] [Nonempty K] [Nonempty L] :
    (∃ (P : Type u) (inst : Preorder P),
      @RepresentsCohesiveClass (K × L) (RectPositive (κ := K) (lam := L)) P inst) ↔
      TukeyLE K L ∨ TukeyLE L K := by
  constructor
  · rintro ⟨P, inst, hrep⟩
    letI : Preorder P := inst
    exact rectangular_representative_forces_comparable hrep
  · rintro (hKL | hLK)
    · exact ⟨K, inferInstance, left_represents_rectangular_of_tukeyLE hKL⟩
    · exact ⟨L, inferInstance, right_represents_rectangular_of_tukeyLE hLK⟩

end OpenProblemFormalizations.IdealSpectra.CohesiveIdeal
