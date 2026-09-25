import OpenProblemFormalizations.IdealWebs.FiniteSelectors

/-!
The elementary set-theoretic skeleton of the crossing construction used in
the candidate answer to The bounded topology, Conjecture 4.14. This file does
not construct the required Tsirelson submeasure or prove the no-sun theorem.
-/

namespace OpenProblemFormalizations.IdealWebs

open Set

/-- Rows active at time `m`: a row has begun and still has a point at or after `m`. -/
def crossingRows (m : ℕ) (a : Set (ℕ × ℕ)) : Set ℕ :=
  {n | n ≤ m ∧ ∃ t, m ≤ t ∧ (n, t) ∈ a}

theorem crossingRows_mono (m : ℕ) {a b : Set (ℕ × ℕ)}
    (hab : a ⊆ b) : crossingRows m a ⊆ crossingRows m b := by
  rintro n ⟨hn, t, hmt, hta⟩
  exact ⟨hn, t, hmt, hab hta⟩

theorem crossingRows_union (m : ℕ) (a b : Set (ℕ × ℕ)) :
    crossingRows m (a ∪ b) = crossingRows m a ∪ crossingRows m b := by
  ext n
  constructor
  · rintro ⟨hn, t, hmt, htab⟩
    rcases htab with hta | htb
    · exact Or.inl ⟨hn, t, hmt, hta⟩
    · exact Or.inr ⟨hn, t, hmt, htb⟩
  · rintro (⟨hn, t, hmt, hta⟩ | ⟨hn, t, hmt, htb⟩)
    · exact ⟨hn, t, hmt, Or.inl hta⟩
    · exact ⟨hn, t, hmt, Or.inr htb⟩

theorem crossingRows_finite (m : ℕ) (a : Set (ℕ × ℕ)) :
    (crossingRows m a).Finite := by
  exact (finite_le_nat m).subset (fun n hn => hn.1)

/-- Union of complete rows indexed by `s`. -/
def completeRows (s : Set ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 ∈ s}

theorem crossingRows_completeRows (m : ℕ) (s : Set ℕ) :
    crossingRows m (completeRows s) = s ∩ Set.Iic m := by
  ext n
  simp only [crossingRows, completeRows, mem_setOf_eq, mem_inter_iff, mem_Iic]
  constructor
  · rintro ⟨hn, t, hmt, hns⟩
    exact ⟨hns, hn⟩
  · rintro ⟨hns, hn⟩
    exact ⟨hn, m, le_refl m, hns⟩

/-- Boundedness of the crossing gauge, phrased without extended reals. -/
def crossingBounded (rho : Set ℕ → ℕ) (a : Set (ℕ × ℕ)) : Prop :=
  ∃ C, ∀ m, rho (crossingRows m a) ≤ C

theorem crossingBounded_mono {rho : Set ℕ → ℕ}
    (hrho : Monotone rho) {a b : Set (ℕ × ℕ)}
    (hab : a ⊆ b) (hb : crossingBounded rho b) :
    crossingBounded rho a := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, ?_⟩
  intro m
  exact (hrho (crossingRows_mono m hab)).trans (hC m)

theorem crossingBounded_union {rho : Set ℕ → ℕ}
    (hsub : ∀ s t : Set ℕ, rho (s ∪ t) ≤ rho s + rho t)
    {a b : Set (ℕ × ℕ)} (ha : crossingBounded rho a)
    (hb : crossingBounded rho b) : crossingBounded rho (a ∪ b) := by
  obtain ⟨Ca, ha⟩ := ha
  obtain ⟨Cb, hb⟩ := hb
  refine ⟨Ca + Cb, ?_⟩
  intro m
  rw [crossingRows_union]
  exact (hsub _ _).trans (Nat.add_le_add (ha m) (hb m))

/-- If the row gauge grows without bound along initial segments of every
infinite set, the union of those complete rows is outside the crossing ideal. -/
theorem completeRows_not_crossingBounded {rho : Set ℕ → ℕ}
    (hunb : ∀ s : Set ℕ, s.Infinite → ∀ C, ∃ m, C < rho (s ∩ Set.Iic m))
    {s : Set ℕ} (hs : s.Infinite) :
    ¬ crossingBounded rho (completeRows s) := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := hunb s hs C
  have hCm : rho (s ∩ Set.Iic m) ≤ C := by
    simpa [crossingRows_completeRows] using hC m
  exact Nat.not_lt_of_ge hCm hm

end OpenProblemFormalizations.IdealWebs
