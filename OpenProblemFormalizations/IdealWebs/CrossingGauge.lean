import OpenProblemFormalizations.IdealWebs.FiniteSelectors
import OpenProblemFormalizations.IdealWebs.CountableLevels
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite

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

/-- Rows on which a set has infinitely many points. -/
def infiniteRows (a : Set (ℕ × ℕ)) : Set ℕ :=
  {n | {t : ℕ | (n, t) ∈ a}.Infinite}

/-- Every infinite row is active at every time after its row index. -/
theorem infiniteRows_initial_subset_crossingRows (m : ℕ) (a : Set (ℕ × ℕ)) :
    infiniteRows a ∩ Set.Iic m ⊆ crossingRows m a := by
  intro n hn
  obtain ⟨hrow, hnm⟩ := hn
  have htail : ∃ t, m ≤ t ∧ (n, t) ∈ a := by
    by_contra h
    have hsubset : {t : ℕ | (n, t) ∈ a} ⊆ Set.Iic m := by
      intro t ht
      exact Nat.le_of_lt (Nat.lt_of_not_ge (fun hmt => h ⟨t, hmt, ht⟩))
    exact hrow ((finite_le_nat m).subset hsubset)
  exact ⟨hnm, htail⟩

/-- A bounded crossing set has only finitely many infinite rows whenever
the row gauge is unbounded on each infinite set. -/
theorem infiniteRows_finite_of_crossingBounded {rho : Set ℕ → ℕ}
    (hrho : Monotone rho)
    (hunb : ∀ s : Set ℕ, s.Infinite → ∀ C, ∃ m, C < rho (s ∩ Set.Iic m))
    {a : Set (ℕ × ℕ)} (ha : crossingBounded rho a) :
    (infiniteRows a).Finite := by
  by_contra hinf
  have hinf' : (infiniteRows a).Infinite := hinf
  obtain ⟨C, hC⟩ := ha
  obtain ⟨m, hm⟩ := hunb (infiniteRows a) hinf' C
  have hle := hrho (infiniteRows_initial_subset_crossingRows m a)
  exact Nat.not_lt_of_ge (hle.trans (hC m)) hm

/-- One complete row of the crossing grid. -/
def fullRow (n : ℕ) : Set (ℕ × ℕ) := completeRows {n}

theorem fullRow_crossingBounded {rho : Set ℕ → ℕ}
    (hrho : Monotone rho) (n : ℕ) :
    crossingBounded rho (fullRow n) := by
  refine ⟨rho {n}, ?_⟩
  intro m
  rw [fullRow, crossingRows_completeRows]
  exact hrho Set.inter_subset_left

theorem sUnion_fullRow_image (s : Set ℕ) :
    ⋃₀ (fullRow '' s) = completeRows s := by
  ext p
  simp [fullRow, completeRows]

/-- Complete rows give a countable sun for any row gauge that diverges on
every infinite set of row indices. -/
theorem fullRows_seqSun {rho : Set ℕ → ℕ}
    (hunb : ∀ s : Set ℕ, s.Infinite → ∀ C, ∃ m, C < rho (s ∩ Set.Iic m)) :
    SeqSun {a | crossingBounded rho a} fullRow := by
  intro s hs
  rw [sUnion_fullRow_image]
  exact completeRows_not_crossingBounded hunb hs

/-- A finite-coordinate formulation of being in the Cantor closure of `w`.
The equivalence with topological closure is not used in this module. -/
def FiniteCoordinateApprox {α : Type*} (w : Set (Set α)) (a : Set α) : Prop :=
  ∀ f : Finset α, ∃ b ∈ w, ∀ x ∈ f, (x ∈ b ↔ x ∈ a)

/-- Finite sets lying in one complete row. -/
def finiteRowFamily : Set (Set (ℕ × ℕ)) :=
  {a | a.Finite ∧ ∃ n, a ⊆ fullRow n}

theorem fullRow_finiteCoordinateApprox (n : ℕ) :
    FiniteCoordinateApprox finiteRowFamily (fullRow n) := by
  intro f
  refine ⟨fullRow n ∩ (f : Set (ℕ × ℕ)), ?_, ?_⟩
  · constructor
    · exact f.finite_toSet.subset (by intro x hx; exact hx.2)
    · exact ⟨n, Set.inter_subset_left⟩
  · intro x hx
    simp [hx]

theorem finiteCoordinateClosure_not_seqWeb {rho : Set ℕ → ℕ}
    (hunb : ∀ s : Set ℕ, s.Infinite → ∀ C, ∃ m, C < rho (s ∩ Set.Iic m)) :
    ¬ SeqWeb {a | crossingBounded rho a}
      {a | FiniteCoordinateApprox finiteRowFamily a} := by
  intro hweb
  obtain ⟨s, hs, hbounded⟩ := hweb fullRow fullRow_finiteCoordinateApprox
  exact (fullRows_seqSun hunb) s hs hbounded

/-- A sequence of single-row sets whose later rows start beyond every point
of each earlier set has at most one active row at each time. -/
theorem separatedRows_crossingRows_subsingleton
    (a : ℕ → Set (ℕ × ℕ)) (r : ℕ → ℕ)
    (hrow : ∀ i, a i ⊆ fullRow (r i))
    (hsep : ∀ i j, i < j → ∀ t, (r i, t) ∈ a i → t < r j)
    (m : ℕ) :
    (crossingRows m (⋃ i, a i)).Subsingleton := by
  intro n hn n' hn'
  obtain ⟨hnm, t, hmt, ht⟩ := hn
  obtain ⟨hnm', t', hmt', ht'⟩ := hn'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht'
  have hni : n = r i := by
    have h := hrow i hi
    simpa [fullRow, completeRows] using h
  have hnj : n' = r j := by
    have h := hrow j hj
    simpa [fullRow, completeRows] using h
  rcases lt_trichotomy i j with hij | hij | hji
  · have hlt : t < r j := hsep i j hij t (hni ▸ hi)
    omega
  · subst j
    omega
  · have hlt : t' < r i := hsep j i hji t' (hnj ▸ hj)
    omega

/-- The time-separated branch of the finite-row web thinning argument. -/
theorem separatedRows_crossingBounded {rho : Set ℕ → ℕ} (hrho : Monotone rho)
    (C : ℕ) (hunit : ∀ n, rho {n} ≤ C)
    (a : ℕ → Set (ℕ × ℕ)) (r : ℕ → ℕ)
    (hrow : ∀ i, a i ⊆ fullRow (r i))
    (hsep : ∀ i j, i < j → ∀ t, (r i, t) ∈ a i → t < r j) :
    crossingBounded rho (⋃ i, a i) := by
  refine ⟨C, ?_⟩
  intro m
  have hsingle := separatedRows_crossingRows_subsingleton a r hrow hsep m
  by_cases hne : (crossingRows m (⋃ i, a i)).Nonempty
  · obtain ⟨n, hn⟩ := hne
    have hsub : crossingRows m (⋃ i, a i) ⊆ {n} := by
      intro x hx
      exact Set.mem_singleton_iff.mpr (hsingle hx hn)
    exact (hrho hsub).trans (hunit n)
  · have hsub : crossingRows m (⋃ i, a i) ⊆ {0} := by
      intro x hx
      exact (hne ⟨x, hx⟩).elim
    exact (hrho hsub).trans (hunit 0)

/-- A sequence with finite fibers eventually has an arbitrarily large row
beyond any prescribed index. -/
theorem finiteFibers_exists_later_row (r : ℕ → ℕ)
    (hfinite : ∀ n, (r ⁻¹' {n}).Finite) (k B : ℕ) :
    ∃ i, k < i ∧ B < r i := by
  by_contra h
  have hsmall : (r ⁻¹' Set.Iic B).Finite :=
    (finite_le_nat B).preimage' (fun n _ => hfinite n)
  have hsub : Set.Ici (k + 1) ⊆ r ⁻¹' Set.Iic B := by
    intro i hi
    change k + 1 ≤ i at hi
    change r i ≤ B
    apply Nat.le_of_not_gt
    intro hgt
    exact h ⟨i, by omega, hgt⟩
  exact (Set.Ici_infinite (k + 1)) (hsmall.subset hsub)

theorem finiteSet_second_bounded (a : Set (ℕ × ℕ)) (ha : a.Finite) :
    ∃ B : ℕ, ∀ p ∈ a, p.2 ≤ B := by
  classical
  let f := ha.toFinset
  refine ⟨f.sup (fun p => p.2), ?_⟩
  intro p hp
  exact Finset.le_sup (ha.mem_toFinset.mpr hp)

/-- The row-finite case of the web thinning: pass to a sequence whose row
indices begin strictly beyond every earlier selected time coordinate. -/
theorem finiteFibers_separated_subsequence
    (f : ℕ → Set (ℕ × ℕ)) (r : ℕ → ℕ)
    (hfinite : ∀ i, (f i).Finite)
    (hfinfib : ∀ n, (r ⁻¹' {n}).Finite) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ i j, i < j → ∀ t, (r (s i), t) ∈ f (s i) → t < r (s j) := by
  classical
  choose B hB using fun i => finiteSet_second_bounded (f i) (hfinite i)
  let step : ℕ → ℕ := fun i =>
    Classical.choose (finiteFibers_exists_later_row r hfinfib i (max (r i) (B i)))
  have hstep (i : ℕ) : i < step i ∧ max (r i) (B i) < r (step i) := by
    exact Classical.choose_spec (finiteFibers_exists_later_row r hfinfib i _)
  let s : ℕ → ℕ := fun k => Nat.rec (step 0) (fun _ i => step i) k
  have hs (k : ℕ) : s (k + 1) = step (s k) := rfl
  have hsmono : StrictMono s := strictMono_nat_of_lt_succ (fun k => by
    rw [hs]
    exact (hstep (s k)).1)
  have hrmono : StrictMono (fun k => r (s k)) := strictMono_nat_of_lt_succ (fun k => by
    rw [hs]
    exact lt_of_le_of_lt (le_max_left _ _) (hstep (s k)).2)
  refine ⟨s, hsmono, ?_⟩
  intro i j hij t ht
  have hbt : t ≤ B (s i) := hB (s i) (r (s i), t) ht
  have hnext : max (r (s i)) (B (s i)) < r (s (i + 1)) := by
    rw [hs]
    exact (hstep (s i)).2
  have hle : r (s (i + 1)) ≤ r (s j) :=
    hrmono.monotone (Nat.succ_le_iff.mpr hij)
  omega

/-- The finite single-row family really is a sequence-web whenever singleton
row gauges have one common bound. This is the missing web half of the crossing
counterexample's elementary combinatorial skeleton. -/
theorem finiteRowFamily_seqWeb {rho : Set ℕ → ℕ} (hrho : Monotone rho)
    (C : ℕ) (hunit : ∀ n, rho {n} ≤ C) :
    SeqWeb {a | crossingBounded rho a} finiteRowFamily := by
  classical
  intro f hf
  have hfinite (i : ℕ) : (f i).Finite := (hf i).1
  choose r hr using fun i => (hf i).2
  by_cases hsame : ∃ n, (r ⁻¹' {n}).Infinite
  · obtain ⟨n, hn⟩ := hsame
    refine ⟨r ⁻¹' {n}, hn, ?_⟩
    apply crossingBounded_mono hrho ?_ (fullRow_crossingBounded hrho n)
    intro p hp
    obtain ⟨b, ⟨i, hi, rfl⟩, hpb⟩ := hp
    change r i = n at hi
    simpa [hi] using (hr i hpb)
  · have hfinfib (n : ℕ) : (r ⁻¹' {n}).Finite := by
      by_contra h
      exact hsame ⟨n, h⟩
    obtain ⟨s, hsmono, hsep⟩ :=
      finiteFibers_separated_subsequence f r hfinite hfinfib
    refine ⟨Set.range s, Set.infinite_range_of_injective hsmono.injective, ?_⟩
    have hEq : ⋃₀ (f '' Set.range s) = ⋃ k, f (s k) := by
      ext p
      simp
    rw [hEq]
    exact separatedRows_crossingBounded hrho C hunit
      (fun k => f (s k)) (fun k => r (s k)) (fun k => hr (s k)) hsep

end OpenProblemFormalizations.IdealWebs
