module

public import NearCritical.Section10CoupledPairMass

/-! The joint order of steps of two chains (source 5550), built from labels.

Each chain reads, at its step `t`, the block `Bl (lab t)` of a label (a tube, a
start site, an exit site). A rank on labels increases strictly along each chain
(in the source: level, then vertical before horizontal). `mergeSched` merges the
two label sequences by rank, a common label being a single shared step.

* `mergeSched_leftCount`, `mergeSched_rightCount`: each chain makes all its steps.
* `mergeSched_fresh`: if blocks of distinct labels are disjoint and the explored
  set is disjoint from all blocks still to be read, the joint exploration is
  fresh (`PairFresh`). This is the hypothesis of `revealed_pair_mass_le`.
* `mergeSched_sharedCount_le`: the number of shared steps is at most the number
  of common labels.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

variable {E : Type*}

/-- Joint schedule of two chains with `m` and `m'` steps to go from times `t`, `t'`. -/
def mergeSched (rank : E → ℕ) (lab lab' : ℕ → E) : ℕ → ℕ → ℕ → ℕ → List PairMove
  | 0, 0, _, _ => []
  | m+1, 0, t, t' => PairMove.left :: mergeSched rank lab lab' m 0 (t+1) t'
  | 0, m'+1, t, t' => PairMove.right :: mergeSched rank lab lab' 0 m' t (t'+1)
  | m+1, m'+1, t, t' =>
      if lab t = lab' t' then PairMove.both :: mergeSched rank lab lab' m m' (t+1) (t'+1)
      else if rank (lab t) ≤ rank (lab' t') then
        PairMove.left :: mergeSched rank lab lab' m (m'+1) (t+1) t'
      else PairMove.right :: mergeSched rank lab lab' (m+1) m' t (t'+1)
termination_by m m' => m + m'

theorem mergeSched_leftCount (rank : E → ℕ) (lab lab' : ℕ → E) :
    ∀ (n m m' t t' : ℕ), m + m' ≤ n →
      leftCount (mergeSched rank lab lab' m m' t t') = m := by
  intro n
  induction n with
  | zero =>
    intro m m' t t' h
    obtain ⟨rfl, rfl⟩ : m = 0 ∧ m' = 0 := by omega
    rw [mergeSched]
    rfl
  | succ n ih =>
    intro m m' t t' h
    rcases m with _ | m <;> rcases m' with _ | m'
    · rw [mergeSched]
      rfl
    · rw [mergeSched, leftCount]
      exact ih 0 m' t (t'+1) (by omega)
    · rw [mergeSched, leftCount, ih m 0 (t+1) t' (by omega)]
    · rw [mergeSched]
      split_ifs
      · rw [leftCount, ih m m' (t+1) (t'+1) (by omega)]
      · rw [leftCount, ih m (m'+1) (t+1) t' (by omega)]
      · rw [leftCount]
        exact ih (m+1) m' t (t'+1) (by omega)

theorem mergeSched_rightCount (rank : E → ℕ) (lab lab' : ℕ → E) :
    ∀ (n m m' t t' : ℕ), m + m' ≤ n →
      rightCount (mergeSched rank lab lab' m m' t t') = m' := by
  intro n
  induction n with
  | zero =>
    intro m m' t t' h
    obtain ⟨rfl, rfl⟩ : m = 0 ∧ m' = 0 := by omega
    rw [mergeSched]
    rfl
  | succ n ih =>
    intro m m' t t' h
    rcases m with _ | m <;> rcases m' with _ | m'
    · rw [mergeSched]
      rfl
    · rw [mergeSched, rightCount, ih 0 m' t (t'+1) (by omega)]
    · rw [mergeSched, rightCount]
      exact ih m 0 (t+1) t' (by omega)
    · rw [mergeSched]
      split_ifs
      · rw [rightCount, ih m m' (t+1) (t'+1) (by omega)]
      · rw [rightCount]
        exact ih m (m'+1) (t+1) t' (by omega)
      · rw [rightCount, ih (m+1) m' t (t'+1) (by omega)]

/-- The merged schedule is a fresh joint exploration. -/
theorem mergeSched_fresh {d : ℕ} (rank : E → ℕ) (lab lab' : ℕ → E)
    (Bl : E → Finset (LBond d)) (hBl : ∀ a b, a ≠ b → Disjoint (Bl a) (Bl b))
    (hlab : StrictMono (fun t => rank (lab t))) (hlab' : StrictMono (fun t => rank (lab' t))) :
    ∀ (n m m' t t' : ℕ) (R : Finset (LBond d)), m + m' ≤ n →
      (∀ s, t ≤ s → s < t + m → Disjoint R (Bl (lab s))) →
      (∀ s, t' ≤ s → s < t' + m' → Disjoint R (Bl (lab' s))) →
      PairFresh (fun t => Bl (lab t)) (fun t => Bl (lab' t))
        (mergeSched rank lab lab' m m' t t') t t' R := by
  have hne : ∀ s u, s < u → lab s ≠ lab u := by
    intro s u hsu h
    have := hlab hsu
    simp only [h, lt_irrefl] at this
  have hne' : ∀ s u, s < u → lab' s ≠ lab' u := by
    intro s u hsu h
    have := hlab' hsu
    simp only [h, lt_irrefl] at this
  intro n
  induction n with
  | zero =>
    intro m m' t t' R h _ _
    obtain ⟨rfl, rfl⟩ : m = 0 ∧ m' = 0 := by omega
    rw [mergeSched]
    trivial
  | succ n ih =>
    intro m m' t t' R h hR hR'
    rcases m with _ | m <;> rcases m' with _ | m'
    · rw [mergeSched]
      trivial
    · rw [mergeSched, PairFresh]
      refine ⟨hR' t' le_rfl (by omega), ih 0 m' t (t'+1) _ (by omega) ?_ ?_⟩
      · intro s h1 h2
        omega
      · intro s h1 h2
        rw [Finset.disjoint_union_left]
        exact ⟨hR' s (by omega) (by omega), hBl _ _ (hne' t' s (by omega))⟩
    · rw [mergeSched, PairFresh]
      refine ⟨hR t le_rfl (by omega), ih m 0 (t+1) t' _ (by omega) ?_ ?_⟩
      · intro s h1 h2
        rw [Finset.disjoint_union_left]
        exact ⟨hR s (by omega) (by omega), hBl _ _ (hne t s (by omega))⟩
      · intro s h1 h2
        omega
    · rw [mergeSched]
      split_ifs with h1 h2
      · rw [PairFresh]
        refine ⟨?_, ih m m' (t+1) (t'+1) _ (by omega) ?_ ?_⟩
        · rw [Finset.disjoint_union_right]
          exact ⟨hR t le_rfl (by omega), hR' t' le_rfl (by omega)⟩
        · intro s h3 h4
          rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
          refine ⟨hR s (by omega) (by omega), hBl _ _ (hne t s (by omega)), ?_⟩
          rw [← h1]
          exact hBl _ _ (hne t s (by omega))
        · intro s h3 h4
          rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
          refine ⟨hR' s (by omega) (by omega), ?_, hBl _ _ (hne' t' s (by omega))⟩
          rw [h1]
          exact hBl _ _ (hne' t' s (by omega))
      · rw [PairFresh]
        refine ⟨hR t le_rfl (by omega), ih m (m'+1) (t+1) t' _ (by omega) ?_ ?_⟩
        · intro s h3 h4
          rw [Finset.disjoint_union_left]
          exact ⟨hR s (by omega) (by omega), hBl _ _ (hne t s (by omega))⟩
        · intro s h3 h4
          rw [Finset.disjoint_union_left]
          refine ⟨hR' s h3 h4, hBl _ _ ?_⟩
          intro heq
          rcases Nat.eq_or_lt_of_le h3 with h5 | h5
          · rw [← h5] at heq
            exact h1 heq
          · have := hlab' h5
            simp only [← heq] at this
            omega
      · rw [PairFresh]
        refine ⟨hR' t' le_rfl (by omega), ih (m+1) m' t (t'+1) _ (by omega) ?_ ?_⟩
        · intro s h3 h4
          rw [Finset.disjoint_union_left]
          refine ⟨hR s h3 h4, hBl _ _ ?_⟩
          intro heq
          have hmono := hlab.monotone h3
          simp only [← heq] at hmono
          omega
        · intro s h3 h4
          rw [Finset.disjoint_union_left]
          exact ⟨hR' s (by omega) (by omega), hBl _ _ (hne' t' s (by omega))⟩

/-- Shared steps are common labels. -/
theorem mergeSched_sharedCount_le (rank : E → ℕ) (lab lab' : ℕ → E)
    (hlab : StrictMono (fun t => rank (lab t))) (hlab' : StrictMono (fun t => rank (lab' t))) :
    ∀ (n m m' t t' : ℕ), m + m' ≤ n →
      sharedCount (mergeSched rank lab lab' m m' t t') ≤
        ((Finset.Ico t (t+m)).image lab ∩ (Finset.Ico t' (t'+m')).image lab').card := by
  have hne : ∀ s u, s < u → lab s ≠ lab u := by
    intro s u hsu h
    have := hlab hsu
    simp only [h, lt_irrefl] at this
  intro n
  induction n with
  | zero =>
    intro m m' t t' h
    obtain ⟨rfl, rfl⟩ : m = 0 ∧ m' = 0 := by omega
    rw [mergeSched]
    exact Nat.zero_le _
  | succ n ih =>
    intro m m' t t' h
    have hsubL : ∀ m, (Finset.Ico (t+1) (t+1+m)).image lab ⊆
        (Finset.Ico t (t+(m+1))).image lab := fun m =>
      Finset.image_subset_image (fun s hs => by
        rw [Finset.mem_Ico] at hs ⊢
        omega)
    have hsubR : ∀ m', (Finset.Ico (t'+1) (t'+1+m')).image lab' ⊆
        (Finset.Ico t' (t'+(m'+1))).image lab' := fun m' =>
      Finset.image_subset_image (fun s hs => by
        rw [Finset.mem_Ico] at hs ⊢
        omega)
    rcases m with _ | m <;> rcases m' with _ | m'
    · rw [mergeSched]
      exact Nat.zero_le _
    · rw [mergeSched, sharedCount]
      exact (ih 0 m' t (t'+1) (by omega)).trans
        (Finset.card_le_card (Finset.inter_subset_inter (le_refl _) (hsubR m')))
    · rw [mergeSched, sharedCount]
      exact (ih m 0 (t+1) t' (by omega)).trans
        (Finset.card_le_card (Finset.inter_subset_inter (hsubL m) (le_refl _)))
    · rw [mergeSched]
      split_ifs with h1 h2
      · rw [sharedCount]
        refine Nat.succ_le_of_lt (lt_of_le_of_lt (ih m m' (t+1) (t'+1) (by omega)) ?_)
        apply Finset.card_lt_card
        refine ⟨Finset.inter_subset_inter (hsubL m) (hsubR m'), fun hss => ?_⟩
        have hmem : lab t ∈ (Finset.Ico t (t+(m+1))).image lab ∩
            (Finset.Ico t' (t'+(m'+1))).image lab' := by
          rw [Finset.mem_inter]
          refine ⟨Finset.mem_image.mpr ⟨t, by rw [Finset.mem_Ico]; omega, rfl⟩,
            Finset.mem_image.mpr ⟨t', by rw [Finset.mem_Ico]; omega, h1.symm⟩⟩
        have h3 := Finset.mem_of_mem_inter_left (hss hmem)
        obtain ⟨s, hs, hsl⟩ := Finset.mem_image.mp h3
        rw [Finset.mem_Ico] at hs
        exact hne t s (by omega) hsl.symm
      · rw [sharedCount]
        exact (ih m (m'+1) (t+1) t' (by omega)).trans
          (Finset.card_le_card (Finset.inter_subset_inter (hsubL m) (le_refl _)))
      · rw [sharedCount]
        exact (ih (m+1) m' t (t'+1) (by omega)).trans
          (Finset.card_le_card (Finset.inter_subset_inter (le_refl _) (hsubR m')))

end NearCritical.Section10
