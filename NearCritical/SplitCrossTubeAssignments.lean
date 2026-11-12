module

public import NearCritical.SplitCrossTotalOverlap

/-! Relate the recursive sums used in the error proof to a finite set of
terminal assignments. Each index occurs once. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open scoped Classical BigOperators

private theorem sum_pi_insert {ι α : Type*} [DecidableEq ι] (Y : ι → Finset α)
    (s : Finset ι) (i : ι) (hi : i ∉ s)
    (F : (∀ j ∈ insert i s, α) → ℝ) :
    (∑ f ∈ (insert i s).pi Y, F f) =
      ∑ y ∈ Y i, ∑ f ∈ s.pi Y, F (Finset.Pi.cons s i y f) := by
  have hdis : ∀ y ∈ Y i, ∀ z ∈ Y i, y ≠ z →
      Disjoint ((s.pi Y).image (Finset.Pi.cons s i y)) ((s.pi Y).image (Finset.Pi.cons s i z)) := by
    intro y _ z _ hne
    rw [Finset.disjoint_left]
    intro g hg hg'
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hg
    obtain ⟨f', _, hf'⟩ := Finset.mem_image.mp hg'
    have he : Finset.Pi.cons s i y f i (Finset.mem_insert_self _ _) =
        Finset.Pi.cons s i z f' i (Finset.mem_insert_self _ _) :=
      congrFun (congrFun (hf.trans hf'.symm) i) _
    rw [Finset.Pi.cons_same, Finset.Pi.cons_same] at he
    exact hne he
  rw [Finset.pi_insert hi, Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_image (fun _ _ _ _ h => Finset.Pi.cons_injective hi h)]

private theorem sumTubeChoices_eq_dep_pi {d : ℕ} {U : Finset (Vertex d)} {ι α : Type*}
    [DecidableEq ι] (Y : ι → Finset α) (E : ι → α → TEdge d U) :
    ∀ (l : List ι), l.Nodup → ∀ (s : Finset ι), s = l.toFinset →
      ∀ (H : ∀ i ∈ l, i ∈ s) (F : List (TEdge d U) → ℝ),
      sumTubeChoices Y E l F =
        ∑ p ∈ s.pi Y, F (l.pmap (fun i hi => E i (p i hi)) H)
  | [], _, s, hs, H, F => by
    have he : s = ∅ := by simpa using hs
    subst s
    simp [sumTubeChoices, List.pmap]
  | i :: l, hn, s, hs, H, F => by
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hn
    have hs' : s = insert i l.toFinset := by simpa only [List.toFinset_cons] using hs
    clear hs
    subst s
    rw [sum_pi_insert Y _ _ (by simpa using hi)]
    unfold sumTubeChoices
    apply Finset.sum_congr rfl
    intro y _
    rw [sumTubeChoices_eq_dep_pi Y E l hl l.toFinset rfl (fun _ hj => List.mem_toFinset.mpr hj)]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    simp only [List.pmap, Finset.Pi.cons_same]
    congr 1
    apply List.pmap_congr_left
    intro j hj _ _
    congr 1
    have hne : j ≠ i := fun h => hi (by simpa only [h] using hj)
    rw [Finset.Pi.cons_ne hne.symm]

/-- The recursive sum agrees with the finite sum over full assignments
when the list enumerates the entire index type. -/
theorem sumTubeChoices_eq_piFinset {d : ℕ} {U : Finset (Vertex d)} {ι α : Type*}
    [Fintype ι] [DecidableEq ι] (Y : ι → Finset α) (E : ι → α → TEdge d U)
    (l : List ι) (hn : l.Nodup) (hcover : ∀ i, i ∈ l) (F : List (TEdge d U) → ℝ) :
    sumTubeChoices Y E l F = ∑ p ∈ Fintype.piFinset Y, F (l.map (fun i => E i (p i))) := by
  have hs : (Finset.univ : Finset ι) = l.toFinset := by
    ext i
    simp [hcover i]
  rw [sumTubeChoices_eq_dep_pi Y E l hn Finset.univ hs (fun i _ => Finset.mem_univ i)]
  rw [Finset.sum_univ_pi]
  simp only [List.pmap_eq_map]

end NearCritical.SplitCrossDirect
