module

public import NearCritical.Section10OffspringTransfer

/-! Offspring versus opened targets.

* `openedTargets_subset_offspring` (deterministic): a candidate whose own target
  patch is joined to `A` by an opened pivotal pair is an offspring of `A` (the
  pair is also pivotal for the union of all target patches).
* `offspringFailure_le`: hence, under the product law, if more than `m`
  candidates are joined with probability at least `1 - eps` and `N <= m + 1`,
  then fewer than `N` offspring occur with probability at most `eps`. This is
  the hypothesis `hoff` of `NestLayout.moveSuccess_ge` in terms of the count
  event of the Section 9 theorem.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem openedTargets_subset_offspring {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d))
    (cand : Finset (Finset (Vertex d))) (tgt : Finset (Vertex d) → Finset (Vertex d)) :
    (cand.filter fun c =>
        (sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A (tgt c)).Nonempty) ⊆
      sprinklingOffspring (sprinklingUnexploredGraph ω L Q₁ F₁)
        (sprinklingUnexploredGraph ω R Q₃ F₃) A cand tgt
        (sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A (sprinklingTargetBoundary cand tgt)) := by
  intro c hc
  obtain ⟨hcc, ⟨e, he⟩⟩ := Finset.mem_filter.mp hc
  obtain ⟨hpm, hopen⟩ := Finset.mem_filter.mp he
  obtain ⟨hE, hadj, h1L, h2R, ⟨x, hx⟩, ⟨y, hy⟩, hdisj⟩ := Finset.mem_filter.mp hpm
  obtain ⟨hxc, hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyc, hyT⟩ := Finset.mem_inter.mp hy
  have hxr := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxc).2
  have hyr := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mp hyc).2
  have hyAll : y ∈ sprinklingTargetBoundary cand tgt := mem_sprinklingTargetBoundary cand tgt hcc hyT
  have he' : e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A
      (sprinklingTargetBoundary cand tgt) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hE, hadj, h1L, h2R, ⟨x, hx⟩,
      ⟨y, Finset.mem_inter.mpr ⟨hyc, hyAll⟩⟩, hdisj⟩, hopen⟩
  exact (mem_sprinklingOffspring _ _ _ _ _ _ c).mpr ⟨hcc, x, hxA, y, hyT, e, he', hxr, hyr⟩

theorem offspringFailure_le {d : ℕ} (p q : unitInterval)
    (M L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d)) (cand : Finset (Finset (Vertex d)))
    (tgt : Finset (Vertex d) → Finset (Vertex d)) (N m : ℕ) (hNm : N ≤ m + 1) {ε : ℝ}
    (hopen : 1 - ε ≤ ((percolation d p).prod (percolation d q)).real
      {z : Configuration d × Configuration d | (m : ℝ) < ((cand.filter fun c =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (tgt c)).Nonempty).card : ℝ)}) :
    ((percolation d p).prod (percolation d q)).real
      {z : Configuration d × Configuration d |
        ¬ N ≤ (sprinklingOffspring (stepView M L R Q₁ F₁ Q₃ F₃ z).1
          (stepView M L R Q₁ F₁ Q₃ F₃ z).2.1 A cand tgt
          ((stepView M L R Q₁ F₁ Q₃ F₃ z).2.2.1 A
            (sprinklingTargetBoundary cand tgt))).card} ≤ ε := by
  have hP : ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃)
      (fun z : Configuration d × Configuration d => (m : ℝ) < ((cand.filter fun c =>
        ((stepView M L R Q₁ F₁ Q₃ F₃ z).2.2.1 A (tgt c)).Nonempty).card : ℝ)) :=
    (stepView_readsOnly M L R Q₁ F₁ Q₃ F₃).comp (fun v => (m : ℝ) < ((cand.filter fun c =>
      (v.2.2.1 A (tgt c)).Nonempty).card : ℝ))
  have hmeas : MeasurableSet {z : Configuration d × Configuration d |
      (m : ℝ) < ((cand.filter fun c =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (tgt c)).Nonempty).card : ℝ)} :=
    hP.measurableSet
  have hcompl := measureReal_compl (μ := (percolation d p).prod (percolation d q)) hmeas
  have hsub : {z : Configuration d × Configuration d |
        ¬ N ≤ (sprinklingOffspring (stepView M L R Q₁ F₁ Q₃ F₃ z).1
          (stepView M L R Q₁ F₁ Q₃ F₃ z).2.1 A cand tgt
          ((stepView M L R Q₁ F₁ Q₃ F₃ z).2.2.1 A
            (sprinklingTargetBoundary cand tgt))).card} ⊆
      {z : Configuration d × Configuration d | (m : ℝ) < ((cand.filter fun c =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (tgt c)).Nonempty).card : ℝ)}ᶜ := by
    intro z hz hin
    apply hz
    have hlt : m < (cand.filter fun c =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (tgt c)).Nonempty).card := by
      exact_mod_cast hin
    have hle := Finset.card_le_card (openedTargets_subset_offspring z.1
      (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A cand tgt)
    exact (hNm.trans hlt).trans hle
  have h1 := measureReal_mono (μ := (percolation d p).prod (percolation d q)) hsub
    (measure_ne_top _ _)
  rw [hcompl] at h1
  have huniv : ((percolation d p).prod (percolation d q)).real Set.univ = 1 := by simp
  rw [huniv] at h1
  linarith

end NearCritical.Section10
