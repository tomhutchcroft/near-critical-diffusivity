module

public import NearCritical.Section9TwoLayerTransfer
public import NearCritical.Section10UnconditionalStep

/-! Transfer of step events from the revealed law to the product law.

* `revealed_prod_eq_of_readsOnly`: an event reading a finite set of layered
  bonds whose critical-layer part avoids the explored bonds of both revealed
  clusters has the same probability under `revealedLaw x P_q` and `P_p x P_q`.
* `stepReadSet_fresh`: the read set of a step is such a set, when the left tube
  misses the far cube, the right tube misses the near cube, and the middle
  region misses both.
* `openedTargets_prod_eq`: hence the opened-target count event of
  `section9_source_many_opened_pivotal_targets` has the same probability under
  the conditional law of Section 9 and under the unconditional product law.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem revealed_prod_eq_of_readsOnly {d : ℕ} (p q : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (U : Finset (LBond d)) (P : Configuration d × Configuration d → Prop)
    (hP : ReadsOnly U P)
    (hfresh : ∀ b : Bond d, ((false, b) : LBond d) ∈ U →
      b ∉ clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) :
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real {z | P z} =
      ((percolation d p).prod (percolation d q)).real {z | P z} := by
  refine section9_revealed_prod_eq p q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
    ((U.filter (fun e => e.1 = false)).image Prod.snd) ?_ _ hP.measurableSet ?_
  · rw [Finset.disjoint_right]
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨heU, he1⟩ := Finset.mem_filter.mp he
    have : ((false, e.2) : LBond d) ∈ U := by
      have h : e = (false, e.2) := Prod.ext he1 rfl
      rw [← h]
      exact heU
    exact hfresh e.2 this
  · intro ω θ hagree η
    have h : P (ω, η) = P (θ, η) := by
      refine hP _ _ (fun e he => ?_)
      obtain ⟨l, b⟩ := e
      cases l with
      | false =>
        exact hagree b (Finset.mem_image.mpr ⟨(false, b), Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩)
      | true => rfl
    show P (ω, η) ↔ P (θ, η)
    rw [h]

theorem stepReadSet_fresh {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) (hMQ₁ : Disjoint M Q₁)
    (hMQ₃ : Disjoint M Q₃) :
    ∀ b : Bond d, ((false, b) : LBond d) ∈ stepReadSet M L R Q₁ F₁ Q₃ F₃ →
      b ∉ clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃ := by
  intro b hb hrev
  unfold stepReadSet at hb
  have hcrit : b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃ ∪
      internalBondSet M := by
    rcases Finset.mem_union.mp hb with h | h
    · obtain ⟨b', hb', hbb⟩ := Finset.mem_image.mp h
      rw [← (Prod.mk.inj hbb).2]
      exact hb'
    · obtain ⟨b', _, hbb⟩ := Finset.mem_image.mp h
      exact absurd (Prod.mk.inj hbb).1 (by simp)
  have hQ₁ : b ∈ clusterRevealBonds Q₁ F₁ → b.1 ∈ Q₁ :=
    fun h => ((mem_clusterRevealBonds _ _ _).mp h).1
  have hQ₃ : b ∈ clusterRevealBonds Q₃ F₃ → b.1 ∈ Q₃ :=
    fun h => ((mem_clusterRevealBonds _ _ _).mp h).1
  rcases Finset.mem_union.mp hcrit with h | h
  · rcases Finset.mem_union.mp h with h1 | h1
    · obtain ⟨hint, hnot⟩ := Finset.mem_sdiff.mp h1
      have hbL : b.1 ∈ L := ((mem_internalBondSet _ _).mp hint).1
      rcases Finset.mem_union.mp hrev with hr | hr
      · exact hnot hr
      · exact Finset.disjoint_left.mp hLQ₃ hbL (hQ₃ hr)
    · obtain ⟨hint, hnot⟩ := Finset.mem_sdiff.mp h1
      have hbR : b.1 ∈ R := ((mem_internalBondSet _ _).mp hint).1
      rcases Finset.mem_union.mp hrev with hr | hr
      · exact Finset.disjoint_left.mp hRQ₁ hbR (hQ₁ hr)
      · exact hnot hr
  · have hbM : b.1 ∈ M := ((mem_internalBondSet _ _).mp h).1
    rcases Finset.mem_union.mp hrev with hr | hr
    · exact Finset.disjoint_left.mp hMQ₁ hbM (hQ₁ hr)
    · exact Finset.disjoint_left.mp hMQ₃ hbM (hQ₃ hr)

/-- **The opened-target count has the same law under the conditional and the
product measure.** -/
theorem openedTargets_prod_eq {d : ℕ} (p q : unitInterval)
    (M L R Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) (hMQ₁ : Disjoint M Q₁)
    (hMQ₃ : Disjoint M Q₃)
    {ι : Type*} (I : Finset ι) (targets : ι → Finset (Vertex d)) (A : Finset (Vertex d))
    (m : ℕ) :
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
      {z : Configuration d × Configuration d | (m : ℝ) < ((I.filter fun j =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} =
    ((percolation d p).prod (percolation d q)).real
      {z : Configuration d × Configuration d | (m : ℝ) < ((I.filter fun j =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} := by
  have hP : ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃)
      (fun z : Configuration d × Configuration d => (m : ℝ) < ((I.filter fun j =>
        ((stepView M L R Q₁ F₁ Q₃ F₃ z).2.2.1 A (targets j)).Nonempty).card : ℝ)) :=
    (stepView_readsOnly M L R Q₁ F₁ Q₃ F₃).comp (fun v => (m : ℝ) < ((I.filter fun j =>
      (v.2.2.1 A (targets j)).Nonempty).card : ℝ))
  exact revealed_prod_eq_of_readsOnly p q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos _ _ hP
    (stepReadSet_fresh M L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁ hMQ₁ hMQ₃)

end NearCritical.Section10
