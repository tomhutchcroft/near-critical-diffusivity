module

public import NearCritical.Section10SemanticRule
public import NearCritical.Section10BridgeTypicality
public import NearCritical.Section9PivotalSupport
public import NearCritical.Section9CandidateCount
public import NearCritical.Section9PivotOpening

/-! Locality of one sprinkling step (source `lem.skl.independent`, deterministic
part).

For regions `L`, `R`, `Mid` and revealed unions `F₁`, `F₃` in the cubes `Q₁`,
`Q₃`, all objects of the step
* the unexplored graphs on `L` and `R`,
* the opened pivotal pairs for any source and target sets,
* the sprinkling clusters and the coalescing sites,
computed from the critical layer `z.1` and the supercritical configuration
`z.1 OR z.2`, read only `stepReadSet`: the critical layer on the available bonds
of `L`, `R` and on the bonds of `Mid`, and the sprinkle layer on the bonds of
`Mid`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Opened pivotal pairs only read the available critical bonds and the joining
bonds of the middle region. -/
theorem sprinkledPivotalPairs_eq_of_agree {d : ℕ}
    (M L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (ω ω' η η' : Configuration d)
    (hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = ω' b)
    (hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = ω' b)
    (hM : ∀ b ∈ internalBondSet M, η b = η' b) :
    sprinkledPivotalPairs ω η (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B =
      sprinkledPivotalPairs ω' η' (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B := by
  have open_eq (e : Vertex d × Vertex d) (he : e ∈ orientedLatticePairs M) :
      (openGraph η).Adj e.1 e.2 ↔ (openGraph η').Adj e.1 e.2 := by
    obtain ⟨hx, hy, _⟩ := (mem_orientedLatticePairs M e.1 e.2).mp he
    have transport (α β : Configuration d)
        (h : ∀ b ∈ internalBondSet M, α b = β b) :
        (openGraph α).Adj e.1 e.2 → (openGraph β).Adj e.1 e.2 := by
      rintro ⟨b, hb, hends⟩
      have hbM : b ∈ internalBondSet M := by
        apply (mem_internalBondSet M b).mpr
        rcases hends with ⟨hbase, htip⟩ | ⟨hbase, htip⟩
        · exact ⟨hbase ▸ hx, htip ▸ hy⟩
        · exact ⟨hbase ▸ hy, htip ▸ hx⟩
      exact ⟨b, (h b hbM).symm.trans hb, hends⟩
    exact ⟨transport η η' hM, transport η' η (fun b hb => (hM b hb).symm)⟩
  ext e
  simp only [sprinkledPivotalPairs, sprinklingPivotalPairs, Finset.mem_filter]
  have hpivot := sprinklingPivotalPair_iff_of_available_agree
    L R Q₁ F₁ Q₃ F₃ A B ω ω' hL hR e
  constructor
  · rintro ⟨⟨he, hp⟩, ho⟩
    exact ⟨⟨he, hpivot.mp hp⟩, (open_eq e he).mp ho⟩
  · rintro ⟨⟨he, hp⟩, ho⟩
    exact ⟨⟨he, hpivot.mpr hp⟩, (open_eq e he).mpr ho⟩

theorem section9SprinklingCluster_eq_of_agree {d : ℕ}
    (M L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (ω ω' η η' : Configuration d)
    (hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = ω' b)
    (hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = ω' b)
    (hM : ∀ b ∈ internalBondSet M, η b = η' b) :
    section9SprinklingCluster ω η (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B =
      section9SprinklingCluster ω' η' (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B := by
  unfold section9SprinklingCluster
  rw [sprinkledPivotalPairs_eq_of_agree M L R Q₁ F₁ Q₃ F₃ A B ω ω' η η' hL hR hM]
  refine Finset.biUnion_congr rfl (fun e _ => ?_)
  rw [sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω ω' hL e.1,
    sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω ω' hR e.2]

theorem bridgeCoalescingSites_eq_of_agree {d : ℕ}
    (M L R Q₁ F₁ Q₃ F₃ A face B : Finset (Vertex d)) (ω ω' η η' : Configuration d)
    (hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = ω' b)
    (hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = ω' b)
    (hM : ∀ b ∈ internalBondSet M, η b = η' b) :
    bridgeCoalescingSites ω η (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A face B =
      bridgeCoalescingSites ω' η' (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A face B := by
  unfold bridgeCoalescingSites
  refine Finset.filter_congr (fun x _ => ?_)
  rw [section9SprinklingCluster_eq_of_agree M L R Q₁ F₁ Q₃ F₃ {x} B ω ω' η η' hL hR hM,
    section9SprinklingCluster_eq_of_agree M L R Q₁ F₁ Q₃ F₃ A B ω ω' η η' hL hR hM]

/-- The layered bonds read by one step. -/
def stepReadSet {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) : Finset (LBond d) :=
  ((sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃ ∪
      internalBondSet M).image (fun b => ((false, b) : LBond d))) ∪
    (internalBondSet M).image (fun b => ((true, b) : LBond d))

/-- Everything a step computes, as one function of the configuration pair. -/
def stepView {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (z : Configuration d × Configuration d) :
    SimpleGraph (Vertex d) × SimpleGraph (Vertex d) ×
      (Finset (Vertex d) → Finset (Vertex d) → Finset (Vertex d × Vertex d)) ×
      (Finset (Vertex d) → Finset (Vertex d) → Finset (Vertex d) → Finset (Vertex d)) :=
  (sprinklingUnexploredGraph z.1 L Q₁ F₁, sprinklingUnexploredGraph z.1 R Q₃ F₃,
    fun A B => sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
      (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B,
    fun A face B => bridgeCoalescingSites z.1 (sprinkleOrConfiguration z.1 z.2)
      (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A face B)

/-- **Locality of a step.** -/
theorem stepView_readsOnly {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) :
    ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃) (stepView M L R Q₁ F₁ Q₃ F₃) := by
  intro z z' hz
  have hcrit : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃ ∪
      internalBondSet M, z.1 b = z'.1 b := by
    intro b hb
    exact hz ((false, b) : LBond d)
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
  have hspr : ∀ b ∈ internalBondSet M, z.2 b = z'.2 b := by
    intro b hb
    exact hz ((true, b) : LBond d)
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
  have hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, z.1 b = z'.1 b := fun b hb =>
    hcrit b (Finset.mem_union_left _ (Finset.mem_union_left _ hb))
  have hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, z.1 b = z'.1 b := fun b hb =>
    hcrit b (Finset.mem_union_left _ (Finset.mem_union_right _ hb))
  have hM : ∀ b ∈ internalBondSet M,
      sprinkleOrConfiguration z.1 z.2 b = sprinkleOrConfiguration z'.1 z'.2 b := by
    intro b hb
    unfold sprinkleOrConfiguration
    rw [hcrit b (Finset.mem_union_right _ hb), hspr b hb]
  unfold stepView
  rw [sprinklingUnexploredGraph_eq_of_available_agree L Q₁ F₁ z.1 z'.1 hL,
    sprinklingUnexploredGraph_eq_of_available_agree R Q₃ F₃ z.1 z'.1 hR]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · funext A B
    exact sprinkledPivotalPairs_eq_of_agree M L R Q₁ F₁ Q₃ F₃ A B _ _ _ _ hL hR hM
  · funext A face B
    exact bridgeCoalescingSites_eq_of_agree M L R Q₁ F₁ Q₃ F₃ A face B _ _ _ _ hL hR hM

end NearCritical.Section10
