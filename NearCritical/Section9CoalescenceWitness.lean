module

public import NearCritical.Section9SprinklingCluster
public import NearCritical.Section9ClusterPartition

@[expose] public section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- A coalescing pair comes with one open pivot for each root and a common
vertex in the two corresponding unions of deleted-edge components. -/
theorem section9_coalescence_open_pivot_witness {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (x y : Vertex d)
    (h : (section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {x} B ∩
      section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty) :
    ∃ e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {x} B,
      ∃ f ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {y} B,
        ∃ z : Vertex d,
          (z ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∨
            z ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2) ∧
          (z ∈ sprinklingUnexploredCluster ω L Q₁ F₁ f.1 ∨
            z ∈ sprinklingUnexploredCluster ω R Q₃ F₃ f.2) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hz
  obtain ⟨e, he, hzE⟩ :=
    (mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {x} B z).mp hx
  obtain ⟨f, hf, hzF⟩ :=
    (mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {y} B z).mp hy
  exact ⟨e, he, f, hf, z, hzE, hzF⟩

/-- A single pivot cannot witness both roots when no left deleted-edge
component contains both. This separates the one-pivot and two-pivot cases. -/
theorem section9_coalescence_pivots_ne_of_no_common_left {d : ℕ}
    (ω η : Configuration d) (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    {e f : Vertex d × Vertex d}
    (he : e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {x} B)
    (hf : f ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {y} B)
    (hleft : ∀ u, ¬ (x ∈ sprinklingUnexploredCluster ω L Q₁ F₁ u ∧
      y ∈ sprinklingUnexploredCluster ω L Q₁ F₁ u)) : e ≠ f := by
  intro hef
  subst f
  have hsource (v : Vertex d)
      (hv : e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {v} B) :
      v ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 := by
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
    obtain ⟨z, hz⟩ := hp.2.2.2.1
    obtain ⟨hzC, hzv⟩ := Finset.mem_inter.mp hz
    simpa only [Finset.mem_singleton.mp hzv] using hzC
  exact hleft e.1 ⟨hsource x he, hsource y hf⟩

/-- In the two-pivot case the independent openings are on distinct
physical bonds. The cross-component exclusion rules out reversal. -/
theorem section9_coalescence_physical_pivots_ne {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    {e f : Vertex d × Vertex d}
    (he : e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {x} B)
    (hf : f ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {y} B)
    (hleft : ∀ u, ¬ (x ∈ sprinklingUnexploredCluster ω L Q₁ F₁ u ∧
      y ∈ sprinklingUnexploredCluster ω L Q₁ F₁ u))
    (hcross : Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
      (sprinklingUnexploredCluster ω L Q₁ F₁ f.1)) :
    s(e.1,e.2) ≠ s(f.1,f.2) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨_,h₂⟩
  · exact section9_coalescence_pivots_ne_of_no_common_left ω η E L R Q₁ F₁ Q₃ F₃ B
      x y he hf hleft (Prod.ext h₁ h₂)
  · have heP := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    have hfP := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
    have hr := root_mem_sprinklingUnexploredCluster ω R Q₃ F₃ heP.2.2.1
    have hl := root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hfP.2.1
    exact (Finset.disjoint_left.mp hcross) hr (by simpa only [h₂] using hl)

/-- Distinct sprinkle coordinates contribute the square of the opening
probability. The event is the cylinder over the two physical bonds. -/
theorem section9_two_bond_opening {d : ℕ} (q : unitInterval) {e f : Bond d}
    (hef : e ≠ f) :
    percolation d q {η | η e = true ∧ η f = true} =
      (↑(unitInterval.toNNReal q) : ENNReal)^2 := by
  classical
  have hset : {η : Configuration d | η e = true ∧ η f = true} =
      Set.pi (↑({e,f} : Finset (Bond d)) : Set (Bond d)) (fun _ => ({true} : Set Bool)) := by
    ext η
    simp [Set.mem_pi]
  rw [hset, percolation, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  rw [Finset.prod_insert (by simpa using hef), Finset.prod_singleton]
  simp [bernoulliMeasure_apply_of_mem_of_notMem, pow_two]

/-- A critical-configuration event and two distinct fresh sprinkle
openings contribute separate factors under the independent reveal law. -/
theorem section9_critical_event_two_bond_opening {d : ℕ} (p q : unitInterval)
    (A : Set (Configuration d)) {e f : Bond d} (hef : e ≠ f) :
    ((percolation d p).prod (percolation d q))
      (A ×ˢ {η | η e = true ∧ η f = true}) =
      percolation d p A * (↑(unitInterval.toNNReal q) : ENNReal)^2 := by
  rw [Measure.prod_prod, section9_two_bond_opening q hef]

/-- The remaining coalescence case has a shared right component after
the left-left and both cross intersections have been excluded. -/
theorem section9_coalescence_shared_right {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (x y : Vertex d)
    (h : (section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {x} B ∩
      section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty)
    (hexclude : ∀ e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {x} B,
      ∀ f ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {y} B,
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
          (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) ∧
        Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
          (sprinklingUnexploredCluster ω L Q₁ F₁ f.1)) :
    ∃ e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {x} B,
      ∃ f ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ {y} B,
        sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
          sprinklingUnexploredCluster ω R Q₃ F₃ f.2 := by
  obtain ⟨e, he, f, hf, z, hzE, hzF⟩ :=
    section9_coalescence_open_pivot_witness ω η E L R Q₁ F₁ Q₃ F₃ B x y h
  obtain ⟨hLL, hLR, hRL⟩ := hexclude e he f hf
  refine ⟨e, he, f, hf, ?_⟩
  rcases hzE with hzL | hzR <;> rcases hzF with hzL' | hzR'
  · exact ((Finset.disjoint_left.mp hLL) hzL hzL').elim
  · exact ((Finset.disjoint_left.mp hLR) hzL hzR').elim
  · exact ((Finset.disjoint_left.mp hRL) hzR hzL').elim
  · exact sprinklingUnexploredCluster_eq_of_inter_nonempty ω R Q₃ F₃ e.2 f.2
      ⟨z, Finset.mem_inter.mpr ⟨hzR, hzR'⟩⟩

/-- The shared right component connects both pivot heads to one target
root, in the same deleted-edge graph. -/
theorem section9_shared_right_three_terminals {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e)
    (hf : f.2 ∈ R)
    (hshared : sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
      sprinklingUnexploredCluster ω R Q₃ F₃ f.2) :
    ∃ y ∈ B, (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable e.2 f.2 ∧
      (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable e.2 y := by
  obtain ⟨y, hy⟩ := he.2.2.2.2.1
  obtain ⟨hyC, hyB⟩ := Finset.mem_inter.mp hy
  have hfC : f.2 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2 := by
    rw [hshared]
    exact root_mem_sprinklingUnexploredCluster ω R Q₃ F₃ hf
  exact ⟨y, hyB, ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 f.2).mp hfC).2,
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mp hyC).2⟩

end NearCritical
