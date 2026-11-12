module
public import NearCritical.Section9PivotalSupport

/-! Actual deleted-cluster boundary closure and source deletion compatibility. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

private theorem cluster_boundary_available_adj {d : ℕ} {ω : Configuration d}
    (L Q F : Finset (Vertex d)) (b : Bond d)
    (hb : b ∈ sprinklingAvailableBonds L Q F) (hopen : ω b = true) :
    (sprinklingUnexploredGraph ω L Q F).Adj b.1 (bondTip b) := by
  obtain ⟨hbL,hbNot⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨hbase,htip⟩ := (mem_internalBondSet L b).mp hbL
  refine ⟨⟨b,hopen,Or.inl ⟨rfl,rfl⟩⟩,hbase,htip,?_⟩
  intro he
  apply hbNot
  exact (mem_clusterRevealBonds Q F b).mpr
    ((pair_mem_exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)) b.1 (bondTip b)).mp he)

/-- An available bond with exactly one endpoint in the actual deleted
component must be closed. Bonds internal to the component are unrestricted. -/
theorem section9_actual_cluster_crossing_bond_closed {d : ℕ} (ω : Configuration d)
    (L Q F : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ L) (b : Bond d)
    (hb : b ∈ sprinklingAvailableBonds L Q F)
    (hcross :
      (b.1 ∈ sprinklingUnexploredCluster ω L Q F root ∧
        bondTip b ∉ sprinklingUnexploredCluster ω L Q F root) ∨
      (bondTip b ∈ sprinklingUnexploredCluster ω L Q F root ∧
        b.1 ∉ sprinklingUnexploredCluster ω L Q F root)) :
    ω b = false := by
  cases hopen : ω b with
  | false => rfl
  | true =>
    have hadj := cluster_boundary_available_adj L Q F b hb hopen
    have hbL := (mem_internalBondSet L b).mp (Finset.mem_sdiff.mp hb).1
    rcases hcross with ⟨hbase,htip⟩ | ⟨htip,hbase⟩
    · have hreach := ((mem_sprinklingUnexploredCluster ω L Q F root b.1).mp hbase).2
      exact (htip ((mem_sprinklingUnexploredCluster ω L Q F root (bondTip b)).mpr
        ⟨hbL.2,hreach.trans hadj.reachable⟩)).elim
    · have hreach := ((mem_sprinklingUnexploredCluster ω L Q F root (bondTip b)).mp htip).2
      exact (hbase ((mem_sprinklingUnexploredCluster ω L Q F root b.1).mpr
        ⟨hbL.1,hreach.trans hadj.symm.reachable⟩)).elim

/-- A right-available bond wholly inside L is left-available under the actual
source separation R∩Q₁=∅. The two deleted-edge conventions are checked explicitly. -/
theorem section9_right_available_inside_left_available {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (hRQ₁ : Disjoint R Q₁) (b : Bond d)
    (hbR : b ∈ sprinklingAvailableBonds R Q₃ F₃)
    (hbaseL : b.1 ∈ L) (htipL : bondTip b ∈ L) :
    b ∈ sprinklingAvailableBonds L Q₁ F₁ := by
  apply Finset.mem_sdiff.mpr
  refine ⟨(mem_internalBondSet L b).mpr ⟨hbaseL,htipL⟩,?_⟩
  intro hbQ
  have hbInternalR := (mem_internalBondSet R b).mp (Finset.mem_sdiff.mp hbR).1
  have hbInternalQ := (mem_clusterRevealBonds Q₁ F₁ b).mp hbQ
  exact Finset.disjoint_left.mp hRQ₁ hbInternalR.1 hbInternalQ.1

/-- On an actual left-cluster fiber, a right-available bond crossing C and
wholly inside L is closed. Only crossing bonds are asserted closed. -/
theorem section9_right_crossing_bond_closed_on_left_cluster_fiber {d : ℕ}
    (ω : Configuration d) (L R Q₁ F₁ Q₃ F₃ C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ L)
    (hC : sprinklingUnexploredCluster ω L Q₁ F₁ root = C)
    (hRQ₁ : Disjoint R Q₁) (b : Bond d)
    (hbR : b ∈ sprinklingAvailableBonds R Q₃ F₃)
    (hbaseL : b.1 ∈ L) (htipL : bondTip b ∈ L)
    (hcross : (b.1 ∈ C ∧ bondTip b ∉ C) ∨ (bondTip b ∈ C ∧ b.1 ∉ C)) :
    ω b = false := by
  apply section9_actual_cluster_crossing_bond_closed ω L Q₁ F₁ root hroot b
    (section9_right_available_inside_left_available L R Q₁ F₁ Q₃ F₃ hRQ₁ b hbR hbaseL htipL)
  simpa only [hC] using hcross

end NearCritical
