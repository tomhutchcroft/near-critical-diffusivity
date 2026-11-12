module

public import NearCritical.Section9ClosedCertificate

/-! Actual finite forcing witnesses for the nonmonotone avoidance event. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- A deleted-graph walk has a finite positive certificate on its actual
physical edges. Its forcing conclusion retains the SAME explored-edge deletion. -/
theorem sprinklingUnexploredWalk_certificate {d : ℕ} {ω : Configuration d}
    (T Q F : Finset (Vertex d)) {x y : Vertex d}
    (w : (sprinklingUnexploredGraph ω T Q F).Walk x y) :
    ∃ P : Finset (Bond d), (∀ b ∈ P, ω b = true) ∧
      (∀ b ∈ P, s(b.1,bondTip b) ∈ w.edges) ∧
      ∀ θ : Configuration d, (∀ b ∈ P, θ b = true) →
        (sprinklingUnexploredGraph θ T Q F).Reachable x y := by
  induction w with
  | nil => exact ⟨∅,by simp,by simp,fun _ _ => .refl _⟩
  | @cons x z y hxz w ih =>
    obtain ⟨P,hopen,hedge,hforce⟩ := ih
    obtain ⟨b,_,hb,hends⟩ := sprinklingUnexplored_adj_available_bond T Q F hxz
    have hed : s(b.1,bondTip b) = s(x,z) := by
      rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rfl
      · exact Sym2.eq_swap
    refine ⟨insert b P,?_,?_,?_⟩
    · intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hb
      · exact hopen c hc
    · intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl hed
      · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (hedge c hc)
    · intro θ hθ
      have hhead : (sprinklingUnexploredGraph θ T Q F).Adj x z :=
        ⟨⟨b,hθ b (Finset.mem_insert_self _ _),hends⟩,hxz.2⟩
      exact hhead.reachable.trans (hforce θ (fun c hc => hθ c (Finset.mem_insert_of_mem hc)))

/-- The source avoidance event: a connection in D, excluding a connection to
V in the larger tube T, with the same fixed explored-edge deletion. -/
def section9AvoidanceEvent {d : ℕ} (D T Q F B V : Finset (Vertex d))
    (root : Vertex d) : Set (Configuration d) :=
  {θ | (sprinklingUnexploredCluster θ D Q F root ∩ B).Nonempty ∧
    ¬ (sprinklingUnexploredCluster θ T Q F root ∩ V).Nonempty}

/-- Positive walk bits and negative closed bits jointly force the actual
nonmonotone event, and these two finite witnesses are disjoint. No probability
product bound follows from this lemma alone. -/
theorem section9AvoidanceEvent_certificate {d : ℕ} (ω : Configuration d)
    (D T Q F B V : Finset (Vertex d)) {root y : Vertex d}
    (hroot : root ∈ D) (hy : y ∈ B)
    (w : (sprinklingUnexploredGraph ω D Q F).Walk root y)
    (hnon : ¬ (sprinklingUnexploredCluster ω T Q F root ∩ V).Nonempty) :
    ∃ P : Finset (Bond d), (∀ b ∈ P, ω b = true) ∧
      (∀ b ∈ P, s(b.1,bondTip b) ∈ w.edges) ∧
      Disjoint P (section9ClosedAvailableBonds ω T Q F) ∧
      ForcesOn (section9AvoidanceEvent D T Q F B V root) ω
        ((P ∪ section9ClosedAvailableBonds ω T Q F : Finset (Bond d)) : Set (Bond d)) := by
  obtain ⟨P,hopen,hedge,hforce⟩ := sprinklingUnexploredWalk_certificate D Q F w
  have hneg := section9ClosedAvailable_forces_nonhit ω T Q F V root hnon
  have hyD : y ∈ D := microscopicWalk_support w hroot y w.end_mem_support
  refine ⟨P,hopen,hedge,(section9ClosedAvailable_disjoint_open ω T Q F P hopen).symm,?_⟩
  intro θ hagree
  have hθP : ∀ b ∈ P, θ b = true := by
    intro b hb
    exact (hagree b (Finset.mem_union.mpr (Or.inl hb))).trans (hopen b hb)
  have hθN : ∀ b ∈ section9ClosedAvailableBonds ω T Q F, θ b = ω b := by
    intro b hb
    exact hagree b (Finset.mem_union.mpr (Or.inr hb))
  refine ⟨?_,hneg θ hθN⟩
  exact ⟨y,Finset.mem_inter.mpr
    ⟨(mem_sprinklingUnexploredCluster θ D Q F root y).mpr ⟨hyD,hforce θ hθP⟩,hy⟩⟩

end NearCritical
