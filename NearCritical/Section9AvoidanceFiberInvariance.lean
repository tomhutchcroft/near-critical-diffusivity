module
public import NearCritical.Section9ClusterBoundaryClosure
public import NearCritical.Section9AvoidanceCertificate
public import NearCritical.Section9RevealFiber
public import NearCritical.Section8PathSeparation
public import NearCritical.FiniteBlockResampling

/-! Actual fiber-mask closure preserves right avoidance under an explicit
exterior-entry guard. Internal cluster bits may change; external bonds remain fresh. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

private theorem fiber_open_bond_not_mask {d : ℕ} (ω : Configuration d)
    (L Q F C : Finset (Vertex d)) (root : Vertex d) (hr : root ∈ L)
    (hC : sprinklingUnexploredCluster ω L Q F root = C)
    (u : Vertex d) (b : Bond d) (hb : ω b = true)
    (hbase : b.1 ∈ C → b.1 = u) (htip : bondTip b ∈ C → bondTip b = u) :
    b ∉ sprinklingClusterFiberMask L Q F C := by
  intro hmask
  obtain ⟨havailable,htouch⟩ := Finset.mem_filter.mp hmask
  have hne : b.1 ≠ bondTip b :=
    (show (openGraph ω).Adj b.1 (bondTip b) from ⟨b,hb,Or.inl ⟨rfl,rfl⟩⟩).ne
  have hcross : (b.1 ∈ C ∧ bondTip b ∉ C) ∨ (bondTip b ∈ C ∧ b.1 ∉ C) := by
    rcases htouch with hbaseC | htipC
    · exact Or.inl ⟨hbaseC,fun htipC => hne ((hbase hbaseC).trans (htip htipC).symm)⟩
    · exact Or.inr ⟨htipC,fun hbaseC => hne ((hbase hbaseC).trans (htip htipC).symm)⟩
  have hclosed := section9_actual_cluster_crossing_bond_closed ω L Q F root hr b havailable
    (by simpa only [hC] using hcross)
  have hbad : (false : Bool) = true := hclosed.symm.trans hb
  cases hbad

private theorem fiber_first_entry_walk_transfer {d : ℕ} (ω θ : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ C : Finset (Vertex d)) (root : Vertex d) (hr : root ∈ L)
    (hC : sprinklingUnexploredCluster ω L Q₁ F₁ root = C)
    (hagree : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃,
      b ∉ sprinklingClusterFiberMask L Q₁ F₁ C → ω b = θ b)
    {a u : Vertex d} (w : (sprinklingUnexploredGraph ω R Q₃ F₃).Walk a u)
    (hfirst : ∀ x ∈ w.support, x ∈ C → x = u) :
    (sprinklingUnexploredGraph θ R Q₃ F₃).Reachable a u := by
  induction w with
  | nil => exact .refl _
  | @cons a c u hac w ih =>
    obtain ⟨b,hbR,hbOpen,hends⟩ := sprinklingUnexplored_adj_available_bond R Q₃ F₃ hac
    have hbase : b.1 ∈ (w.cons hac).support := by
      rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (w.cons hac).start_mem_support
      · exact List.mem_cons_of_mem _ w.start_mem_support
    have htip : bondTip b ∈ (w.cons hac).support := by
      rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact List.mem_cons_of_mem _ w.start_mem_support
      · exact (w.cons hac).start_mem_support
    have hbNot := fiber_open_bond_not_mask ω L Q₁ F₁ C root hr hC u b hbOpen
      (fun hbC => hfirst b.1 hbase hbC) (fun hbC => hfirst (bondTip b) htip hbC)
    have hbθ : θ b = true := (hagree b hbR hbNot).symm.trans hbOpen
    have hadjθ : (sprinklingUnexploredGraph θ R Q₃ F₃).Adj a c :=
      ⟨⟨b,hbθ,hends⟩,hac.2⟩
    exact hadjθ.reachable.trans (ih (fun x hx hxC =>
      hfirst x (List.mem_cons_of_mem _ hx) hxC))

private theorem fiber_first_entry_mem_target {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ C V : Finset (Vertex d))
    (root : Vertex d) (hr : root ∈ L)
    (hC : sprinklingUnexploredCluster ω L Q₁ F₁ root = C)
    (hRQ₁ : Disjoint R Q₁)
    (hExterior : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃,
      (b.1 ∈ C → bondTip b ∉ L → b.1 ∈ V) ∧
      (bondTip b ∈ C → b.1 ∉ L → bondTip b ∈ V))
    {v u : Vertex d} (hv : v ∉ C)
    (w : (sprinklingUnexploredGraph ω R Q₃ F₃).Walk v u)
    (hu : u ∈ C) (hfirst : ∀ x ∈ w.support, x ∈ C → x = u) : u ∈ V := by
  have huv : u ≠ v := fun heq => hv (heq ▸ hu)
  obtain ⟨a,hua,q,hrev⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne huv w.reverse
  have haRev : a ∈ w.reverse.support := by
    rw [hrev]
    exact List.mem_cons_of_mem _ q.start_mem_support
  have haSupport : a ∈ w.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using haRev
  have haC : a ∉ C := fun haC => hua.ne (hfirst a haSupport haC).symm
  have huL : u ∈ L := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ root u).mp
    (hC.symm ▸ hu)).1
  obtain ⟨b,hbR,hbOpen,hends⟩ := sprinklingUnexplored_adj_available_bond R Q₃ F₃ hua
  have haL : a ∉ L := by
    intro haL
    have hbaseL : b.1 ∈ L := by rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    have htipL : bondTip b ∈ L := by rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    have hcross : (b.1 ∈ C ∧ bondTip b ∉ C) ∨ (bondTip b ∈ C ∧ b.1 ∉ C) := by
      rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨hu,haC⟩
      · exact Or.inr ⟨hu,haC⟩
    have hc := section9_right_crossing_bond_closed_on_left_cluster_fiber ω
      L R Q₁ F₁ Q₃ F₃ C root hr hC hRQ₁ b hbR hbaseL htipL hcross
    have hbad : (false : Bool) = true := hc.symm.trans hbOpen
    cases hbad
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact (hExterior b hbR).1 hu haL
  · exact (hExterior b hbR).2 hu haL

/-- Closing the actual left fiber mask preserves right avoidance, provided
all possible entries from outside L into C already land in the forbidden target.
The configurations agree on every right-available coordinate outside that mask. -/
theorem section9_avoidance_iff_of_left_fiber_mask_closed {d : ℕ} (ω θ : Configuration d)
    (L R D Q₁ F₁ Q₃ F₃ C B V : Finset (Vertex d))
    (root : Vertex d) (hr : root ∈ L)
    (hC : sprinklingUnexploredCluster ω L Q₁ F₁ root = C)
    (hRQ₁ : Disjoint R Q₁) (hDR : D ⊆ R) {v : Vertex d} (hv : v ∈ D \ C)
    (hagree : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃,
      b ∉ sprinklingClusterFiberMask L Q₁ F₁ C → ω b = θ b)
    (hclosed : ∀ b ∈ sprinklingClusterFiberMask L Q₁ F₁ C, θ b = false)
    (hExterior : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃,
      (b.1 ∈ C → bondTip b ∉ L → b.1 ∈ V) ∧
      (bondTip b ∈ C → b.1 ∉ L → bondTip b ∈ V)) :
    (ω ∈ section9AvoidanceEvent (D \ C) R Q₃ F₃ B V v ↔
     θ ∈ section9AvoidanceEvent (D \ C) R Q₃ F₃ B V v) := by
  have hvR : v ∈ R := hDR (Finset.mem_sdiff.mp hv).1
  have hvC : v ∉ C := (Finset.mem_sdiff.mp hv).2
  have hpositive : sprinklingUnexploredCluster ω (D \ C) Q₃ F₃ v =
      sprinklingUnexploredCluster θ (D \ C) Q₃ F₃ v := by
    apply sprinklingUnexploredCluster_eq_of_available_agree
    intro b hb
    obtain ⟨hbInternal,hbNot⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hbase,htip⟩ := (mem_internalBondSet (D \ C) b).mp hbInternal
    have hbR : b ∈ sprinklingAvailableBonds R Q₃ F₃ := Finset.mem_sdiff.mpr
      ⟨(mem_internalBondSet R b).mpr
        ⟨hDR (Finset.mem_sdiff.mp hbase).1,hDR (Finset.mem_sdiff.mp htip).1⟩,hbNot⟩
    apply hagree b hbR
    intro hbS
    rcases (Finset.mem_filter.mp hbS).2 with hbaseC | htipC
    · exact (Finset.mem_sdiff.mp hbase).2 hbaseC
    · exact (Finset.mem_sdiff.mp htip).2 htipC
  have hle : sprinklingUnexploredGraph θ R Q₃ F₃ ≤ sprinklingUnexploredGraph ω R Q₃ F₃ := by
    intro a b hab
    obtain ⟨e,heAvailable,heOpen,hends⟩ := sprinklingUnexplored_adj_available_bond R Q₃ F₃ hab
    have heNot : e ∉ sprinklingClusterFiberMask L Q₁ F₁ C := by
      intro heS
      have hbad : (false : Bool) = true := (hclosed e heS).symm.trans heOpen
      cases hbad
    exact ⟨⟨e,(hagree e heAvailable heNot).trans heOpen,hends⟩,hab.2⟩
  have hhit : (sprinklingUnexploredCluster ω R Q₃ F₃ v ∩ V).Nonempty ↔
      (sprinklingUnexploredCluster θ R Q₃ F₃ v ∩ V).Nonempty := by
    constructor
    · rintro ⟨y,hy⟩
      obtain ⟨hyCluster,hyV⟩ := Finset.mem_inter.mp hy
      obtain ⟨hyR,hyReach⟩ := (mem_sprinklingUnexploredCluster ω R Q₃ F₃ v y).mp hyCluster
      obtain ⟨w⟩ := hyReach
      by_cases hvisit : ∃ x ∈ w.support, x ∈ C
      · obtain ⟨u,p,q,hpq,hu,hfirst⟩ := Section8.walk_first_hit w (C : Set (Vertex d)) hvisit
        have huV := fiber_first_entry_mem_target ω L R Q₁ F₁ Q₃ F₃ C V
          root hr hC hRQ₁ hExterior hvC p hu hfirst
        have huR : u ∈ R := microscopicWalk_support p hvR u p.end_mem_support
        have hθReach := fiber_first_entry_walk_transfer ω θ L R Q₁ F₁ Q₃ F₃ C
          root hr hC hagree p hfirst
        exact ⟨u,Finset.mem_inter.mpr
          ⟨(mem_sprinklingUnexploredCluster θ R Q₃ F₃ v u).mpr ⟨huR,hθReach⟩,huV⟩⟩
      · have hfirst : ∀ x ∈ w.support, x ∈ C → x = y :=
          fun x hx hxC => (hvisit ⟨x,hx,hxC⟩).elim
        have hθReach := fiber_first_entry_walk_transfer ω θ L R Q₁ F₁ Q₃ F₃ C
          root hr hC hagree w hfirst
        exact ⟨y,Finset.mem_inter.mpr
          ⟨(mem_sprinklingUnexploredCluster θ R Q₃ F₃ v y).mpr ⟨hyR,hθReach⟩,hyV⟩⟩
    · rintro ⟨y,hy⟩
      obtain ⟨hyCluster,hyV⟩ := Finset.mem_inter.mp hy
      obtain ⟨hyR,hyReach⟩ := (mem_sprinklingUnexploredCluster θ R Q₃ F₃ v y).mp hyCluster
      exact ⟨y,Finset.mem_inter.mpr
        ⟨(mem_sprinklingUnexploredCluster ω R Q₃ F₃ v y).mpr ⟨hyR,hyReach.mono hle⟩,hyV⟩⟩
  simp only [section9AvoidanceEvent,Set.mem_setOf_eq,hpositive,hhit]

/-- Specialize to closing exactly the actual left fiber mask. Bonds from C
to outside L are preserved, rather than incorrectly closed. -/
theorem section9_avoidance_iff_resample_left_fiber_mask_false {d : ℕ} (ω : Configuration d)
    (L R D Q₁ F₁ Q₃ F₃ C B V : Finset (Vertex d))
    (root : Vertex d) (hr : root ∈ L)
    (hC : sprinklingUnexploredCluster ω L Q₁ F₁ root = C)
    (hRQ₁ : Disjoint R Q₁) (hDR : D ⊆ R) {v : Vertex d} (hv : v ∈ D \ C)
    (hExterior : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃,
      (b.1 ∈ C → bondTip b ∉ L → b.1 ∈ V) ∧
      (bondTip b ∈ C → b.1 ∉ L → bondTip b ∈ V)) :
    (ω ∈ section9AvoidanceEvent (D \ C) R Q₃ F₃ B V v ↔
     resampleBonds (sprinklingClusterFiberMask L Q₁ F₁ C) ω (fun _ => false) ∈
       section9AvoidanceEvent (D \ C) R Q₃ F₃ B V v) := by
  apply section9_avoidance_iff_of_left_fiber_mask_closed ω
    (resampleBonds (sprinklingClusterFiberMask L Q₁ F₁ C) ω (fun _ => false))
    L R D Q₁ F₁ Q₃ F₃ C B V root hr hC hRQ₁ hDR hv
  · intro b _ hbNot
    simp only [resampleBonds,extendConfiguration,dif_neg hbNot]
  · intro b hb
    simp only [resampleBonds,extendConfiguration,dif_pos hb]
    rfl
  · exact hExterior

/-- For an arbitrary configuration, closing the left fiber mask can only
help suffix avoidance: positive suffix coordinates are untouched and the
larger nonhit graph only decreases. No actual-fiber hypothesis is needed. -/
theorem section9_avoidance_implies_resample_left_fiber_mask_false {d : ℕ}
    (ω : Configuration d) (L R D Q₁ F₁ Q₃ F₃ C B V : Finset (Vertex d))
    (v : Vertex d)
    (havoid : ω ∈ section9AvoidanceEvent (D \ C) R Q₃ F₃ B V v) :
    resampleBonds (sprinklingClusterFiberMask L Q₁ F₁ C) ω (fun _ => false) ∈
      section9AvoidanceEvent (D \ C) R Q₃ F₃ B V v := by
  let S := sprinklingClusterFiberMask L Q₁ F₁ C
  let θ := resampleBonds S ω (fun _ => false)
  have hpositive : sprinklingUnexploredCluster ω (D \ C) Q₃ F₃ v =
      sprinklingUnexploredCluster θ (D \ C) Q₃ F₃ v := by
    apply sprinklingUnexploredCluster_eq_of_available_agree
    intro b hb
    have hends := (mem_internalBondSet (D \ C) b).mp (Finset.mem_sdiff.mp hb).1
    have hbNot : b ∉ S := by
      intro hbS
      rcases (Finset.mem_filter.mp hbS).2 with hbaseC | htipC
      · exact (Finset.mem_sdiff.mp hends.1).2 hbaseC
      · exact (Finset.mem_sdiff.mp hends.2).2 htipC
    simp only [θ,resampleBonds,extendConfiguration,dif_neg hbNot]
  have hclosedagree : ∀ b ∈ section9ClosedAvailableBonds ω R Q₃ F₃, θ b = ω b := by
    intro b hb
    have hbClosed := (Finset.mem_filter.mp hb).2
    by_cases hbS : b ∈ S
    · simp only [θ,resampleBonds,extendConfiguration,dif_pos hbS]
      exact hbClosed.symm
    · simp only [θ,resampleBonds,extendConfiguration,dif_neg hbS]
  have hle := sprinklingUnexploredGraph_le_of_closed_agree R Q₃ F₃ ω θ hclosedagree
  obtain ⟨hpositiveω,hnonω⟩ := havoid
  change (sprinklingUnexploredCluster θ (D \ C) Q₃ F₃ v ∩ B).Nonempty ∧
    ¬ (sprinklingUnexploredCluster θ R Q₃ F₃ v ∩ V).Nonempty
  refine ⟨hpositive ▸ hpositiveω,?_⟩
  rintro ⟨x,hx⟩
  obtain ⟨hxCluster,hxV⟩ := Finset.mem_inter.mp hx
  obtain ⟨hxR,hvx⟩ := (mem_sprinklingUnexploredCluster θ R Q₃ F₃ v x).mp hxCluster
  apply hnonω
  exact ⟨x,Finset.mem_inter.mpr
    ⟨(mem_sprinklingUnexploredCluster ω R Q₃ F₃ v x).mpr ⟨hxR,hvx.mono hle⟩,hxV⟩⟩

end NearCritical
