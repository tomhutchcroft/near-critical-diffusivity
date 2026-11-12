module

public import NearCritical.Section9CoalescenceConnection

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- A cross intersection connects the other root and a target to the
first pivot head in the union of the two tube domains. -/
theorem section9_cross_three_terminals {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e)
    (hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f)
    (hcross : (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
      sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty) :
    let D := (L : Set (Vertex d)) ∪ (R : Set (Vertex d))
    ∃ z ∈ B, (restrictedGraph ω D).Reachable e.2 y ∧
      (restrictedGraph ω D).Reachable e.2 z := by
  intro D
  have hL : sprinklingUnexploredGraph ω L Q₁ F₁ ≤ restrictedGraph ω D := by
    intro a b hab
    exact ⟨hab.1, Or.inl hab.2.1, Or.inl hab.2.2.1⟩
  have hR : sprinklingUnexploredGraph ω R Q₃ F₃ ≤ restrictedGraph ω D := by
    intro a b hab
    exact ⟨hab.1, Or.inr hab.2.1, Or.inr hab.2.2.1⟩
  obtain ⟨v, hv⟩ := hcross
  obtain ⟨hvR, hvL⟩ := Finset.mem_inter.mp hv
  have hev := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 v).mp hvR).2
  have hfv := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ f.1 v).mp hvL).2
  obtain ⟨w, hw⟩ := hf.2.2.2.1
  obtain ⟨hwL, hwy⟩ := Finset.mem_inter.mp hw
  have hwEq := Finset.mem_singleton.mp hwy
  subst w
  have hfy := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ f.1 y).mp hwL).2
  obtain ⟨z, hz⟩ := he.2.2.2.2.1
  obtain ⟨hzR, hzB⟩ := Finset.mem_inter.mp hz
  have hez := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 z).mp hzR).2
  exact ⟨z, hzB, (hev.mono hR).trans ((hfv.symm.trans hfy).mono hL), hez.mono hR⟩

/-- In Case 2 the first left arm avoids both components used by
the cross connection. This is the separation required by BK. -/
theorem section9_cross_component_disjoint {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e)
    (hLL : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω L Q₁ F₁ f.1)) :
    Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∪
        sprinklingUnexploredCluster ω L Q₁ F₁ f.1) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  rcases Finset.mem_union.mp hv' with hR | hL
  · exact Finset.disjoint_left.mp he.2.2.2.2.2 hv hR
  · exact Finset.disjoint_left.mp hLL hv hL

/-- If the two root components do not meet, neither do the two
left pivot components. This supplies the separation in Cases 2 and 3. -/
theorem section9_left_pivot_components_disjoint {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e)
    (hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f)
    (hxy : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ x)
      (sprinklingUnexploredCluster ω L Q₁ F₁ y)) :
    Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) := by
  have root_eq (z : Vertex d) (a : Vertex d × Vertex d)
      (ha : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {z} B a) :
      sprinklingUnexploredCluster ω L Q₁ F₁ a.1 =
        sprinklingUnexploredCluster ω L Q₁ F₁ z := by
    obtain ⟨w, hw⟩ := ha.2.2.2.1
    obtain ⟨hwC, hwz⟩ := Finset.mem_inter.mp hw
    have hwEq := Finset.mem_singleton.mp hwz
    subst w
    have hz := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ a.1 z).mp hwC).1
    exact sprinklingUnexploredCluster_eq_of_inter_nonempty ω L Q₁ F₁ a.1 z
      ⟨z, Finset.mem_inter.mpr ⟨hwC, root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hz⟩⟩
  simpa only [root_eq x e he, root_eq y f hf] using hxy

/-- Two singleton connections in overlapping domains concatenate in
their union. The statement is evaluated in the same configuration. -/
theorem section9_cross_connection_concat {d : ℕ} {ω : Configuration d}
    (D T : Set (Vertex d)) (a b c : Vertex d)
    (hab : connectionToSetEvent D a {b} ω)
    (hbc : connectionToSetEvent T b {c} ω) :
    connectionToSetEvent (D ∪ T) a {c} ω := by
  obtain ⟨ha, b', hb', _, hp⟩ := hab
  obtain ⟨_, c', hc', hcT, hq⟩ := hbc
  have hbEq : b' = b := hb'
  have hcEq : c' = c := hc'
  subst b'
  subst c'
  refine ⟨Or.inl ha, c, rfl, Or.inr hcT, ?_⟩
  exact (hp.mono (restrictedGraph_mono ω Set.subset_union_left)).trans
    (hq.mono (restrictedGraph_mono ω Set.subset_union_right))

/-- A cross intersection yields a joint connection disjointly from the
first left arm. Both sides have finite witnesses in the original field. -/
theorem section9_cross_disjointOccurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e)
    (hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f)
    (hLL : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω L Q₁ F₁ f.1))
    (hcross : (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
      sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty) :
    let D := (R : Set (Vertex d)) ∪ (L : Set (Vertex d))
    DisjointOccurrence (connectionToSetEvent (L : Set (Vertex d)) e.1 {x})
      (connectionToSetEvent D e.2 {y} ∩ connectionToSetEvent D e.2 (B : Set (Vertex d))) ω := by
  intro D
  have leftReach (a : Vertex d × Vertex d) (w : Vertex d)
      (ha : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {w} B a) :
      (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable a.1 w := by
    obtain ⟨u, hu⟩ := ha.2.2.2.1
    obtain ⟨huC, huw⟩ := Finset.mem_inter.mp hu
    have hEq := Finset.mem_singleton.mp huw
    subst u
    exact ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ a.1 w).mp huC).2
  obtain ⟨v, hv⟩ := hcross
  obtain ⟨hvR, hvL⟩ := Finset.mem_inter.mp hv
  obtain ⟨z, hz⟩ := he.2.2.2.2.1
  obtain ⟨hzR, hzB⟩ := Finset.mem_inter.mp hz
  have hev := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 v).mp hvR).2
  have hez := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 z).mp hzR).2
  obtain ⟨hvIn, hfv⟩ := (mem_sprinklingUnexploredCluster ω L Q₁ F₁ f.1 v).mp hvL
  obtain ⟨S, hSo, hSb, hSf⟩ :=
    sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1 (leftReach e x he)
  obtain ⟨U, hUo, hUb, hUf⟩ :=
    sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1 hev
  obtain ⟨V, hVo, hVb, hVf⟩ :=
    sprinklingComponent_connection_certificate ω L Q₁ F₁ hvIn (hfv.symm.trans (leftReach f y hf))
  obtain ⟨W, hWo, hWb, hWf⟩ :=
    sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1 hez
  have hVC : sprinklingUnexploredCluster ω L Q₁ F₁ v =
      sprinklingUnexploredCluster ω L Q₁ F₁ f.1 :=
    sprinklingUnexploredCluster_eq_of_inter_nonempty ω L Q₁ F₁ v f.1
      ⟨v, Finset.mem_inter.mpr ⟨root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hvIn, hvL⟩⟩
  let T := (U ∪ V) ∪ W
  have hTb : ∀ b ∈ T, b.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∪
      sprinklingUnexploredCluster ω L Q₁ F₁ f.1 := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · rcases Finset.mem_union.mp hb with hb | hb
      · exact Finset.mem_union_left _ (hUb b hb)
      · exact Finset.mem_union_right _ (hVC ▸ hVb b hb)
    · exact Finset.mem_union_left _ (hWb b hb)
  have hdis := disjoint_bond_certificates_of_disjoint_bases
    (section9_cross_component_disjoint ω L R Q₁ F₁ Q₃ F₃ {x} B e f he hLL) hSb hTb
  refine ⟨S, T, S.finite_toSet, T.finite_toSet,
    Set.disjoint_left.mpr (Finset.disjoint_left.mp hdis), ?_, ?_⟩
  · intro θ hθ
    exact hSf θ (fun b hb => (hθ b hb).trans (hSo b hb))
  · intro θ hθ
    have hU (b) (hb : b ∈ U) : θ b = true :=
      (hθ b (Finset.mem_union_left W (Finset.mem_union_left V hb))).trans (hUo b hb)
    have hV (b) (hb : b ∈ V) : θ b = true :=
      (hθ b (Finset.mem_union_left W (Finset.mem_union_right U hb))).trans (hVo b hb)
    have hW (b) (hb : b ∈ W) : θ b = true :=
      (hθ b (Finset.mem_union_right (U ∪ V) hb)).trans (hWo b hb)
    refine ⟨section9_cross_connection_concat _ _ _ _ _ (hUf θ hU) (hVf θ hV), ?_⟩
    exact connectionToSetEvent_mono Set.subset_union_left (Set.singleton_subset_iff.mpr hzB)
      e.2 (hWf θ hW)

/-- BK bounds the fixed cross event by one left arm and one joint
connection in the union domain. -/
theorem section9_cross_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e : Vertex d × Vertex d) :
    let D := (R : Set (Vertex d)) ∪ (L : Set (Vertex d))
    (percolation d p).real {ω | ∃ f : Vertex d × Vertex d,
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
        sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty} ≤
      (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) e.1 {x}) *
        (percolation d p).real
          (connectionToSetEvent D e.2 {y} ∩ connectionToSetEvent D e.2 (B : Set (Vertex d))) := by
  intro D
  let A := connectionToSetEvent (L : Set (Vertex d)) e.1 {x}
  let C := connectionToSetEvent D e.2 {y} ∩ connectionToSetEvent D e.2 (B : Set (Vertex d))
  have hC : BK.Increasing C := by
    intro ω θ h hω
    exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
      connectionToSetEvent_increasing _ _ _ h hω.2⟩
  calc
    _ ≤ (percolation d p).real {ω | DisjointOccurrence A C ω} :=
      measureReal_mono (by
        rintro ω ⟨f, he, hf, hLL, hcross⟩
        exact section9_cross_disjointOccurrence ω L R Q₁ F₁ Q₃ F₃ B
          x y e f he hf hLL hcross)
    _ ≤ _ := percolation_bk d p A C (connectionToSetEvent_increasing _ _ _) hC

end NearCritical
