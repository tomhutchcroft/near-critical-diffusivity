module
public import NearCritical.Section9OverlapMatching
public import NearCritical.Section9CoalescenceBK
public import NearCritical.Section9ConditionedMarkedTree

/-! Actual mixed-component witnesses for the original cross-overlap cases. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Four terminals in one component, with two terminal families retained. -/
def section9CrossJointEvent {d : ℕ} (D : Finset (Vertex d))
    (a b : Vertex d) (A B : Finset (Vertex d)) : Set (Configuration d) :=
  connectionToSetEvent (D : Set (Vertex d)) a {b} ∩
    (connectionToSetEvent (D : Set (Vertex d)) a (A : Set (Vertex d)) ∩
     connectionToSetEvent (D : Set (Vertex d)) a (B : Set (Vertex d)))

private theorem cross_joint_increasing {d : ℕ} (D : Finset (Vertex d))
    (a b : Vertex d) (A B : Finset (Vertex d)) : BK.Increasing (section9CrossJointEvent D a b A B) := by
  intro ω η h hω
  exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
    connectionToSetEvent_increasing _ _ _ h hω.2.1,
    connectionToSetEvent_increasing _ _ _ h hω.2.2⟩

private theorem cross_joint_certificate {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e)
    (hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f)
    (hcross : (sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∩
      sprinklingUnexploredCluster ω R Q₃ F₃ f.2).Nonempty) :
    ∃ Z : Finset (Bond d), (∀ b ∈ Z, ω b = true) ∧
      (∀ b ∈ Z, b.1 ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪
        sprinklingUnexploredCluster ω R Q₃ F₃ f.2) ∧
      ∀ θ : Configuration d, (∀ b ∈ Z, θ b = true) →
        θ ∈ section9CrossJointEvent (L ∪ R) e.1 f.2 A B := by
  obtain ⟨w,hw⟩ := hcross
  obtain ⟨hwL,hwR⟩ := Finset.mem_inter.mp hw
  obtain ⟨x,hx⟩ := he.2.2.2.1
  obtain ⟨hxL,hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨y,hy⟩ := hf.2.2.2.2.1
  obtain ⟨hyR,hyB⟩ := Finset.mem_inter.mp hy
  obtain ⟨S,hSo,hSb,hSf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 w).mp hwL).2
  obtain ⟨U,hUo,hUb,hUf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxL).2
  obtain ⟨V,hVo,hVb,hVf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ hf.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ f.2 w).mp hwR).2
  obtain ⟨W,hWo,hWb,hWf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ hf.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ f.2 y).mp hyR).2
  refine ⟨(S ∪ U) ∪ (V ∪ W),?_,?_,?_⟩
  · intro b hb
    rcases Finset.mem_union.mp hb with hL | hR
    · exact (Finset.mem_union.mp hL).elim (hSo b) (hUo b)
    · exact (Finset.mem_union.mp hR).elim (hVo b) (hWo b)
  · intro b hb
    rcases Finset.mem_union.mp hb with hL | hR
    · exact Finset.mem_union_left _ ((Finset.mem_union.mp hL).elim (hSb b) (hUb b))
    · exact Finset.mem_union_right _ ((Finset.mem_union.mp hR).elim (hVb b) (hWb b))
  · intro θ hθ
    have hS := hSf θ (fun b hb => hθ b (Finset.mem_union_left _ (Finset.mem_union_left _ hb)))
    have hU := hUf θ (fun b hb => hθ b (Finset.mem_union_left _ (Finset.mem_union_right _ hb)))
    have hV := hVf θ (fun b hb => hθ b (Finset.mem_union_right _ (Finset.mem_union_left _ hb)))
    have hW := hWf θ (fun b hb => hθ b (Finset.mem_union_right _ (Finset.mem_union_right _ hb)))
    obtain ⟨_,w₁,hw₁,_,hew⟩ := hS
    have hw₁eq : w₁ = w := hw₁
    subst w₁
    obtain ⟨_,w₂,hw₂,_,hfw⟩ := hV
    have hw₂eq : w₂ = w := hw₂
    subst w₂
    obtain ⟨_,y',hy',hy'R,hfy⟩ := hW
    have hy'eq : y' = y := hy'
    subst y'
    have hLD : (L : Set (Vertex d)) ⊆ (↑(L ∪ R) : Set (Vertex d)) := fun _ hz => Finset.mem_union_left _ hz
    have hRD : (R : Set (Vertex d)) ⊆ (↑(L ∪ R) : Set (Vertex d)) := fun _ hz => Finset.mem_union_right _ hz
    have hewD := hew.mono (restrictedGraph_mono θ hLD)
    have hfwD := hfw.mono (restrictedGraph_mono θ hRD)
    have hefD := hewD.trans hfwD.symm
    refine ⟨⟨hLD he.2.1,f.2,rfl,hRD hf.2.2.1,hefD⟩,?_,?_⟩
    · exact connectionToSetEvent_mono hLD (Set.singleton_subset_iff.mpr hxA) e.1 hU
    · exact ⟨hLD he.2.1,y,hyB,hRD hy'R,hefD.trans (hfy.mono (restrictedGraph_mono θ hRD))⟩

/-- A single cross overlap supplies a four-terminal joint witness disjoint
from each of the two other original component arms. -/
theorem section9_cross_singleton_occurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (h : ω ∈ section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f) :
    DisjointOccurrence (section9CrossJointEvent (L ∪ R) e.1 f.2 A B)
      {θ | DisjointOccurrence (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d)))
        (connectionToSetEvent (L : Set (Vertex d)) f.1 (A : Set (Vertex d))) θ} ω := by
  obtain ⟨he,hf,hLL,hLR,hRL,hRR⟩ := h
  obtain ⟨Z,hZo,hZb,hZf⟩ := cross_joint_certificate ω L R Q₁ F₁ Q₃ F₃ A B e f he hf hLR
  obtain ⟨y,hy⟩ := he.2.2.2.2.1
  obtain ⟨hyR,hyB⟩ := Finset.mem_inter.mp hy
  obtain ⟨x,hx⟩ := hf.2.2.2.1
  obtain ⟨hxL,hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨V,hVo,hVb,hVf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mp hyR).2
  obtain ⟨W,hWo,hWb,hWf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ hf.2.1
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ f.1 x).mp hxL).2
  have hGVR := Finset.disjoint_union_left.mpr ⟨he.2.2.2.2.2,hRR.symm⟩
  have hGWL := Finset.disjoint_union_left.mpr ⟨hLL,hf.2.2.2.2.2.symm⟩
  have hZV := disjoint_bond_certificates_of_disjoint_bases hGVR hZb hVb
  have hZW := disjoint_bond_certificates_of_disjoint_bases hGWL hZb hWb
  have hVW := disjoint_bond_certificates_of_disjoint_bases hRL hVb hWb
  refine ⟨(↑Z : Set (Bond d)),(↑V : Set (Bond d)) ∪ (↑W : Set (Bond d)),
    Z.finite_toSet,V.finite_toSet.union W.finite_toSet,?_,?_,?_⟩
  · exact Set.disjoint_left.mpr fun b hb hbr => hbr.elim (Finset.disjoint_left.mp hZV hb) (Finset.disjoint_left.mp hZW hb)
  · intro θ hθ
    exact hZf θ (fun b hb => (hθ b hb).trans (hZo b hb))
  · apply Section8.forcesOn_disjointOccurrence_union V.finite_toSet W.finite_toSet
    · exact Set.disjoint_left.mpr (Finset.disjoint_left.mp hVW)
    · intro θ hθ
      exact connectionToSetEvent_mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr hyB) e.2
        (hVf θ (fun b hb => (hθ b hb).trans (hVo b hb)))
    · intro θ hθ
      exact connectionToSetEvent_mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr hxA) f.1
        (hWf θ (fun b hb => (hθ b hb).trans (hWo b hb)))

/-- In the double-cross case the two mixed component unions give disjoint
four-terminal joint witnesses. -/
theorem section9_double_cross_occurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (h : ω ∈ section9OverlapPatternEvent .cross L R Q₁ F₁ Q₃ F₃ A B e f) :
    DisjointOccurrence (section9CrossJointEvent (L ∪ R) e.1 f.2 A B)
      (section9CrossJointEvent (L ∪ R) f.1 e.2 A B) ω := by
  obtain ⟨he,hf,hLL,hLR,hRL,hRR⟩ := h
  obtain ⟨Z,hZo,hZb,hZf⟩ := cross_joint_certificate ω L R Q₁ F₁ Q₃ F₃ A B e f he hf hLR
  obtain ⟨W,hWo,hWb,hWf⟩ := cross_joint_certificate ω L R Q₁ F₁ Q₃ F₃ A B f e hf he
    (by simpa only [Finset.inter_comm] using hRL)
  have hGL := Finset.disjoint_union_left.mpr ⟨hLL,hf.2.2.2.2.2.symm⟩
  have hGR := Finset.disjoint_union_left.mpr ⟨he.2.2.2.2.2,hRR.symm⟩
  have hGG := Finset.disjoint_union_right.mpr ⟨hGL,hGR⟩
  have hZW := disjoint_bond_certificates_of_disjoint_bases hGG hZb hWb
  refine ⟨Z,W,Z.finite_toSet,W.finite_toSet,Set.disjoint_left.mpr (Finset.disjoint_left.mp hZW),?_,?_⟩
  · intro θ hθ
    exact hZf θ (fun b hb => (hθ b hb).trans (hZo b hb))
  · intro θ hθ
    exact hWf θ (fun b hb => (hθ b hb).trans (hWo b hb))

/-- Actual BK separates the mixed four-terminal group from the two other
component arms in the cross-singleton case. -/
theorem section9_cross_singleton_joint_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    (percolation d p).real (section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      (percolation d p).real (section9CrossJointEvent (L ∪ R) e.1 f.2 A B) *
        ((percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) *
         (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) f.1 (A : Set (Vertex d)))) := by
  let J := section9CrossJointEvent (L ∪ R) e.1 f.2 A B
  let V := connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))
  let W := connectionToSetEvent (L : Set (Vertex d)) f.1 (A : Set (Vertex d))
  let K := {ω : Configuration d | DisjointOccurrence V W ω}
  have hV : BK.Increasing V := connectionToSetEvent_increasing _ _ _
  have hW : BK.Increasing W := connectionToSetEvent_increasing _ _ _
  have hK : BK.Increasing K := by
    intro ω η h hω
    obtain ⟨F,G,hFfin,hGfin,hdis,hF,hG,hVF,hWG⟩ := BK.openDisjointOccurrence_of_disjointOccurrence hω
    exact BK.OpenDisjointOccurrence.to_disjointOccurrence
      ⟨F,G,hFfin,hGfin,hdis,(fun b hb => h b (hF b hb)),(fun b hb => h b (hG b hb)),hVF,hWG⟩ hV hW
  refine (measureReal_mono (fun ω h => section9_cross_singleton_occurrence ω L R Q₁ F₁ Q₃ F₃ A B e f h)
    (measure_ne_top _ _)).trans ?_
  exact (percolation_bk d p J K (cross_joint_increasing _ _ _ _ _) hK).trans
    (mul_le_mul_of_nonneg_left (percolation_bk d p V W hV hW) measureReal_nonneg)

/-- Both mixed four-terminal groups are separated by actual BK in the
double-cross case. No four-point probability estimate is assumed here. -/
theorem section9_double_cross_joint_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    (percolation d p).real (section9OverlapPatternEvent .cross L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      (percolation d p).real (section9CrossJointEvent (L ∪ R) e.1 f.2 A B) *
        (percolation d p).real (section9CrossJointEvent (L ∪ R) f.1 e.2 A B) := by
  refine (measureReal_mono (fun ω h => section9_double_cross_occurrence ω L R Q₁ F₁ Q₃ F₃ A B e f h)
    (measure_ne_top _ _)).trans ?_
  exact percolation_bk d p _ _ (cross_joint_increasing _ _ _ _ _) (cross_joint_increasing _ _ _ _ _)

private theorem cross_pattern_local {d : ℕ} (k : Section9OverlapPattern)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (ω η : Configuration d)
    (h : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = η b) :
    (ω ∈ section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f ↔
      η ∈ section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f) := by
  have hL (v : Vertex d) := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω η
    (fun b hb => h b (Finset.mem_union_left _ hb)) v
  have hR (v : Vertex d) := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω η
    (fun b hb => h b (Finset.mem_union_right _ hb)) v
  have hp (a : Vertex d × Vertex d) := sprinklingPivotalPair_iff_of_available_agree
    L R Q₁ F₁ Q₃ F₃ A B ω η
    (fun b hb => h b (Finset.mem_union_left _ hb))
    (fun b hb => h b (Finset.mem_union_right _ hb)) a
  cases k <;> simp only [section9OverlapPatternEvent,section9OverlapPatternHolds,Set.mem_setOf_eq,hp,hL,hR]

private theorem cross_pattern_fresh_probability {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (k : Section9OverlapPattern) (e f : Vertex d × Vertex d) :
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real (section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f) =
      (percolation d p).real (section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f) :=
  section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
    (sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃)
    (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁)
    _ (measurableSet_section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f)
    (cross_pattern_local k L R Q₁ F₁ Q₃ F₃ A B e f)

/-- Actual conditioning transfer for the cross-singleton reduction. -/
theorem section9_conditioned_cross_singleton_joint_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) (e f : Vertex d × Vertex d) :
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real
      (section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      (percolation d p).real (section9CrossJointEvent (L ∪ R) e.1 f.2 A B) *
        ((percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) *
         (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) f.1 (A : Set (Vertex d)))) := by
  rw [cross_pattern_fresh_probability p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁]
  exact section9_cross_singleton_joint_probability_le p L R Q₁ F₁ Q₃ F₃ A B e f

/-- Actual conditioning transfer for the double-cross reduction. -/
theorem section9_conditioned_double_cross_joint_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) (e f : Vertex d × Vertex d) :
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real
      (section9OverlapPatternEvent .cross L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      (percolation d p).real (section9CrossJointEvent (L ∪ R) e.1 f.2 A B) *
        (percolation d p).real (section9CrossJointEvent (L ∪ R) f.1 e.2 A B) := by
  rw [cross_pattern_fresh_probability p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁]
  exact section9_double_cross_joint_probability_le p L R Q₁ F₁ Q₃ F₃ A B e f

end NearCritical
