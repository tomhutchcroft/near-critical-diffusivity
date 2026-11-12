module
public import NearCritical.Section9CoalescenceBK
public import NearCritical.Section9RestrictedTripodProbability
public import NearCritical.Section9ConditionedMarkedTree

/-! Source Case I: only the original left components coincide. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The original same-left singleton case, with both pivotal events literal. -/
def section9SameLeftOnlyEvent {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    Set (Configuration d) :=
  {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
    sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f ∧
    (sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∩
      sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty ∧
    Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
      (sprinklingUnexploredCluster ω R Q₃ F₃ f.2)}

/-- Disjoint finite certificates group the common left component and the
two separate right components, retaining the full target families. -/
theorem section9_same_left_only_occurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (h : ω ∈ section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f) :
    DisjointOccurrence
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {f.1} ∩
       connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
      {θ | DisjointOccurrence
        (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d)))
        (connectionToSetEvent (R : Set (Vertex d)) f.2 (B : Set (Vertex d))) θ} ω := by
  obtain ⟨he,hf,hLL,hRR⟩ := h
  have heq := sprinklingUnexploredCluster_eq_of_inter_nonempty ω L Q₁ F₁ e.1 f.1 hLL
  have hroot := root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hf.2.1
  rw [← heq] at hroot
  have hef := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 f.1).mp hroot).2
  obtain ⟨x,hx⟩ := he.2.2.2.1
  obtain ⟨hxC,hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨y,hy⟩ := he.2.2.2.2.1
  obtain ⟨hyC,hyB⟩ := Finset.mem_inter.mp hy
  obtain ⟨z,hz⟩ := hf.2.2.2.2.1
  obtain ⟨hzC,hzB⟩ := Finset.mem_inter.mp hz
  obtain ⟨S,hSo,hSb,hSf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1 hef
  obtain ⟨U,hUo,hUb,hUf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxC).2
  obtain ⟨V,hVo,hVb,hVf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mp hyC).2
  obtain ⟨W,hWo,hWb,hWf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ hf.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ f.2 z).mp hzC).2
  have hLeft : ∀ b ∈ S ∪ U, b.1 ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 := by
    intro b hb
    exact (Finset.mem_union.mp hb).elim (hSb b) (hUb b)
  have hLF : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) := by rw [heq]; exact hf.2.2.2.2.2
  have hLV := disjoint_bond_certificates_of_disjoint_bases he.2.2.2.2.2 hLeft hVb
  have hLW := disjoint_bond_certificates_of_disjoint_bases hLF hLeft hWb
  have hVW := disjoint_bond_certificates_of_disjoint_bases hRR hVb hWb
  refine ⟨(↑(S ∪ U) : Set (Bond d)),(↑V : Set (Bond d)) ∪ (↑W : Set (Bond d)),
    (S ∪ U).finite_toSet,V.finite_toSet.union W.finite_toSet,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro b hb hbr
    exact hbr.elim (Finset.disjoint_left.mp hLV hb) (Finset.disjoint_left.mp hLW hb)
  · intro θ hθ
    refine ⟨hSf θ (fun b hb => (hθ b (Finset.mem_union_left U hb)).trans (hSo b hb)),?_⟩
    apply connectionToSetEvent_mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr hxA) e.1
    exact hUf θ (fun b hb => (hθ b (Finset.mem_union_right S hb)).trans (hUo b hb))
  · apply Section8.forcesOn_disjointOccurrence_union V.finite_toSet W.finite_toSet
    · exact Set.disjoint_left.mpr (Finset.disjoint_left.mp hVW)
    · intro θ hθ
      apply connectionToSetEvent_mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr hyB) e.2
      exact hVf θ (fun b hb => (hθ b hb).trans (hVo b hb))
    · intro θ hθ
      apply connectionToSetEvent_mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr hzB) f.2
      exact hWf θ (fun b hb => (hθ b hb).trans (hWo b hb))

/-- The source singleton overlap probability has a finite tripod bound
and two ordinary right-arm factors, all derived by actual BK. -/
theorem section9_same_left_only_tree_bound {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    let P := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    (percolation d p).real (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u f.1 * P x u)) *
        ((percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) *
         (percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) f.2 (B : Set (Vertex d)))) := by
  intro P
  let J := connectionToSetEvent (L : Set (Vertex d)) e.1 {f.1} ∩
    connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))
  let V := connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))
  let W := connectionToSetEvent (R : Set (Vertex d)) f.2 (B : Set (Vertex d))
  let K := {ω : Configuration d | DisjointOccurrence V W ω}
  have hJ : BK.Increasing J := by
    intro ω η h hω
    exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
      connectionToSetEvent_increasing _ _ _ h hω.2⟩
  have hV : BK.Increasing V := connectionToSetEvent_increasing _ _ _
  have hW : BK.Increasing W := connectionToSetEvent_increasing _ _ _
  have hK : BK.Increasing K := by
    intro ω η h hω
    obtain ⟨F,G,hFfin,hGfin,hdis,hF,hG,hVF,hWG⟩ := BK.openDisjointOccurrence_of_disjointOccurrence hω
    exact BK.OpenDisjointOccurrence.to_disjointOccurrence
      ⟨F,G,hFfin,hGfin,hdis,(fun b hb => h b (hF b hb)),(fun b hb => h b (hG b hb)),hVF,hWG⟩ hV hW
  refine (measureReal_mono (fun ω h => section9_same_left_only_occurrence ω L R Q₁ F₁ Q₃ F₃ A B e f h)
    (measure_ne_top _ _)).trans ?_
  exact (percolation_bk d p J K hJ hK).trans
    (mul_le_mul (restricted_joint_connection_probability_le p L A e.1 f.1)
      (percolation_bk d p V W hV hW) measureReal_nonneg
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg measureReal_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)))

private theorem same_left_event_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (ω η : Configuration d)
    (h : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = η b) :
    (ω ∈ section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f ↔
      η ∈ section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f) := by
  have hL (v : Vertex d) := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω η
    (fun b hb => h b (Finset.mem_union_left _ hb)) v
  have hR (v : Vertex d) := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω η
    (fun b hb => h b (Finset.mem_union_right _ hb)) v
  have hp (a : Vertex d × Vertex d) := sprinklingPivotalPair_iff_of_available_agree
    L R Q₁ F₁ Q₃ F₃ A B ω η
    (fun b hb => h b (Finset.mem_union_left _ hb))
    (fun b hb => h b (Finset.mem_union_right _ hb)) a
  simp only [section9SameLeftOnlyEvent,Set.mem_setOf_eq,hp,hL,hR]

theorem measurableSet_section9SameLeftOnlyEvent {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    MeasurableSet (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f) := by
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let E := section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f
  let S : Set (U → Bool) := {ξ | extendConfiguration U (fun _ => false) ξ ∈ E}
  have he : E = (U.restrict : Configuration d → (U → Bool)) ⁻¹' S := by
    ext ω
    exact same_left_event_local L R Q₁ F₁ Q₃ F₃ A B e f ω _
      (by intro b hb; simp [U,extendConfiguration,hb,Finset.restrict])
  change MeasurableSet E
  rw [he]
  exact (Set.toFinite S).measurableSet.preimage (Finset.measurable_restrict U)

/-- The actual positive heart-conditioned singleton-overlap probability
obeys the same finite tree bound on fresh available coordinates. -/
theorem section9_conditioned_same_left_only_tree_bound {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) (e f : Vertex d × Vertex d) :
    let P := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real
      (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u f.1 * P x u)) *
        ((percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) *
         (percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) f.2 (B : Set (Vertex d)))) := by
  intro P
  rw [section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
    (sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃)
    (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁)
    _ (measurableSet_section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f)
    (same_left_event_local L R Q₁ F₁ Q₃ F₃ A B e f)]
  exact section9_same_left_only_tree_bound p L R Q₁ F₁ Q₃ F₃ A B e f

end NearCritical
