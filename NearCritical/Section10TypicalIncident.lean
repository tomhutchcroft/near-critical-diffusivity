module

public import NearCritical.Section10TypicalClusters
public import NearCritical.Section10IncidentMetric

/-! Actual typical-family locality on the smaller incident-heart bond mask.
The cylinder retains the union-value conjunct. It does not claim that a
typical-family observable is a function of the vertex union alone. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem isTypicalCluster_iff_of_component_reveal_agree {d : ℕ}
    (a : TypicalParameters) (t : ℕ) (z : Vertex d) (F C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ typicalCube t z) (ω η : Configuration d)
    (hF : heartClusterUnion ω (typicalCube t z) (typicalHeart t z a.heartRatio) = F)
    (hC : finiteBoxCluster ω (typicalCube t z) root = C) (hCF : C ⊆ F)
    (hagree : ∀ e ∈ clusterRevealBonds (typicalCube t z) F, ω e = η e) :
    IsTypicalCluster a t z ω C ↔ IsTypicalCluster a t z η C := by
  have hH : typicalHeart t z a.heartRatio ⊆ typicalCube t z := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hFη := heartClusterUnion_eq_of_reveal_agree (typicalCube t z)
    (typicalHeart t z a.heartRatio) F hH hF hagree
  have hrin := spanningFaceDiameter_eq_of_union_reveal_agree (typicalCube t z) C F
    (typicalFace t z) root hroot ω η hC hCF hagree
  simp only [IsTypicalCluster, typicalRegularPatch, hF, hFη, hrin]

private theorem typicalClusterFamily_subset_of_union_reveal_agree {d : ℕ}
    (a : TypicalParameters) (t : ℕ) (z : Vertex d) (F : Finset (Vertex d))
    (ω η : Configuration d)
    (hF : heartClusterUnion ω (typicalCube t z) (typicalHeart t z a.heartRatio) = F)
    (hagree : ∀ e ∈ clusterRevealBonds (typicalCube t z) F, ω e = η e) :
    typicalClusterFamily a t z ω ⊆ typicalClusterFamily a t z η := by
  intro C hCmem
  obtain ⟨hactual, htyp⟩ := (mem_typicalClusterFamily a t z ω C).mp hCmem
  obtain ⟨root, hroot, hC⟩ := (mem_finiteClusterFamily ω (typicalCube t z) C).mp hactual
  have hCF : C ⊆ F := by
    rw [← hF]
    exact htyp.1
  have hCη : finiteBoxCluster η (typicalCube t z) root = C := by
    apply finiteBoxCluster_eq_of_reveal_agree (typicalCube t z) C root hroot hC
    intro e he
    exact hagree e (clusterRevealBonds_mono_vertices (typicalCube t z) C F hCF he)
  apply (mem_typicalClusterFamily a t z η C).mpr
  refine ⟨(mem_finiteClusterFamily η (typicalCube t z) C).mpr ⟨root, hroot, hCη⟩, ?_⟩
  exact (isTypicalCluster_iff_of_component_reveal_agree a t z F C root hroot
    ω η hF hC hCF hagree).mp htyp

/-- Actual component membership supplies the component for each candidate;
components outside F may change and are not compared. -/
theorem typicalClusterFamily_eq_of_union_reveal_agree {d : ℕ}
    (a : TypicalParameters) (t : ℕ) (z : Vertex d) (F : Finset (Vertex d))
    (ω η : Configuration d)
    (hF : heartClusterUnion ω (typicalCube t z) (typicalHeart t z a.heartRatio) = F)
    (hagree : ∀ e ∈ clusterRevealBonds (typicalCube t z) F, ω e = η e) :
    typicalClusterFamily a t z ω = typicalClusterFamily a t z η := by
  have hH : typicalHeart t z a.heartRatio ⊆ typicalCube t z := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hFη := heartClusterUnion_eq_of_reveal_agree (typicalCube t z)
    (typicalHeart t z a.heartRatio) F hH hF hagree
  exact Finset.Subset.antisymm
    (typicalClusterFamily_subset_of_union_reveal_agree a t z F ω η hF hagree)
    (typicalClusterFamily_subset_of_union_reveal_agree a t z F η ω hFη
      (fun e he => (hagree e he).symm))

theorem isPreGoodCube_iff_of_union_reveal_agree {d : ℕ}
    (a : TypicalParameters) (t : ℕ) (z : Vertex d) (F : Finset (Vertex d))
    (ω η : Configuration d)
    (hF : heartClusterUnion ω (typicalCube t z) (typicalHeart t z a.heartRatio) = F)
    (hagree : ∀ e ∈ clusterRevealBonds (typicalCube t z) F, ω e = η e) :
    IsPreGoodCube a t z ω ↔ IsPreGoodCube a t z η := by
  simp only [IsPreGoodCube, typicalClusterFamily_eq_of_union_reveal_agree a t z F ω η hF hagree]

/-- A fixed union AND typical-family atom is a genuine cylinder of the
incident mask associated to that union. Off the union atom both sides fail.
No realizability/positive-mass assumption is needed for this event identity. -/
theorem typicalFamily_union_event_cylinder {d : ℕ}
    (a : TypicalParameters) (t : ℕ) (z : Vertex d)
    (F : Finset (Vertex d)) (K : Finset (Finset (Vertex d))) :
    {ω : Configuration d |
      heartClusterUnion ω (typicalCube t z) (typicalHeart t z a.heartRatio) = F ∧
      typicalClusterFamily a t z ω = K} =
    (clusterRevealBonds (typicalCube t z) F).restrict ⁻¹'
      {ξ | heartClusterUnion (extendConfiguration (clusterRevealBonds (typicalCube t z) F)
            (fun _ => false) ξ) (typicalCube t z) (typicalHeart t z a.heartRatio) = F ∧
        typicalClusterFamily a t z (extendConfiguration (clusterRevealBonds (typicalCube t z) F)
            (fun _ => false) ξ) = K} := by
  ext ω
  let η := extendConfiguration (clusterRevealBonds (typicalCube t z) F) (fun _ => false)
    ((clusterRevealBonds (typicalCube t z) F).restrict ω)
  have hagree : ∀ e ∈ clusterRevealBonds (typicalCube t z) F, ω e = η e := by
    intro e he
    simp [η, extendConfiguration, he, Finset.restrict]
  have hH : typicalHeart t z a.heartRatio ⊆ typicalCube t z := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hUnion := heartClusterUnion_eq_iff_reveal_agree (typicalCube t z)
    (typicalHeart t z a.heartRatio) F hH ω η hagree
  change (heartClusterUnion ω (typicalCube t z) (typicalHeart t z a.heartRatio) = F ∧
    typicalClusterFamily a t z ω = K) ↔
    (heartClusterUnion η (typicalCube t z) (typicalHeart t z a.heartRatio) = F ∧
    typicalClusterFamily a t z η = K)
  constructor
  · rintro ⟨hF, hK⟩
    have hFam := typicalClusterFamily_eq_of_union_reveal_agree a t z F ω η hF hagree
    exact ⟨hUnion.mp hF, hFam.symm.trans hK⟩
  · rintro ⟨hFη, hKη⟩
    have hF := hUnion.mpr hFη
    have hFam := typicalClusterFamily_eq_of_union_reveal_agree a t z F ω η hF hagree
    exact ⟨hF, hFam.trans hKη⟩

end NearCritical.Section10
