module

public import NearCritical.Section10TypicalClusters
public import NearCritical.SelectedNestChain

/-! Instantiate the deterministic trace with the actual critical components
chosen by a nest. Their source typicality provides the intrinsic metric. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

/-- The strict cuts used by the actual typical cube give the same odd
integer box as the coarse crossing geometry, for either parity of `t`. -/
theorem typicalCube_eq_translated_centeredBox {d t : ℕ} (ht : 0 < t) (z : Vertex d) :
    typicalCube t z = translateSites z (centeredBox d ((t - 1) / 2)) := by
  classical
  let r := (t - 1) / 2
  have hlo : 2 * r < t := by dsimp [r]; omega
  have hhi : t ≤ 2 * r + 2 := by dsimp [r]; omega
  have hrt : r ≤ t := by omega
  ext x
  change x ∈ (translateSites z (centeredBox d t)).filter _ ↔
    x ∈ translateSites z (centeredBox d r)
  constructor
  · intro hx
    obtain ⟨_, hcut⟩ := Finset.mem_filter.mp hx
    have heq : z + (x - z) = x := by abel
    refine Finset.mem_image.mpr ⟨x - z, mem_centeredBox.mpr ?_, heq⟩
    intro j
    have hj := hcut j
    rw [← Int.cast_abs] at hj
    have hcutj : 2 * |x j - z j| < (t : ℤ) := by exact_mod_cast hj
    have hneg := neg_le_abs (x j - z j)
    have hpos := le_abs_self (x j - z j)
    change -(r : ℤ) ≤ x j - z j ∧ x j - z j ≤ (r : ℤ)
    omega
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have hv' := mem_centeredBox.mp hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, mem_centeredBox.mpr ?_, rfl⟩, ?_⟩
    · intro j
      have h := hv' j
      omega
    · intro j
      have habs : |v j| ≤ (r : ℤ) := abs_le.mpr (hv' j)
      have hcutj : 2 * |v j| < (t : ℤ) := by omega
      have he : (z + v) j - z j = v j := by
        change z j + v j - z j = v j
        omega
      rw [he]
      rw [← Int.cast_abs]
      exact_mod_cast hcutj

/-- Source typicality supplies short internal connections between any two face
vertices of the actual component, including vertices on the same face. -/
theorem typicalCluster_boundary_connection {d : ℕ} [Nontrivial (Fin d × Bool)]
    (a : TypicalParameters) (t : ℕ) (z : Vertex d) (critical : Configuration d)
    {C : Finset (Vertex d)} (hC : C ∈ typicalClusterFamily a t z critical)
    {x y : Vertex d} (hx : x ∈ clusterFaceBoundary C (typicalFace t z))
    (hy : y ∈ clusterFaceBoundary C (typicalFace t z)) :
    BoundedIntrinsicConnection (restrictedGraph critical (C : Set (Vertex d))) x y
      (2 * (a.diameterUpper * (2 * (t : ℝ)) ^ 2)) := by
  obtain ⟨hactual, htyp⟩ := (mem_typicalClusterFamily a t z critical C).mp hC
  obtain ⟨root, _, hroot⟩ := (mem_finiteClusterFamily critical (typicalCube t z) C).mp hactual
  subst C
  exact finiteCluster_faceInterface_connection critical (typicalCube t z) root
    (typicalFace t z) htyp.2.1 htyp.2.2.2.2.1 hx hy

/-- Build the trace from the chosen component labels and the local successful
tube steps. The component sites, face interfaces and metric are determined by
the critical configuration and typical membership. -/
def selectedTrace_of_typicalClusters {d n : ℕ} [Nontrivial (Fin d × Bool)]
    {ω critical : Configuration d} {D : Set (Vertex d)} {B : ℝ}
    (a : TypicalParameters) (t : ℕ) (z : ℕ → Vertex d)
    (hcritical : ∀ e, critical e = true → ω e = true)
    (nest : ℕ → Finset (Finset (Vertex d))) (rep : ℕ → Finset (Vertex d))
    (hrep : ∀ j, j ≤ n → rep j ∈ nest j)
    (htypical : ∀ j, j ≤ n → rep j ∈ typicalClusterFamily a t (z j) critical)
    (hcube : ∀ j, j ≤ n → (typicalCube t (z j) : Set (Vertex d)) ⊆ D)
    (step : ∀ j, j < n → NestSprinklingStep d (Finset (Vertex d)) ω D B)
    (hcriticalSides : ∀ j (hj : j < n),
      (step j hj).leftGraph ≤ openGraph critical ∧ (step j hj).rightGraph ≤ openGraph critical)
    (hsource : ∀ j (hj : j < n), (step j hj).sourceBoundary ⊆
      clusterFaceBoundary (rep j) (typicalFace t (z j)))
    (htarget : ∀ j (hj : j < n) C, (step j hj).targetBoundary C ⊆
      clusterFaceBoundary C (typicalFace t (z (j + 1))))
    (hoffspring : ∀ j (hj : j < n), nest (j + 1) ⊆ (step j hj).offspring) :
    SelectedNestTrace d (Finset (Vertex d)) ω D
      (2 * (a.diameterUpper * (2 * (t : ℝ)) ^ 2)) B n where
  critical := critical
  critical_le := hcritical
  nest := nest
  representative := rep
  representative_mem := hrep
  sites := fun _ C => (C : Set (Vertex d))
  interfaceSites := fun j C => (clusterFaceBoundary C (typicalFace t (z j)) : Set (Vertex d))
  interface_subset := fun j _ => clusterFaceBoundary_subset (rep j) (typicalFace t (z j))
  sites_subset := by
    intro j hj x hx
    have hactual := (mem_typicalClusterFamily a t (z j) critical (rep j)).mp (htypical j hj)
    exact hcube j hj (finiteClusterFamily_component_subset critical (typicalCube t (z j))
      hactual.1 hx)
  typical_diameter := by
    intro j hj x hx y hy
    exact typicalCluster_boundary_connection a t (z j) critical (htypical j hj) hx hy
  step := step
  critical_sides := hcriticalSides
  source_in_representative := fun j hj _ hx => hsource j hj hx
  target_in_cluster := fun j hj C _ hy => htarget j hj C hy
  next_nest_offspring := hoffspring

end NearCritical.Section10
