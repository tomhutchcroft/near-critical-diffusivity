module
public import NearCritical.Section9AvoidanceOccurrence
public import NearCritical.Section9MiddleGeometry
public import NearCritical.Section9PhysicalBond
public import NearCritical.HalfSpaceLastVisit

/-! The actual physical last-exit candidates embed in the literal oriented
cluster boundary with inner endpoint in source S2, not its smaller core. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Finite realization of the oriented boundary with inner endpoint in S2.
The outer endpoint is enumerated in a containing box, not restricted to S2. -/
def section9OrientedClusterBoundary {d : ℕ} (i : Fin d) (n : ℕ)
    (C : Finset (Vertex d)) : Finset (Vertex d × Vertex d) :=
  (orientedLatticePairs (centeredBox d (3*n))).filter fun e =>
    e.1 ∈ C ∧ e.1 ∈ section9FiniteMiddle i n ∧ e.2 ∉ C

private theorem middle_neighbor_mem_ambient {d : ℕ} (i : Fin d) (n : ℕ) (hn : 1 ≤ n)
    {u v : Vertex d} (hu : u ∈ section9FiniteMiddle i n)
    (huv : (openGraph (fun _ : Bond d => true)).Adj u v) :
    v ∈ centeredBox d (3*n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have huShape := (Finset.mem_filter.mp hu).2
  apply mem_centeredBox.mpr
  intro j
  have hstep := openGraph_adj_height_bounds huv j
  have huvR : (u j : ℝ) ≤ (v j : ℝ)+1 := by exact_mod_cast hstep.1
  have hvuR : (v j : ℝ) ≤ (u j : ℝ)+1 := by exact_mod_cast hstep.2
  have hvBounds : -3*(n : ℝ) ≤ (v j : ℝ) ∧ (v j : ℝ) ≤ 3*(n : ℝ) := by
    by_cases hji : j = i
    · subst j
      constructor <;> linarith [huShape.1,huShape.2.1]
    · obtain ⟨hl,hh⟩ := huShape.2.2 j hji
      constructor <;> linarith
  constructor
  · exact_mod_cast hvBounds.1
  · exact_mod_cast hvBounds.2

/-- The containing-box guards impose no extra restriction on a physical
boundary edge whose inner endpoint lies in the actual middle region. -/
theorem section9_mem_oriented_cluster_boundary {d : ℕ} (i : Fin d) (n : ℕ) (hn : 1 ≤ n)
    (C : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    e ∈ section9OrientedClusterBoundary i n C ↔
      e.1 ∈ C ∩ section9FiniteMiddle i n ∧ e.2 ∉ C ∧
        (openGraph (fun _ : Bond d => true)).Adj e.1 e.2 := by
  constructor
  · intro he
    obtain ⟨hpair,hC,hMiddle,hNot⟩ := Finset.mem_filter.mp he
    exact ⟨Finset.mem_inter.mpr ⟨hC,hMiddle⟩,hNot,
      ((mem_orientedLatticePairs (centeredBox d (3*n)) e.1 e.2).mp hpair).2.2⟩
  · rintro ⟨hinner,hNot,hadj⟩
    obtain ⟨hC,hMiddle⟩ := Finset.mem_inter.mp hinner
    have hboxInner : e.1 ∈ centeredBox d (3*n) := (Finset.mem_filter.mp hMiddle).1
    have hboxOuter := middle_neighbor_mem_ambient i n hn hMiddle hadj
    exact Finset.mem_filter.mpr
      ⟨(mem_orientedLatticePairs (centeredBox d (3*n)) e.1 e.2).mpr
        ⟨hboxInner,hboxOuter,hadj⟩,hC,hMiddle,hNot⟩

private theorem candidate_physical_endpoints {d : ℕ}
    (D C Q F : Finset (Vertex d)) (t : (Vertex d × Vertex d) × Bond d)
    (ht : t ∈ section9AvoidanceLastExitCandidates D C Q F) :
    s(t.2.1,bondTip t.2) = s(t.1.1,t.1.2) := by
  have hends := (Finset.mem_filter.mp ht).2.2.2
  rcases hends with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]
  · rw [hu,hv]
    exact Sym2.eq_swap

/-- Ordered endpoints determine the indexed physical bond, so projecting
the actual last-exit candidates introduces no multiplicity. -/
theorem section9_last_exit_candidate_projection_injOn {d : ℕ} (i : Fin d) (n : ℕ)
    (C F₃ : Finset (Vertex d)) :
    Set.InjOn (fun t : (Vertex d × Vertex d) × Bond d => t.1)
      ((section9AvoidanceLastExitCandidates (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) C
        (section9FiniteEndCube i n (2*(n : ℝ))) F₃ : Finset ((Vertex d × Vertex d) × Bond d)) :
          Set ((Vertex d × Vertex d) × Bond d)) := by
  intro t ht t' ht' hpair
  have htPhys := candidate_physical_endpoints _ _ _ _ t ht
  have hsPhys := candidate_physical_endpoints _ _ _ _ t' ht'
  have hsym : s(t.1.1,t.1.2) = s(t'.1.1,t'.1.2) :=
    congrArg (fun e : Vertex d × Vertex d => s(e.1,e.2)) hpair
  have hb : t.2 = t'.2 := section9_bond_endpoints_injective
    (htPhys.trans (hsym.trans hsPhys.symm))
  exact Prod.ext hpair hb

/-- Actual physical candidates have inner endpoint in C⊆T12 and in T23,
hence in S2=T12∩T23. Their endpoint projection lies in the literal oriented
boundary, without requiring their outer endpoint to lie in S2. -/
theorem section9_last_exit_candidate_projection_subset_boundary {d : ℕ}
    (i : Fin d) (n : ℕ) (C F₃ : Finset (Vertex d))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) :
    (section9AvoidanceLastExitCandidates (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) C
      (section9FiniteEndCube i n (2*(n : ℝ))) F₃).image
        (fun t : (Vertex d × Vertex d) × Bond d => t.1) ⊆ section9OrientedClusterBoundary i n C := by
  intro e he
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp he
  have hm := Finset.mem_filter.mp ht
  have hR := Finset.mem_product.mp (Finset.mem_product.mp hm.1).1
  have hC := hm.2.1
  have hMiddle : t.1.1 ∈ section9FiniteMiddle i n := by
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.mem_inter.mpr ⟨hCL hC,hR.1⟩
  have hboxInner : t.1.1 ∈ centeredBox d (3*n) := (Finset.mem_filter.mp hR.1).1
  have hboxOuter : t.1.2 ∈ centeredBox d (3*n) := (Finset.mem_filter.mp hR.2).1
  have hadj : (openGraph (fun _ : Bond d => true)).Adj t.1.1 t.1.2 :=
    ⟨t.2,rfl,hm.2.2.2⟩
  exact Finset.mem_filter.mpr
    ⟨(mem_orientedLatticePairs (centeredBox d (3*n)) t.1.1 t.1.2).mpr
      ⟨hboxInner,hboxOuter,hadj⟩,hC,hMiddle,hm.2.2.1⟩

end NearCritical
