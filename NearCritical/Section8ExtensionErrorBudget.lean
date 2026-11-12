module
public import NearCritical.Section8ExtensionEREOne
public import NearCritical.Section8ExtensionTripodError
public import NearCritical.Section8ExtensionErrorGeometry
public import NearCritical.Section9FreshEvent
public import NearCritical.Section9AvoidanceCertificate

/-! Actual source shifted-avoidance budget in the two literal regularity energies. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem extension_connection_avoidance_split {d : ℕ} (p : unitInterval)
    (T Q F W : Finset (Vertex d)) (a z : Vertex d) (ha : a ∈ T) :
    (percolation d p).real {ω | z ∈ sprinklingUnexploredCluster ω T Q F a} ≤
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} W a) +
      ∑ y ∈ W, (percolation d p).real
        (connectionToSetEvent (T : Set (Vertex d)) a {y} ∩
         connectionToSetEvent (T : Set (Vertex d)) a {z}) := by
  let J := fun y => connectionToSetEvent (T : Set (Vertex d)) a {y} ∩
    connectionToSetEvent (T : Set (Vertex d)) a {z}
  have hsub : {ω | z ∈ sprinklingUnexploredCluster ω T Q F a} ⊆
      section9AvoidanceEvent T T Q F {z} W a ∪ ⋃ y ∈ W, J y := by
    intro ω hz
    by_cases hh : (sprinklingUnexploredCluster ω T Q F a ∩ W).Nonempty
    · obtain ⟨y,hy⟩ := hh
      obtain ⟨hyC,hyW⟩ := Finset.mem_inter.mp hy
      obtain ⟨hyT,hay⟩ := (mem_sprinklingUnexploredCluster ω T Q F a y).mp hyC
      obtain ⟨hzT,haz⟩ := (mem_sprinklingUnexploredCluster ω T Q F a z).mp hz
      have hle : sprinklingUnexploredGraph ω T Q F ≤ restrictedGraph ω (T : Set (Vertex d)) :=
        fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr
        ⟨hyW,⟨ha,y,rfl,hyT,hay.mono hle⟩,⟨ha,z,rfl,hzT,haz.mono hle⟩⟩⟩)
    · exact Or.inl ⟨⟨z,Finset.mem_inter.mpr ⟨hz,Finset.mem_singleton_self z⟩⟩,hh⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add le_rfl (measureReal_biUnion_finset_le W J)))

/-- The actual shifted avoidance probability loses at most the literal ERE1
and ERE2 errors from the ordinary restricted connection. No lower bound for
that ordinary connection is assumed. All constants are explicit. -/
theorem section8_extension_source_energy_budget {d : ℕ} (hd : 5 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (i : Fin d) (n r : ℕ) (hr : 1 ≤ r) (hn : 16*(r+1) ≤ n)
    (F boundary : Finset (Vertex d)) (hF : F ⊆ section9FiniteEndCube i n 0)
    {x z : Vertex d} (hx : x ∈ section8ExtensionPositiveFaceCore i n)
    (hz : z ∈ section8ExtensionMiddleCore i n) :
    let T := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let Q := section9FiniteEndCube i n 0
    let a := Function.update x i (x i+(r : ℤ))
    let Cb := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
    let K₁ := G^2*(4 : ℝ)^((d : ℝ)-2)
    let K₂ := G^3*Cb*(16 : ℝ)^((d : ℝ)-2)*(1+(8 : ℝ)^((d : ℝ)-4))
    (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) a {z}) ≤
      (percolation d (criticalPoint d)).real (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) +
      (n : ℝ)^((2 : ℝ)-(d : ℝ)) *
        (K₁*regularityEnergyOne F (section8ExtensionSmallCube i n) r x +
         K₂*regularityEnergyTwo F boundary r x) := by
  intro T Q a Cb K₁ K₂
  let S := section8ExtensionSmallCube i n
  let q : ℝ := 2-(d : ℝ)
  let w := fun y : Vertex d => (max (r : ℝ) (latticeDistance x y))^((4 : ℤ)-(d : ℤ))
  obtain ⟨hwall,hIT,_⟩ := section8_extension_source_geometry i n r hn hx hz
  obtain ⟨haz,hYZ⟩ := section8_extension_error_source_distances i n r hn hx hz
  have hnR : 1 ≤ (n : ℝ) := by
    have hnr : (1 : ℕ) ≤ n := by omega
    exact_mod_cast hnr
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have haI : a ∈ section8OutwardSegment x i r :=
    (section8_mem_outward_segment x a i r).mpr ⟨r,le_rfl,rfl⟩
  have haT : a ∈ T := hIT haI
  have hE₁ := section8_extension_deletion_ere_one_le (by omega : 2 ≤ d) hG green
    T F S x z i r hr n hn0 (fun y hy => hwall y (hF hy))
    (fun y hy => (hYZ y (hF (Finset.mem_inter.mp hy).1)).1)
    (section8_extension_tube_disjoint_small_cube i n)
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂,Cb]; positivity
  have hcoef : 0 ≤ K₂*(n : ℝ)^q := mul_nonneg hK₂ (Real.rpow_nonneg hn0.le _)
  have hpw (y : Vertex d) :
      (max (r : ℝ) (latticeDistance x y))^((4 : ℝ)-(d : ℝ)) = w y := by
    simpa only [w,Int.cast_sub,Int.cast_ofNat,Int.cast_natCast] using
      Real.rpow_intCast (max (r : ℝ) (latticeDistance x y)) ((4 : ℤ)-(d : ℤ))
  have hE₂ : (∑ y ∈ F ∩ boundary,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (T : Set (Vertex d)) a {y} ∩
         connectionToSetEvent (T : Set (Vertex d)) a {z})) ≤
      K₂*(n : ℝ)^q*regularityEnergyTwo F boundary r x := by
    calc
      _ ≤ ∑ y ∈ F ∩ boundary, (K₂*(n : ℝ)^q)*w y := by
        apply Finset.sum_le_sum
        intro y hy
        have hyQ := hF (Finset.mem_inter.mp hy).1
        have ht := section8_extension_restricted_joint_error_le hd hG green T a y z n hnR
          haz (hYZ y hyQ).1 (hYZ y hyQ).2
        change _ ≤ K₂*(n : ℝ)^q*(max 1 (latticeDistance a y))^((4 : ℝ)-(d : ℝ)) at ht
        refine ht.trans (mul_le_mul_of_nonneg_left ?_ hcoef)
        rw [← hpw]
        exact section8_outward_shift_kernel_le x y i r hr (hwall y hyQ) _ (by linarith)
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hc := section8_extension_deletion_probability_cost (criticalPoint d) T Q F a z
  have hs := extension_connection_avoidance_split (criticalPoint d) T Q F (F ∩ boundary) a z haT
  calc
    _ ≤ (percolation d (criticalPoint d)).real {ω | z ∈ sprinklingUnexploredCluster ω T Q F a} +
        ∑ y ∈ F ∩ T,
          (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) a {y}) *
          (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) y {z}) := hc
    _ ≤ ((percolation d (criticalPoint d)).real (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) +
        ∑ y ∈ F ∩ boundary, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (T : Set (Vertex d)) a {y} ∩ connectionToSetEvent (T : Set (Vertex d)) a {z})) +
        K₁*(n : ℝ)^q*regularityEnergyOne F S r x := add_le_add hs hE₁
    _ ≤ ((percolation d (criticalPoint d)).real (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) +
        K₂*(n : ℝ)^q*regularityEnergyTwo F boundary r x) +
        K₁*(n : ℝ)^q*regularityEnergyOne F S r x := add_le_add (add_le_add le_rfl hE₂) le_rfl
    _ = _ := by dsimp only [q,S]; ring

/-- The same shifted lower budget holds under the actual positive heart law;
the baseline undeleted connection remains an ordinary fresh-copy probability. -/
theorem section8_extension_source_revealed_energy_budget {d : ℕ} (hd : 5 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (i : Fin d) (n r : ℕ) (hr : 1 ≤ r) (hn : 16*(r+1) ≤ n)
    (F boundary H H₃ F₃ : Finset (Vertex d)) (hF : F ⊆ section9FiniteEndCube i n 0)
    (hH : H ⊆ section9FiniteEndCube i n 0)
    (hH₃ : H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)))
    (hpos : percolation d (criticalPoint d) (section9RevealEvent
      (section9FiniteEndCube i n 0) H (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F F₃) ≠ 0)
    {x z : Vertex d} (hx : x ∈ section8ExtensionPositiveFaceCore i n)
    (hz : z ∈ section8ExtensionMiddleCore i n) :
    let T := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let Q := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let ν := section9RevealedLaw (criticalPoint d) Q H Q₃ H₃ F F₃
    let a := Function.update x i (x i+(r : ℤ))
    let Cb := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
    let K₁ := G^2*(4 : ℝ)^((d : ℝ)-2)
    let K₂ := G^3*Cb*(16 : ℝ)^((d : ℝ)-2)*(1+(8 : ℝ)^((d : ℝ)-4))
    (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) a {z}) ≤
      ν.real (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) +
      (n : ℝ)^((2 : ℝ)-(d : ℝ)) *
        (K₁*regularityEnergyOne F (section8ExtensionSmallCube i n) r x +
         K₂*regularityEnergyTwo F boundary r x) := by
  intro T Q Q₃ ν a Cb K₁ K₂
  have hn0 : 0 < n := by omega
  let U := sprinklingAvailableBonds T Q F
  have hdis : Disjoint (clusterRevealBonds Q F ∪ clusterRevealBonds Q₃ F₃) U := by
    apply Finset.disjoint_left.mpr
    intro b hb hbU
    rcases Finset.mem_union.mp hb with hQ | hQ₃
    · exact (Finset.mem_sdiff.mp hbU).2 hQ
    · have hbT := (mem_internalBondSet T b).mp (Finset.mem_sdiff.mp hbU).1
      have hbThird := (mem_clusterRevealBonds Q₃ F₃ b).mp hQ₃
      exact Finset.disjoint_left.mp (section9FiniteLeftTube_disjoint_third i hn0) hbT.1 hbThird.1
  have hm : MeasurableSet (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) :=
    (measurableSet_sprinklingUnexploredCluster_hits T Q F {z} a).inter
      (measurableSet_sprinklingUnexploredCluster_hits T Q F (F ∩ boundary) a).compl
  have heq := section9RevealedLaw_fresh_probability (criticalPoint d) Q H Q₃ H₃ F F₃
    hH hH₃ hpos U hdis (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) hm
    (by
      intro ω θ hagree
      have hc := sprinklingUnexploredCluster_eq_of_available_agree T Q F ω θ hagree a
      simp only [section9AvoidanceEvent,Set.mem_setOf_eq,hc])
  rw [heq]
  exact section8_extension_source_energy_budget hd hG green i n r hr hn F boundary hF hx hz

end NearCritical
