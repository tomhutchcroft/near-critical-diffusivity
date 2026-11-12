module
public import NearCritical.Section9FiniteTripodDecay
public import NearCritical.Section9AvoidanceCertificate

/-! Actual bad-hit error for the fresh-copy avoidance lower bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The actual deleted component jointly hitting two separated target families
has the finite-tripod error scale. No multipoint estimate is assumed. -/
theorem section9_avoidance_bad_hit_le {d : ℕ} (hd : 5 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D Q F B V : Finset (Vertex d)) (z : Vertex d), z ∈ D →
      ∀ n : ℝ, 1 ≤ n →
      (∀ y ∈ B, n/16 ≤ latticeDistance z y) →
      (∀ v ∈ V, n/16 ≤ latticeDistance z v) →
      (∀ y ∈ B, ∀ v ∈ V, n/16 ≤ latticeDistance y v) →
      (percolation d (criticalPoint d)).real
        {ω | (sprinklingUnexploredCluster ω D Q F z ∩ B).Nonempty ∧
          (sprinklingUnexploredCluster ω D Q F z ∩ V).Nonempty} ≤
        (B.card : ℝ)*(V.card : ℝ)*C*n^(6-2*(d : ℝ)) := by
  let Cb : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
  let K : ℝ := 2*G*(G^2*Cb)*(2 : ℝ)^((d : ℝ)-2)
  let q : ℝ := 6-2*(d : ℝ)
  let C : ℝ := K/(16 : ℝ)^q
  have hK : 0 ≤ K := by dsimp [K,Cb]; positivity
  have hC : 0 ≤ C := div_nonneg hK (Real.rpow_nonneg (by norm_num) _)
  refine ⟨C,hC,?_⟩
  intro D Q F B V z hz n hn hzy hzv hyv
  let J := fun y v => connectionToSetEvent (D : Set (Vertex d)) z {y} ∩
    connectionToSetEvent (D : Set (Vertex d)) z {v}
  have hsub : {ω | (sprinklingUnexploredCluster ω D Q F z ∩ B).Nonempty ∧
      (sprinklingUnexploredCluster ω D Q F z ∩ V).Nonempty} ⊆
      ⋃ y ∈ B, ⋃ v ∈ V, J y v := by
    rintro ω ⟨⟨y,hy⟩,⟨v,hv⟩⟩
    obtain ⟨hyC,hyB⟩ := Finset.mem_inter.mp hy
    obtain ⟨hvC,hvV⟩ := Finset.mem_inter.mp hv
    obtain ⟨hyD,hzyReach⟩ := (mem_sprinklingUnexploredCluster ω D Q F z y).mp hyC
    obtain ⟨hvD,hzvReach⟩ := (mem_sprinklingUnexploredCluster ω D Q F z v).mp hvC
    have hle : sprinklingUnexploredGraph ω D Q F ≤ restrictedGraph ω (D : Set (Vertex d)) :=
      fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩
    exact Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hyB,
      Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hvV,
        ⟨⟨hz,y,rfl,hyD,hzyReach.mono hle⟩,⟨hz,v,rfl,hvD,hzvReach.mono hle⟩⟩⟩⟩⟩⟩
  have heach (y : Vertex d) (hy : y ∈ B) (v : Vertex d) (hv : v ∈ V) :
      (percolation d (criticalPoint d)).real (J y v) ≤ C*n^q := by
    have hn0 : 0 < n := zero_lt_one.trans_le hn
    have ht := section9_restricted_tripod_decay hd hG green D z y v
      (by positivity : 0 < n/16) (hzy y hy) (hzv v hv) (hyv y hy v hv)
    change (percolation d (criticalPoint d)).real (J y v) ≤ K*(n/16)^q at ht
    refine ht.trans_eq ?_
    rw [Real.div_rpow hn0.le (by norm_num : (0 : ℝ) ≤ 16)]
    dsimp only [C]
    ring
  calc
    _ ≤ (percolation d (criticalPoint d)).real (⋃ y ∈ B, ⋃ v ∈ V, J y v) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ y ∈ B, (percolation d (criticalPoint d)).real (⋃ v ∈ V, J y v) :=
      measureReal_biUnion_finset_le B _
    _ ≤ ∑ y ∈ B, ∑ v ∈ V, C*n^q := by
      apply Finset.sum_le_sum
      intro y hy
      exact (measureReal_biUnion_finset_le V (J y)).trans
        (Finset.sum_le_sum fun v hv => heach y hy v hv)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp only [q]; ring

/-- Fresh deleted-graph connection mass is bounded by actual avoidance plus
the derived bad-hit error. The baseline is not an undeleted connection. -/
theorem section9_avoidance_baseline_le_avoidance_add_bad_hit {d : ℕ} (hd : 5 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D Q F B V : Finset (Vertex d)) (z : Vertex d), z ∈ D →
      ∀ n : ℝ, 1 ≤ n →
      (∀ y ∈ B, n/16 ≤ latticeDistance z y) →
      (∀ v ∈ V, n/16 ≤ latticeDistance z v) →
      (∀ y ∈ B, ∀ v ∈ V, n/16 ≤ latticeDistance y v) →
      (percolation d (criticalPoint d)).real
        {ω | (sprinklingUnexploredCluster ω D Q F z ∩ B).Nonempty} ≤
      (percolation d (criticalPoint d)).real (section9AvoidanceEvent D D Q F B V z) +
        (B.card : ℝ)*(V.card : ℝ)*C*n^(6-2*(d : ℝ)) := by
  obtain ⟨C,hC,hbad⟩ := section9_avoidance_bad_hit_le hd hG green
  refine ⟨C,hC,?_⟩
  intro D Q F B V z hz n hn hzy hzv hyv
  let J : Set (Configuration d) :=
    {ω | (sprinklingUnexploredCluster ω D Q F z ∩ B).Nonempty ∧
      (sprinklingUnexploredCluster ω D Q F z ∩ V).Nonempty}
  have hsub : {ω | (sprinklingUnexploredCluster ω D Q F z ∩ B).Nonempty} ⊆
      section9AvoidanceEvent D D Q F B V z ∪ J := by
    intro ω hB
    by_cases hV : (sprinklingUnexploredCluster ω D Q F z ∩ V).Nonempty
    · exact Or.inr ⟨hB,hV⟩
    · exact Or.inl ⟨hB,hV⟩
  calc
    _ ≤ (percolation d (criticalPoint d)).real (section9AvoidanceEvent D D Q F B V z ∪ J) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (percolation d (criticalPoint d)).real (section9AvoidanceEvent D D Q F B V z) +
        (percolation d (criticalPoint d)).real J := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (hbad D Q F B V z hz n hn hzy hzv hyv)

end NearCritical
