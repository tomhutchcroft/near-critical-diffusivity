module

public import NearCritical.MaskedWaterCubeFirstHit
public import NearCritical.BulkPercolation
public import NearCritical.ProfileCountableBKStrict

/-! Finite cut-sum probability reductions under the SAME actual bulk law.
No domain-law replacement, stationarity or quantitative arm premise is used. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset MeasureTheory
open scoped Classical

private lemma masked_open_pair_occurrence {E : Type*} {ω : E → Bool}
    (A B : Set (E → Bool)) (F G : Finset E) (hFG : Disjoint F G)
    (hFo : ∀ e ∈ F, ω e=true) (hGo : ∀ e ∈ G, ω e=true)
    (hF : ∀ θ, (∀ e ∈ F, θ e=true) → θ ∈ A)
    (hG : ∀ θ, (∀ e ∈ G, θ e=true) → θ ∈ B) :
    DisjointOccurrence A B ω := by
  refine ⟨F,G,F.finite_toSet,G.finite_toSet,?_,?_,?_⟩
  · exact Set.disjoint_left.mpr (fun e heF heG => Finset.disjoint_left.mp hFG heF heG)
  · intro θ hθ
    exact hF θ (fun e he => (hθ e he).trans (hFo e he))
  · intro θ hθ
    exact hG θ (fun e he => (hθ e he).trans (hGo e he))

private lemma masked_open_triple_occurrence {E : Type*} {ω : E → Bool}
    (A B C : Set (E → Bool)) (F G H : Finset E)
    (hFG : Disjoint F G) (hFH : Disjoint F H) (hGH : Disjoint G H)
    (hFo : ∀ e ∈ F, ω e=true) (hGo : ∀ e ∈ G, ω e=true) (hHo : ∀ e ∈ H, ω e=true)
    (hF : ∀ θ, (∀ e ∈ F, θ e=true) → θ ∈ A)
    (hG : ∀ θ, (∀ e ∈ G, θ e=true) → θ ∈ B)
    (hH : ∀ θ, (∀ e ∈ H, θ e=true) → θ ∈ C) :
    DisjointOccurrence A {θ | DisjointOccurrence B C θ} ω := by
  have hdis : Disjoint F (G∪H) := Finset.disjoint_left.mpr (by
    intro e heF he
    rcases Finset.mem_union.mp he with heG | heH
    · exact Finset.disjoint_left.mp hFG heF heG
    · exact Finset.disjoint_left.mp hFH heF heH)
  apply masked_open_pair_occurrence A _ F (G∪H) hdis hFo
    (fun e he => by
      rcases Finset.mem_union.mp he with heG | heH
      · exact hGo e heG
      · exact hHo e heH) hF
  intro θ hθ
  exact masked_open_pair_occurrence B C G H hGH
    (fun e he => hθ e (Finset.mem_union_left H he))
    (fun e he => hθ e (Finset.mem_union_right G he)) hG hH

private lemma masked_increasing_occurrence {E : Type*} {A B : Set (E → Bool)}
    (hA : BK.Increasing A) (hB : BK.Increasing B) :
    BK.Increasing {ω | DisjointOccurrence A B ω} := by
  intro ω η h hω
  obtain ⟨F,G,hFfin,hGfin,hdis,hFo,hGo,hF,hG⟩ :=
    BK.openDisjointOccurrence_of_disjointOccurrence hω
  exact BK.OpenDisjointOccurrence.to_disjointOccurrence
    ⟨F,G,hFfin,hGfin,hdis,(fun e he => h e (hFo e he)),
      (fun e he => h e (hGo e he)),hF,hG⟩ hA hB

private lemma bulk_occurrence_probability_le {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (height δ : ℝ) (p q P : unitInterval) (hP : (P : ℝ)<1)
    (hpP : p≤P) (hqP : q≤P) (A B : Set (Configuration d))
    (hA : BK.Increasing A) (hB : BK.Increasing B) :
    (bulkPercolation U i height δ p q).real {ω | DisjointOccurrence A B ω} ≤
      (bulkPercolation U i height δ p q).real A *
        (bulkPercolation U i height δ p q).real B := by
  exact percolationProfile_bk_of_uniform_lt_one d
    (fun e => if e ∈ internalBondSet (bulkVertices U i height δ) then q else p)
    P hP (fun e => by split <;> assumption) A B hA hB

private lemma bulk_triple_occurrence_probability_le {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (height δ : ℝ) (p q P : unitInterval) (hP : (P : ℝ)<1)
    (hpP : p≤P) (hqP : q≤P) (A B C : Set (Configuration d))
    (hA : BK.Increasing A) (hB : BK.Increasing B) (hC : BK.Increasing C) :
    (bulkPercolation U i height δ p q).real
      {ω | DisjointOccurrence A {θ | DisjointOccurrence B C θ} ω} ≤
      (bulkPercolation U i height δ p q).real A *
        (bulkPercolation U i height δ p q).real B *
        (bulkPercolation U i height δ p q).real C := by
  let μ := bulkPercolation U i height δ p q
  calc
    _ ≤ μ.real A * μ.real {θ | DisjointOccurrence B C θ} :=
      bulk_occurrence_probability_le U i height δ p q P hP hpP hqP A _ hA
        (masked_increasing_occurrence hB hC)
    _ ≤ μ.real A * (μ.real B * μ.real C) := mul_le_mul_of_nonneg_left
      (bulk_occurrence_probability_le U i height δ p q P hP hpP hqP B C hB hC) measureReal_nonneg
    _ = _ := by ring

/-- Three-segment actual bulk-law reduction. Every factor stays under the
same inhomogeneous law; all dependence on BOTH finite cut vertices is retained. -/
theorem maskedWaterCube_two_cuts_probability_le {d : ℕ}
    (i : Fin d) (r R : ℕ) (δ : ℝ) (p q P : unitInterval)
    (hP : (P : ℝ)<1) (hpP : p≤P) (hqP : q≤P)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (m n : ℤ) (hm : 0≤m) (hxm : x.val i+(r : ℤ)≤m)
    (hmn : m≤n) (hnH : n<2*(r : ℤ)+1) :
    let U := waterCube d i r R
    let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
    let A := fun u => connectionToSetEvent
      ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (m-r)) x.val {u}
    let B := fun u v => connectionToSetEvent
      ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) u {v}
    let C := fun v => connectionToSetEvent (finiteHeightSlab i (-(r : ℤ)) ((r : ℤ)+1)) v
      (Subtype.val '' positiveFace U i)
    μ.real (latticeBoundaryConnectionEvent U x (positiveFace U i)) ≤
      ∑ u ∈ U.filter (fun u => u i+(r : ℤ)=m),
        ∑ v ∈ U.filter (fun v => v i+(r : ℤ)=n),
          μ.real (A u)*μ.real (B u v)*μ.real (C v) := by
  let U := waterCube d i r R
  let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
  let A := fun u => connectionToSetEvent
    ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (m-r)) x.val {u}
  let B := fun u v => connectionToSetEvent
    ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) u {v}
  let C := fun v => connectionToSetEvent (finiteHeightSlab i (-(r : ℤ)) ((r : ℤ)+1)) v
    (Subtype.val '' positiveFace U i)
  let E := fun u v => {ω | DisjointOccurrence (A u) {θ | DisjointOccurrence (B u v) (C v) θ} ω}
  let M := U.filter (fun u => u i+(r : ℤ)=m)
  let N := U.filter (fun v => v i+(r : ℤ)=n)
  have hsubset : latticeBoundaryConnectionEvent U x (positiveFace U i) ⊆
      ⋃ u ∈ M, ⋃ v ∈ N, E u v := by
    intro ω hω
    obtain ⟨u,v,hu,hv,hum,hvn,F,G,H,hFG,hFH,hGH,hFo,hGo,hHo,hF,hG,hH⟩ :=
      maskedWaterCube_two_first_heights_open_forcing i r R ω x hx m n hm hxm hmn hnH hω
    refine Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hu,hum⟩,
      Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hv,hvn⟩,?_⟩⟩⟩⟩
    exact masked_open_triple_occurrence (A u) (B u v) (C v) F G H
      hFG hFH hGH hFo hGo hHo hF hG hH
  have hbound (u v : Vertex d) : μ.real (E u v) ≤ μ.real (A u)*μ.real (B u v)*μ.real (C v) :=
    bulk_triple_occurrence_probability_le U i (2*(r : ℝ)+1) δ p q P hP hpP hqP _ _ _
      (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
      (connectionToSetEvent_increasing _ _ _)
  change μ.real (latticeBoundaryConnectionEvent U x (positiveFace U i)) ≤
    ∑ u ∈ M, ∑ v ∈ N, μ.real (A u)*μ.real (B u v)*μ.real (C v)
  calc
    _ ≤ μ.real (⋃ u ∈ M, ⋃ v ∈ N, E u v) := by
      letI : IsProbabilityMeasure μ := by
        change IsProbabilityMeasure (percolationProfile d _)
        infer_instance
      exact measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ ∑ u ∈ M, μ.real (⋃ v ∈ N, E u v) := measureReal_biUnion_finset_le M _
    _ ≤ ∑ u ∈ M, ∑ v ∈ N, μ.real (E u v) :=
      Finset.sum_le_sum (fun u _ => measureReal_biUnion_finset_le N (E u))
    _ ≤ _ := Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hbound u v))

/-- Two-segment counterpart, retaining the actual finite cut vertex and the
same bulk law in BOTH factors. Equality of start and cut heights is allowed. -/
theorem maskedWaterCube_one_cut_probability_le {d : ℕ}
    (i : Fin d) (r R : ℕ) (δ : ℝ) (p q P : unitInterval)
    (hP : (P : ℝ)<1) (hpP : p≤P) (hqP : q≤P)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (n : ℤ) (hn : 0≤n) (hxn : x.val i+(r : ℤ)≤n) (hnH : n<2*(r : ℤ)+1) :
    let U := waterCube d i r R
    let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
    let A := fun v => connectionToSetEvent
      ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) x.val {v}
    let C := fun v => connectionToSetEvent (finiteHeightSlab i (-(r : ℤ)) ((r : ℤ)+1)) v
      (Subtype.val '' positiveFace U i)
    μ.real (latticeBoundaryConnectionEvent U x (positiveFace U i)) ≤
      ∑ v ∈ U.filter (fun v => v i+(r : ℤ)=n), μ.real (A v)*μ.real (C v) := by
  let U := waterCube d i r R
  let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
  let A := fun v => connectionToSetEvent
    ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) x.val {v}
  let C := fun v => connectionToSetEvent (finiteHeightSlab i (-(r : ℤ)) ((r : ℤ)+1)) v
    (Subtype.val '' positiveFace U i)
  let E := fun v => {ω | DisjointOccurrence (A v) (C v) ω}
  let N := U.filter (fun v => v i+(r : ℤ)=n)
  have hsubset : latticeBoundaryConnectionEvent U x (positiveFace U i) ⊆ ⋃ v ∈ N, E v := by
    intro ω hω
    obtain ⟨v,hv,hvn,F,H,hFH,hFo,hHo,hF,hH⟩ :=
      maskedWaterCube_first_height_open_forcing i r R ω x hx n hn hxn hnH hω
    refine Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hv,hvn⟩,?_⟩⟩
    exact masked_open_pair_occurrence (A v) (C v) F H hFH hFo hHo hF hH
  have hbound (v : Vertex d) : μ.real (E v) ≤ μ.real (A v)*μ.real (C v) :=
    bulk_occurrence_probability_le U i (2*(r : ℝ)+1) δ p q P hP hpP hqP _ _
      (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
  change μ.real (latticeBoundaryConnectionEvent U x (positiveFace U i)) ≤
    ∑ v ∈ N, μ.real (A v)*μ.real (C v)
  calc
    _ ≤ μ.real (⋃ v ∈ N, E v) := by
      letI : IsProbabilityMeasure μ := by
        change IsProbabilityMeasure (percolationProfile d _)
        infer_instance
      exact measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ ∑ v ∈ N, μ.real (E v) := measureReal_biUnion_finset_le N E
    _ ≤ _ := Finset.sum_le_sum (fun v _ => hbound v)

end NearCritical
