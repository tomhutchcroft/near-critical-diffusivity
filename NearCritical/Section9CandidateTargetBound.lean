module
public import NearCritical.Section9AvoidanceOccurrence
public import NearCritical.Section8ReflectionGeometry
public import NearCritical.Section9PivotalMeanUpper
public import NearCritical.ThreePointDiagram

/-! Actual last-exit candidate to negative-face target upper bounds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem candidate_coordinate_gap_le {d : ℕ} (i : Fin d) (a b : Vertex d) :
    (b i : ℝ)-(a i : ℝ) ≤ latticeDistance a b := by
  have hcoord : |(a i : ℝ)-(b i : ℝ)| ≤ latticeDistance a b := by
    simpa only [latticeDistance,vertexReal,Real.dist_eq] using
      dist_le_pi_dist (vertexReal a) (vertexReal b) i
  have hgap : (b i : ℝ)-(a i : ℝ) ≤ |(a i : ℝ)-(b i : ℝ)| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  exact hgap.trans hcoord

/-- A last-exit outer endpoint is within one lattice step of C⊆T12,
so it is separated from the negative Q3 face. It need not belong to S2. -/
theorem section9_source_candidate_target_separation {d : ℕ} (i : Fin d) (n : ℕ)
    (hn : 16 ≤ n) (C F₃ : Finset (Vertex d))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (t : (Vertex d × Vertex d) × Bond d)
    (ht : t ∈ section9AvoidanceLastExitCandidates
      (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) C
      (section9FiniteEndCube i n (2*(n : ℝ))) F₃)
    (y : Vertex d) (hy : y ∈ section8ExtensionNegativeFaceCore i n) :
    (n : ℝ)/16 ≤ latticeDistance t.1.2 y := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hm := (Finset.mem_filter.mp ht).2
  have huL := hCL hm.1
  have huUpper := (Finset.mem_filter.mp huL).2.2.1
  have hfull : (openGraph (fun _ : Bond d => true)).Adj t.1.1 t.1.2 :=
    ⟨t.2,rfl,hm.2.2⟩
  have hstep : (t.1.2 i : ℝ) ≤ (t.1.1 i : ℝ)+1 := by
    exact_mod_cast (openGraph_adj_height_bounds hfull i).2
  have hyQ := (Finset.mem_filter.mp hy).1
  have hyLower := ((Finset.mem_filter.mp hyQ).2 i).1
  simp only [ite_true] at hyLower
  have hgap := candidate_coordinate_gap_le i t.1.2 y
  linarith

/-- The actual outside-C deleted component of a last-exit outer endpoint
hits a negative-face family with at most the ordinary two-point upper scale.
No conditional cluster law or candidate probability estimate is assumed. -/
theorem section9_source_candidate_deleted_hit_probability_le {d : ℕ} (hd : 2 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (i : Fin d) (n : ℕ) (hn : 16 ≤ n) (C F₃ B : Finset (Vertex d))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hB : B ⊆ section8ExtensionNegativeFaceCore i n)
    (t : (Vertex d × Vertex d) × Bond d)
    (ht : t ∈ section9AvoidanceLastExitCandidates
      (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) C
      (section9FiniteEndCube i n (2*(n : ℝ))) F₃) :
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    (percolation d (criticalPoint d)).real
      {ω | (sprinklingUnexploredCluster ω (R \ C) Q₃ F₃ t.1.2 ∩ B).Nonempty} ≤
      G*(16 : ℝ)^((d : ℝ)-2)*(B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ)) := by
  intro Q₃ R
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hm := Finset.mem_filter.mp ht
  have hvR : t.1.2 ∈ R := (Finset.mem_product.mp (Finset.mem_product.mp hm.1).1).2
  have hvDC : t.1.2 ∈ R \ C := Finset.mem_sdiff.mpr ⟨hvR,hm.2.2.1⟩
  have hsub : {ω : Configuration d |
      (sprinklingUnexploredCluster ω (R \ C) Q₃ F₃ t.1.2 ∩ B).Nonempty} ⊆
      connectionToSetEvent ((R \ C : Finset (Vertex d)) : Set (Vertex d)) t.1.2 (B : Set (Vertex d)) := by
    rintro ω ⟨y,hy⟩
    obtain ⟨hyCluster,hyB⟩ := Finset.mem_inter.mp hy
    obtain ⟨hyDC,hreach⟩ := (mem_sprinklingUnexploredCluster ω (R \ C) Q₃ F₃ t.1.2 y).mp hyCluster
    have hle : sprinklingUnexploredGraph ω (R \ C) Q₃ F₃ ≤
        restrictedGraph ω ((R \ C : Finset (Vertex d)) : Set (Vertex d)) :=
      fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩
    exact ⟨hvDC,y,hyB,hyDC,hreach.mono hle⟩
  have heach (y : Vertex d) (hy : y ∈ B) :
      twoPoint d (criticalPoint d) t.1.2 y ≤ G*((n : ℝ)/16)^((2 : ℝ)-(d : ℝ)) :=
    (green t.1.2 y).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity)
        ((section9_source_candidate_target_separation i n hn C F₃ hCL t ht y (hB hy)).trans
          (le_max_right _ _)) (by linarith)) hG)
  calc
    _ ≤ (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((R \ C : Finset (Vertex d)) : Set (Vertex d)) t.1.2 (B : Set (Vertex d))) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ y ∈ B, twoPoint d (criticalPoint d) t.1.2 y :=
      connectionToSet_probability_le_twoPoint_sum (criticalPoint d) _ _ B
    _ ≤ ∑ _y ∈ B, G*((n : ℝ)/16)^((2 : ℝ)-(d : ℝ)) :=
      Finset.sum_le_sum fun y hy => heach y hy
    _ = (B.card : ℝ)*(G*((n : ℝ)/16)^((2 : ℝ)-(d : ℝ))) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ = _ := by
      rw [Real.div_rpow hn0.le (by norm_num : (0 : ℝ) ≤ 16),div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16)]
      have he : -((2 : ℝ)-(d : ℝ)) = (d : ℝ)-2 := by ring
      rw [he]
      ring

end NearCritical
