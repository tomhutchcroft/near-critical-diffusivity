module
public import NearCritical.Section9SharedTargetGeometry
public import NearCritical.Section8ExtensionTripodError

/-! The ordinary right joint factor in SAME-oriented target overlap retains
the near-target bubble kernel and one macroscopic separated arm. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- A middle-rooted ordinary joint hit of two third-cube vertices has a
macroscopic n^(2-d) factor and the clipped near-pair kernel. The finite domain
is arbitrary; the actual star-shaped tripod, not a convolution chain, is used. -/
theorem section9_middle_right_joint_probability_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 2 ≤ n →
      ∀ (R : Finset (Vertex d)) (v b b' : Vertex d),
      v ∈ section9FiniteMiddle i n →
      b ∈ section9FiniteEndCube i n (2*(n : ℝ)) →
      b' ∈ section9FiniteEndCube i n (2*(n : ℝ)) →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) v {b} ∩
          connectionToSetEvent (R : Set (Vertex d)) v {b'}) ≤
        K*(n : ℝ)^((2 : ℝ)-(d : ℝ))*
          (max 1 (latticeDistance b b'))^((4 : ℝ)-(d : ℝ)) := by
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  let Cb : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
  let K₀ : ℝ := G^3*Cb*(16 : ℝ)^((d : ℝ)-2)*(1+(8 : ℝ)^((d : ℝ)-4))
  let K : ℝ := K₀*(2 : ℝ)^((d : ℝ)-2)
  have hK : 0 ≤ K := by dsimp [K,K₀,Cb]; positivity
  refine ⟨K,hK,?_⟩
  intro i n hn R v b b' hv hb hb'
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hscale : 1 ≤ (n : ℝ)/2 := by linarith
  have hsep := section9_middle_third_sup_separation i n hv hb
  have hsep' := section9_middle_third_sup_separation i n hv hb'
  have hdiam := section9_end_cube_sup_diameter i n (2*(n : ℝ)) hb hb'
  have hbv : ((n : ℝ)/2)/8 ≤ latticeDistance b v := by
    rw [latticeDistance_comm b v]
    linarith
  have hb'v : ((n : ℝ)/2)/4 ≤ latticeDistance b' v := by
    rw [latticeDistance_comm b' v]
    linarith
  have hnear : max 1 (latticeDistance b b') ≤ 2*((n : ℝ)/2) := by
    apply max_le <;> linarith
  let P := fun x y => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (R : Set (Vertex d)) x {y})
  have hP (x y : Vertex d) : P x y ≤ twoPoint d (criticalPoint d) x y := by
    simpa only [P,Finset.coe_singleton,Finset.sum_singleton] using
      connectionToSet_probability_le_twoPoint_sum (criticalPoint d) (R : Set (Vertex d)) x {y}
  have hP0 (x y : Vertex d) : 0 ≤ P x y := measureReal_nonneg
  have hPb (u : Vertex d) : P u b ≤ twoPoint d (criticalPoint d) b u := by
    rw [twoPoint_symm (criticalPoint d) b u]
    exact hP u b
  have hpower : ((n : ℝ)/2)^((2 : ℝ)-(d : ℝ)) =
      (2 : ℝ)^((d : ℝ)-2)*(n : ℝ)^((2 : ℝ)-(d : ℝ)) := by
    rw [Real.div_rpow hn0.le (by norm_num : (0 : ℝ) ≤ 2),div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have he : -((2 : ℝ)-(d : ℝ)) = (d : ℝ)-2 := by ring
    rw [he,mul_comm]
  calc
    _ ≤ ∑ u ∈ R, P v u*(P u b*P b' u) := by
      simpa only [P,Finset.coe_singleton,Finset.sum_singleton] using
        restricted_joint_connection_probability_le (criticalPoint d) R {b'} v b
    _ ≤ ∑ u ∈ R, twoPoint d (criticalPoint d) v u*twoPoint d (criticalPoint d) b u*
        twoPoint d (criticalPoint d) b' u := by
      apply Finset.sum_le_sum
      intro u _
      rw [mul_assoc]
      exact mul_le_mul (hP v u)
        (mul_le_mul (hPb u) (hP b' u) (hP0 b' u) (twoPoint_nonneg _ _ _))
        (mul_nonneg (hP0 u b) (hP0 b' u)) (twoPoint_nonneg _ _ _)
    _ = ∑ u ∈ R, twoPoint d (criticalPoint d) b u*twoPoint d (criticalPoint d) b' u*
        twoPoint d (criticalPoint d) v u := by
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ K₀*((n : ℝ)/2)^((2 : ℝ)-(d : ℝ))*
        (max 1 (latticeDistance b b'))^((4 : ℝ)-(d : ℝ)) :=
      section8_extension_finite_tripod_error_le hd hG.le green R b b' v ((n : ℝ)/2) hscale hbv hb'v hnear
    _ = _ := by rw [hpower]; dsimp only [K]; ring

/-- The same constant bounds the actual ordinary joint hit of two finite
third-cube target families, with every target pair counted once. No target
disjointness or target regularity is required for this upper bound. -/
theorem section9_middle_right_target_joint_probability_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 2 ≤ n →
      ∀ (R Bᵢ Bⱼ : Finset (Vertex d)) (v : Vertex d),
      v ∈ section9FiniteMiddle i n →
      Bᵢ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      Bⱼ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) v (Bᵢ : Set (Vertex d)) ∩
          connectionToSetEvent (R : Set (Vertex d)) v (Bⱼ : Set (Vertex d))) ≤
        K*(n : ℝ)^((2 : ℝ)-(d : ℝ))*
          (∑ b ∈ Bᵢ, ∑ b' ∈ Bⱼ,
            (max 1 (latticeDistance b b'))^((4 : ℝ)-(d : ℝ))) := by
  obtain ⟨K,hK,hbound⟩ := section9_middle_right_joint_probability_le hd asymptotics
  refine ⟨K,hK,?_⟩
  intro i n hn R Bᵢ Bⱼ v hv hBᵢ hBⱼ
  let J := fun b b' => connectionToSetEvent (R : Set (Vertex d)) v {b} ∩
    connectionToSetEvent (R : Set (Vertex d)) v {b'}
  have hsub : (connectionToSetEvent (R : Set (Vertex d)) v (Bᵢ : Set (Vertex d)) ∩
      connectionToSetEvent (R : Set (Vertex d)) v (Bⱼ : Set (Vertex d))) ⊆
      ⋃ b ∈ Bᵢ, ⋃ b' ∈ Bⱼ, J b b' := by
    rintro ω ⟨⟨hvR,b,hb,hbR,hvb⟩,⟨_,b',hb',hb'R,hvb'⟩⟩
    exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hb,Set.mem_iUnion.mpr
      ⟨b',Set.mem_iUnion.mpr ⟨hb',⟨⟨hvR,b,rfl,hbR,hvb⟩,⟨hvR,b',rfl,hb'R,hvb'⟩⟩⟩⟩⟩⟩
  calc
    _ ≤ (percolation d (criticalPoint d)).real (⋃ b ∈ Bᵢ, ⋃ b' ∈ Bⱼ, J b b') :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ b ∈ Bᵢ, ∑ b' ∈ Bⱼ, (percolation d (criticalPoint d)).real (J b b') := by
      refine (measureReal_biUnion_finset_le Bᵢ _).trans ?_
      apply Finset.sum_le_sum
      intro b _
      exact measureReal_biUnion_finset_le Bⱼ _
    _ ≤ ∑ b ∈ Bᵢ, ∑ b' ∈ Bⱼ,
        K*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(max 1 (latticeDistance b b'))^((4 : ℝ)-(d : ℝ)) :=
      Finset.sum_le_sum (fun b hb => Finset.sum_le_sum
        (fun b' hb' => hbound i n hn R v b b' hv (hBᵢ hb) (hBⱼ hb')))
    _ = _ := by simp only [Finset.mul_sum]

end NearCritical
