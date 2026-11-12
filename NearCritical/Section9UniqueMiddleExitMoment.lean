module
public import NearCritical.Section9UniqueMiddleFirstMoment
public import NearCritical.Section9ExitFaceCardUpper
public import NearCritical.Section9AvoidanceBadHit
public import NearCritical.Section9FreshEvent

/-! Actual source middle/exit moments and the unique-left X2 error. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem middle_exit_product_integral {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (L Q F Z V : Finset (Vertex d)) (x : Vertex d) :
    Integrable (fun ω => ((sprinklingUnexploredCluster ω L Q F x ∩ Z).card : ℝ)*
      ((sprinklingUnexploredCluster ω L Q F x ∩ V).card : ℝ)) μ ∧
    (∫ ω, ((sprinklingUnexploredCluster ω L Q F x ∩ Z).card : ℝ)*
      ((sprinklingUnexploredCluster ω L Q F x ∩ V).card : ℝ) ∂μ) =
      ∑ z ∈ Z, ∑ v ∈ V, μ.real {ω | z ∈ sprinklingUnexploredCluster ω L Q F x ∧
        v ∈ sprinklingUnexploredCluster ω L Q F x} := by
  let A := fun z v => {ω : Configuration d | z ∈ sprinklingUnexploredCluster ω L Q F x ∧
    v ∈ sprinklingUnexploredCluster ω L Q F x}
  have hA (z v : Vertex d) : MeasurableSet (A z v) :=
    (measurableSet_sprinklingUnexploredCluster_mem L Q F x z).inter
      (measurableSet_sprinklingUnexploredCluster_mem L Q F x v)
  have hcard (ω : Configuration d) (S : Finset (Vertex d)) :
      ((sprinklingUnexploredCluster ω L Q F x ∩ S).card : ℝ) =
        ∑ y ∈ S, if y ∈ sprinklingUnexploredCluster ω L Q F x then (1 : ℝ) else 0 := by
    have heq : S.filter (fun y => y ∈ sprinklingUnexploredCluster ω L Q F x) =
        sprinklingUnexploredCluster ω L Q F x ∩ S := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_inter,and_comm]
    rw [Finset.sum_boole,heq]
  have hsum (ω : Configuration d) :
      ((sprinklingUnexploredCluster ω L Q F x ∩ Z).card : ℝ)*
        ((sprinklingUnexploredCluster ω L Q F x ∩ V).card : ℝ) =
      ∑ z ∈ Z, ∑ v ∈ V, (A z v).indicator (fun _ => (1 : ℝ)) ω := by
    rw [hcard ω Z,hcard ω V,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hz : z ∈ sprinklingUnexploredCluster ω L Q F x <;>
      by_cases hv : v ∈ sprinklingUnexploredCluster ω L Q F x <;>
      simp [A,Set.indicator_apply,hz,hv]
  have hi (z : Vertex d) : Integrable
      (fun ω => ∑ v ∈ V, (A z v).indicator (fun _ => (1 : ℝ)) ω) μ :=
    integrable_finsetSum V (fun v _ => (integrable_const (1 : ℝ)).indicator (hA z v))
  constructor
  · simp_rw [hsum]
    exact integrable_finsetSum Z (fun z _ => hi z)
  · simp_rw [hsum]
    rw [integral_finsetSum Z (fun z _ => hi z)]
    apply Finset.sum_congr rfl
    intro z _
    rw [integral_finsetSum V (fun v _ => (integrable_const (1 : ℝ)).indicator (hA z v))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_indicator_one (hA z v)

private theorem middle_exit_local_measurable {d : ℕ}
    (s : Finset (Bond d)) (A : Set (Configuration d))
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ A ↔ θ ∈ A)) :
    MeasurableSet A := by
  let A₀ : Set ((b : s) → Bool) := {ξ | extendConfiguration s (fun _ => false) ξ ∈ A}
  have heq : A = s.restrict ⁻¹' A₀ := by
    ext ω
    apply hlocal ω (extendConfiguration s (fun _ => false) (s.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  rw [heq]
  exact (Set.toFinite A₀).measurableSet.preimage (Finset.measurable_restrict s)

private theorem middle_exit_separation {d : ℕ} (i : Fin d) (n : ℕ) (hn : 16 ≤ n)
    (x z v : Vertex d) (hx : x ∈ section8ExtensionPositiveFaceCore i n)
    (hz : z ∈ section8ExtensionMiddleCore i n) (hv : v ∈ section9ExitFace i n) :
    (n : ℝ)/16 ≤ latticeDistance x z ∧ (n : ℝ)/16 ≤ latticeDistance x v ∧
      (n : ℝ)/16 ≤ latticeDistance z v := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hxQ := (Finset.mem_filter.mp hx).1
  have hxShape := (Finset.mem_filter.mp hxQ).2 i
  have hzShape := ((section8_mem_extension_middle_core i n z).mp hz) i
  simp only [ite_true,sub_zero] at hxShape
  simp only [ite_true] at hzShape
  have hvcoord := section9_exit_face_coordinate i n hv
  have hvLower : 11*(n : ℝ)/8-1 ≤ (v i : ℝ) := by
    rw [hvcoord]
    push_cast
    linarith [Int.le_ceil (11*(n : ℝ)/8)]
  have hgap (a b : Vertex d) : (b i : ℝ)-(a i : ℝ) ≤ latticeDistance a b := by
    have hh : |(b i : ℝ)-(a i : ℝ)| ≤ latticeDistance a b := by
      simpa only [latticeDistance,vertexReal,Real.dist_eq,abs_sub_comm] using
        dist_le_pi_dist (vertexReal a) (vertexReal b) i
    exact (le_abs_self _).trans hh
  refine ⟨?_,?_,?_⟩
  · linarith [hgap x z,hxShape.2,hzShape.1]
  · linarith [hgap x v,hxShape.2]
  · linarith [hgap z v,hzShape.2]

private theorem middle_card_upper {d : ℕ} (i : Fin d) (n : ℕ) :
    (section8ExtensionMiddleCore i n).card ≤ (6*n+1)^d := by
  have hh := Finset.card_le_card (Finset.filter_subset
    (fun z => z ∈ sprinklingEndCube i ((n : ℝ)/2) (n : ℝ)) (centeredBox d (3*n)))
  have hc : (centeredBox d (3*n)).card = (6*n+1)^d := by
    simp only [centeredBox,Fintype.card_piFinset,Int.card_Icc]
    have he : ((3*n : ℕ) : ℤ)+1-(-((3*n : ℕ) : ℤ)) = ((6*n+1 : ℕ) : ℤ) := by omega
    simp only [he,Int.toNat_natCast,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact hh.trans_eq hc

/-- The actual source left-cluster middle/exit product has moment at most K*n^5.
Only the explicit Green input and legal positive outer reveal are needed. -/
theorem section9_source_middle_exit_product_moment_upper {d : ℕ} (hd : 5 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 16 ≤ n →
      ∀ (H₁ H₃ F₁ F₃ : Finset (Vertex d)) (x : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      x ∈ section8ExtensionPositiveFaceCore i n →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      (∫ ω, ((sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ section8ExtensionMiddleCore i n).card : ℝ)*
        ((sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ section9ExitFace i n).card : ℝ) ∂ν) ≤ K*(n : ℝ)^5 := by
  obtain ⟨C,hC,hbad⟩ := section9_avoidance_bad_hit_le hd hG green
  refine ⟨C*(7 : ℝ)^d*(7 : ℝ)^(d-1),by positivity,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ x hH₁ hH₃ hpos hx L Q₁ Q₃ ν
  let Z := section8ExtensionMiddleCore i n
  let V := section9ExitFace i n
  let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
  let A := fun z v => {ω : Configuration d | z ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x ∧
    v ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x}
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hcardpos : 0 < (Z.card : ℝ) :=
    (div_pos (pow_pos hnpos d) (by positivity)).trans_le (section9_middle_core_card_lower i n (by omega))
  obtain ⟨z₀,hz₀⟩ := Finset.card_pos.mp (show 0 < Z.card by exact_mod_cast hcardpos)
  have hgeom := section8_extension_source_geometry i n 0 (by simpa using hn) hx hz₀
  have hxI : x ∈ section8OutwardSegment x i 0 :=
    (section8_mem_outward_segment x x i 0).mpr ⟨0,by omega,by simp⟩
  have hxL : x ∈ L := hgeom.2.1 hxI
  have hprob (z : Vertex d) (hz : z ∈ Z) (v : Vertex d) (hv : v ∈ V) :
      ν.real (A z v) ≤ C*(n : ℝ)^(6-2*(d : ℝ)) := by
    let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
    have hA : MeasurableSet (A z v) :=
      (measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ x z).inter
        (measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ x v)
    have hfresh := section9RevealedLaw_fresh_probability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      hH₁ hH₃ hpos U (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃
        (section9FiniteLeftTube_disjoint_third i hn0) (section9FiniteRightTube_disjoint_first i hn0))
      (A z v) hA (by
        intro ω θ hagree
        have heq := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ
          (fun b hb => hagree b (Finset.mem_union_left _ hb)) x
        simp only [A,Set.mem_setOf_eq,heq])
    rw [hfresh]
    obtain ⟨hxz,hxv,hzv⟩ := middle_exit_separation i n hn x z v hx hz hv
    have hh := hbad L Q₁ F₁ {z} {v} x hxL (n : ℝ) hnR
      (by intro y hy; simpa only [Finset.mem_singleton.mp hy] using hxz)
      (by intro y hy; simpa only [Finset.mem_singleton.mp hy] using hxv)
      (by intro y hy w hw; simpa only [Finset.mem_singleton.mp hy,Finset.mem_singleton.mp hw] using hzv)
    simpa [A,Finset.Nonempty,Finset.mem_inter,Finset.mem_singleton] using hh
  have hZ : (Z.card : ℝ) ≤ (7 : ℝ)^d*(n : ℝ)^d := by
    calc
      _ ≤ (6*(n : ℝ)+1)^d := by exact_mod_cast middle_card_upper i n
      _ ≤ (7*(n : ℝ))^d := by gcongr <;> linarith
      _ = _ := mul_pow _ _ _
  have hV : (V.card : ℝ) ≤ (7 : ℝ)^(d-1)*(n : ℝ)^(d-1) := by
    calc
      _ ≤ (6*(n : ℝ)+1)^(d-1) := by exact_mod_cast section9_exit_face_card_upper i n
      _ ≤ (7*(n : ℝ))^(d-1) := by gcongr <;> linarith
      _ = _ := mul_pow _ _ _
  have hpower : (n : ℝ)^d*(n : ℝ)^(d-1)*(n : ℝ)^(6-2*(d : ℝ)) = (n : ℝ)^5 := by
    rw [← Real.rpow_natCast (n : ℝ) d,← Real.rpow_natCast (n : ℝ) (d-1),
      ← Real.rpow_add hnpos,← Real.rpow_add hnpos]
    have he : (d : ℝ)+((d-1 : ℕ) : ℝ)+(6-2*(d : ℝ)) = 5 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
      ring
    rw [he]
    norm_num
  rw [(middle_exit_product_integral ν L Q₁ F₁ Z V x).2]
  calc
    _ ≤ ∑ _z ∈ Z, ∑ _v ∈ V, C*(n : ℝ)^(6-2*(d : ℝ)) :=
      Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun v hv => hprob z hz v hv
    _ = (Z.card : ℝ)*(V.card : ℝ)*(C*(n : ℝ)^(6-2*(d : ℝ))) := by
      simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ ((7 : ℝ)^d*(n : ℝ)^d)*((7 : ℝ)^(d-1)*(n : ℝ)^(d-1))*
        (C*(n : ℝ)^(6-2*(d : ℝ))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hZ hV (Nat.cast_nonneg _) (by positivity)) (by positivity)
    _ = _ := by rw [show (7 : ℝ)^d*(n : ℝ)^d*((7 : ℝ)^(d-1)*(n : ℝ)^(d-1))*
        (C*(n : ℝ)^(6-2*(d : ℝ))) =
        (C*(7 : ℝ)^d*(7 : ℝ)^(d-1))*
          ((n : ℝ)^d*(n : ℝ)^(d-1)*(n : ℝ)^(6-2*(d : ℝ))) by ring,hpower]

/-- The actual unique-left X2 random variable has the paper error scale.
The same raw moment constant works uniformly for every finite W. -/
theorem section9_source_unique_middle_exit_moment_upper {d : ℕ} (hd : 5 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 16 ≤ n →
      ∀ (H₁ H₃ F₁ F₃ W : Finset (Vertex d)) (x : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      x ∈ section8ExtensionPositiveFaceCore i n →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      (∫ ω, (n : ℝ)^((4 : ℝ)-(d : ℝ))*
        actualUniqueMiddleCount ω L Q₁ F₁ W x (section8ExtensionMiddleCore i n)*
        ((sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ section9ExitFace i n).card : ℝ) ∂ν) ≤
        K*(n : ℝ)^((9 : ℝ)-(d : ℝ)) := by
  obtain ⟨K,hK,hraw⟩ := section9_source_middle_exit_product_moment_upper hd hG green
  refine ⟨K,hK,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ W x hH₁ hH₃ hpos hx L Q₁ Q₃ ν
  let Z := section8ExtensionMiddleCore i n
  let V := section9ExitFace i n
  let f := fun ω : Configuration d => ((sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ Z).card : ℝ)*
    ((sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ V).card : ℝ)
  let U : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ W = {x}}
  let s := (n : ℝ)^((4 : ℝ)-(d : ℝ))
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hU : MeasurableSet U := by
    apply middle_exit_local_measurable (sprinklingAvailableBonds L Q₁ F₁) U
    intro ω θ hagree
    have heq := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hagree x
    simp only [U,Set.mem_setOf_eq,heq]
  have hi : Integrable f ν := (middle_exit_product_integral ν L Q₁ F₁ Z V x).1
  have heq (ω : Configuration d) :
      s*actualUniqueMiddleCount ω L Q₁ F₁ W x Z*
        ((sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ V).card : ℝ) =
        s*U.indicator f ω := by
    by_cases hu : sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ W = {x} <;>
      simp [actualUniqueMiddleCount,Set.indicator_apply,U,f,hu,mul_assoc]
  have hs : 0 ≤ s := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmono : (∫ ω, s*U.indicator f ω ∂ν) ≤ ∫ ω, s*f ω ∂ν := by
    apply integral_mono ((hi.indicator hU).const_mul s) (hi.const_mul s)
    intro ω
    apply mul_le_mul_of_nonneg_left _ hs
    by_cases hu : ω ∈ U
    · simp only [Set.indicator_of_mem hu,le_refl]
    · simp only [Set.indicator_of_notMem hu]
      dsimp [f]
      positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpower : s*(n : ℝ)^5 = (n : ℝ)^((9 : ℝ)-(d : ℝ)) := by
    dsimp [s]
    rw [← Real.rpow_natCast (n : ℝ) 5,← Real.rpow_add hnpos]
    congr 1 <;> norm_num <;> ring
  change (∫ ω, s*actualUniqueMiddleCount ω L Q₁ F₁ W x Z*
    ((sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ V).card : ℝ) ∂ν) ≤ _
  simp_rw [heq]
  calc
    _ ≤ ∫ ω, s*f ω ∂ν := hmono
    _ = s*(∫ ω, f ω ∂ν) := integral_const_mul _ _
    _ ≤ s*(K*(n : ℝ)^5) :=
      mul_le_mul_of_nonneg_left (hraw i n hn H₁ H₃ F₁ F₃ x hH₁ hH₃ hpos hx) hs
    _ = _ := by rw [← mul_assoc,mul_comm s K,mul_assoc,hpower]

end NearCritical
