module

public import NearCritical.BulkProbabilityReduction
public import NearCritical.BulkArmGeometry
public import NearCritical.PercolationMonotonicity

/-! The NEW no-log supercritical bulk-auxiliary bound. The only arm estimate
is an explicit standard ordinary-arm input. Actual product-profile domination
is proved by bounded reuse of the existing Bernoulli thinning construction;
BK is applied only under the homogeneous actual law. No subcritical gain. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset MeasureTheory ProbabilityTheory
open scoped Classical

/-- Coordinate-dependent retention, reusing the scalar AND law. -/
lemma finite_profile_thin_map {E : Type*} [Fintype E] (p : unitInterval)
    (q r : E → unitInterval) (hr : ∀ e, (r e : ℝ) = (p : ℝ) * (q e : ℝ)) :
    ((Measure.pi fun _ : E ↦ bernoulliMeasure true false p).prod
      (Measure.pi fun e : E ↦ bernoulliMeasure true false (q e))).map thinConfiguration =
        Measure.pi fun e : E ↦ bernoulliMeasure true false (r e) := by
  let equiv := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool E
  have he := (measurePreserving_arrowProdEquivProdArrow Bool Bool E
    (fun _ ↦ bernoulliMeasure true false p) (fun e ↦ bernoulliMeasure true false (q e))).map_eq
  rw [← he, Measure.map_map measurable_thinConfiguration equiv.measurable]
  change (Measure.pi fun e : E ↦ (bernoulliMeasure true false p).prod
    (bernoulliMeasure true false (q e))).map
      (fun z e ↦ (z e).1 && (z e).2) = _
  rw [Measure.pi_map_pi (f := fun _ (z : Bool × Bool) ↦ z.1 && z.2)
    (fun _ ↦ (measurable_of_finite _).aemeasurable)]
  congr 1
  funext e
  exact bernoulli_and_map p (q e) (r e) (hr e)

/-- Exact profile thinning of a homogeneous sample, including the FULL law. -/
lemma percolationProfile_thin_map (d : ℕ) (p : unitInterval)
    (q r : Bond d → unitInterval) (hr : ∀ e, (r e : ℝ) = (p : ℝ) * (q e : ℝ)) :
    ((percolation d p).prod (percolationProfile d q)).map thinConfiguration =
      percolationProfile d r := by
  refine (Measure.isProjectiveLimit_infinitePi
    (fun e : Bond d ↦ bernoulliMeasure true false (r e))).unique ?_ |>.symm
  intro s
  have hsmeas : Measurable (s.restrict : Configuration d → (s → Bool)) :=
    measurable_pi_iff.mpr (fun e ↦ measurable_pi_apply (e : Bond d))
  have hprod : ((percolation d p).prod (percolationProfile d q)).map
      (Prod.map s.restrict s.restrict) =
      (Measure.pi fun _ : s ↦ bernoulliMeasure true false p).prod
        (Measure.pi fun e : s ↦ bernoulliMeasure true false (q e.val)) := by
    rw [← Measure.map_prod_map _ _ hsmeas hsmeas]
    simp only [percolation, percolationProfile, Measure.infinitePi_map_restrict]
  rw [Measure.map_map hsmeas measurable_thinConfiguration]
  calc
    _ = (((percolation d p).prod (percolationProfile d q)).map
        (Prod.map s.restrict s.restrict)).map thinConfiguration := by
      rw [Measure.map_map measurable_thinConfiguration (hsmeas.prodMap hsmeas)]
      rfl
    _ = _ := by
      rw [hprod, finite_profile_thin_map p (fun e : s ↦ q e.val)
        (fun e : s ↦ r e.val) (fun e ↦ hr e.val)]

/-- Actual independent-profile domination, with no domination assumption. -/
theorem percolationProfile_event_le_homogeneous {d : ℕ}
    (r : Bond d → unitInterval) (P0 : unitInterval) (hr : ∀ e, (r e : ℝ) ≤ (P0 : ℝ))
    {A : Set (Configuration d)} (hA : MeasurableSet A) (hinc : BK.Increasing A) :
    percolationProfile d r A ≤ percolation d P0 A := by
  by_cases hP0 : (P0 : ℝ) = 0
  · have heq : r = fun _ ↦ P0 := by
      funext e
      apply Subtype.ext
      exact le_antisymm (hr e) (by simpa [hP0] using (r e).property.1)
    rw [heq, percolationProfile_const]
  · have hpos : 0 < (P0 : ℝ) := lt_of_le_of_ne P0.property.1 (Ne.symm hP0)
    let q : Bond d → unitInterval := fun e ↦
      ⟨(r e : ℝ) / (P0 : ℝ), div_nonneg (r e).property.1 P0.property.1,
        (div_le_one hpos).mpr (hr e)⟩
    have hq : ∀ e, (r e : ℝ) = (P0 : ℝ) * (q e : ℝ) := by
      intro e
      dsimp [q]
      field_simp
    rw [← percolationProfile_thin_map d P0 q r hq,
      Measure.map_apply measurable_thinConfiguration hA]
    calc
      _ ≤ ((percolation d P0).prod (percolationProfile d q)) (A ×ˢ Set.univ) := by
        apply measure_mono
        intro z hz
        exact ⟨hinc (thinConfiguration_le_left z) hz, Set.mem_univ _⟩
      _ = _ := by rw [Measure.prod_prod]; simp

lemma maskedPercolation_event_real_le_homogeneous {d : ℕ} (B : Finset (Bond d))
    (p s P0 : unitInterval) (hp : (p : ℝ) ≤ (P0 : ℝ)) (hs : (s : ℝ) ≤ (P0 : ℝ))
    {A : Set (Configuration d)} (hA : MeasurableSet A) (hinc : BK.Increasing A) :
    (maskedPercolation d B p s).real A ≤ (percolation d P0).real A := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply percolationProfile_event_le_homogeneous _ P0 _ hA hinc
  intro e
  split <;> assumption

/-- Increasingness of finite-forcing occurrence follows from its open
certificates, not from a hypothesis about a probability inequality. -/
lemma increasing_disjointOccurrence {E : Type*} {A B : Set (E → Bool)}
    (hA : BK.Increasing A) (hB : BK.Increasing B) :
    BK.Increasing {ω | DisjointOccurrence A B ω} := by
  intro ω η h hω
  obtain ⟨F, H, hFfin, hHfin, hdis, hF, hH, hAF, hBH⟩ :=
    BK.openDisjointOccurrence_of_disjointOccurrence hω
  exact BK.OpenDisjointOccurrence.to_disjointOccurrence
    ⟨F, H, hFfin, hHfin, hdis, (fun e he ↦ h e (hF e he)),
      (fun e he ↦ h e (hH e he)), hAF, hBH⟩ hA hB

/-- There are d issued bonds per base vertex; any mask has at most this size. -/
lemma card_issuedBondMask_le {d : ℕ} (U : Finset (Vertex d)) (M : Finset (IssuedBond U)) :
    M.card ≤ d * U.card := by
  calc
    M.card ≤ Fintype.card (IssuedBond U) := Finset.card_le_univ M
    _ = (issuedBondSet U).card := Fintype.card_coe (issuedBondSet U)
    _ = d * U.card := by
      change (U.product (Finset.univ : Finset (Fin d))).card = d * U.card
      rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_comm _ _

/-- Each actual inhomogeneous bulk two-arm probability is controlled by two
STANDARD homogeneous ordinary-arm bounds. No inhomogeneous BK is used. -/
theorem bulk_twoArm_probability_le_of_ordinaryArms {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (height δ : ℝ)
    (e : IssuedBond U) (he : e ∈ bulkBondMask U i height δ)
    (p s P0 : unitInterval) (hp : (p : ℝ) ≤ (P0 : ℝ)) (hs : (s : ℝ) ≤ (P0 : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hArm : ∀ x : Vertex d, (percolation d P0).real
      (extrinsicRadiusArmEvent x (δ * height / 2)) ≤ C / height^2) :
    (bulkPercolation U i height δ p s).real {ω | sourceTwoArm U i ω e} ≤
      (C / height^2)^2 := by
  let A := extrinsicRadiusArmEvent ((issuedNetwork U).tail e).val (δ * height / 2)
  let B := extrinsicRadiusArmEvent ((issuedNetwork U).head e).val (δ * height / 2)
  have hA : BK.Increasing A := extrinsicRadiusArmEvent_increasing _ _
  have hB : BK.Increasing B := extrinsicRadiusArmEvent_increasing _ _
  rw [bulkPercolation_eq_masked]
  have : IsProbabilityMeasure
      (maskedPercolation d ((bulkBondMask U i height δ).image Subtype.val) p s) := by
    unfold maskedPercolation
    infer_instance
  calc
    _ ≤ (maskedPercolation d ((bulkBondMask U i height δ).image Subtype.val) p s).real
        {ω | DisjointOccurrence A B ω} :=
      measureReal_mono (sourceTwoArm_bulk_subset_disjoint_extrinsicArms U i height δ e he)
    _ ≤ (percolation d P0).real {ω | DisjointOccurrence A B ω} :=
      maskedPercolation_event_real_le_homogeneous _ p s P0 hp hs
        (measurableSet_disjointOccurrence hA hB) (increasing_disjointOccurrence hA hB)
    _ ≤ (percolation d P0).real A * (percolation d P0).real B :=
      percolation_bk d P0 A B hA hB
    _ ≤ (C / height^2) * (C / height^2) :=
      mul_le_mul (hArm _) (hArm _) measureReal_nonneg (div_nonneg hC (sq_nonneg _))
    _ = _ := by ring

/-- NEW supercritical branch of lem.aabb_bound_new, with a coarser delta
constant absorbed into the explicit STANDARD ordinary-arm input C.
The actual no-log bound follows from M.card<=d*|U|, not a presumed layer sum. -/
theorem waterCube_annealedBulkB_supercritical_bound
    (d : ℕ) (i : Fin d) (r R : ℕ) (δ : ℝ) (p s P0 : unitInterval)
    (hp : (p : ℝ) ≤ (P0 : ℝ)) (hs : (s : ℝ) ≤ (P0 : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hArm : ∀ x : Vertex d, (percolation d P0).real
      (extrinsicRadiusArmEvent x (δ * (2*(r:ℝ)+1) / 2)) ≤ C / (2*(r:ℝ)+1)^2) :
    annealedMaskedB (waterCube d i r R) i
      (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) (p : ℝ) (s : ℝ) ≤
      (d : ℝ) * C^2 / (2*(r:ℝ)+1)^2 := by
  let U := waterCube d i r R
  let height : ℝ := 2*(r:ℝ)+1
  let M := bulkBondMask U i height δ
  have hheight : 0 < height := by dsimp [height]; positivity
  have hvol : 0 < (U.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (waterCube_nonempty d i r R)
  obtain ⟨l, hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h, hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  have hb := annealedBulkB_le_sourceTwoArm_probabilities U i height δ hl hh p s
  rw [waterCube_face_height d i r R hl hh] at hb
  have hsum : (∑ e ∈ M, (bulkPercolation U i height δ p s).real
      {ω | sourceTwoArm U i ω e}) ≤ (M.card : ℝ) * (C / height^2)^2 := by
    calc
      _ ≤ ∑ _e ∈ M, (C / height^2)^2 := by
        apply sum_le_sum
        intro e he
        exact bulk_twoArm_probability_le_of_ordinaryArms U i height δ e he p s P0 hp hs C hC hArm
      _ = _ := by simp
  have hm : (M.card : ℝ) ≤ (d : ℝ) * (U.card : ℝ) := by
    exact_mod_cast card_issuedBondMask_le U M
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hm (sq_nonneg (C / height^2)))
  calc
    _ ≤ height^2 / (U.card : ℝ) * (∑ e ∈ M, (bulkPercolation U i height δ p s).real
        {ω | sourceTwoArm U i ω e}) := hb
    _ ≤ height^2 / (U.card : ℝ) * (((d : ℝ) * (U.card : ℝ)) * (C / height^2)^2) :=
      mul_le_mul_of_nonneg_left hsum' (div_nonneg (sq_nonneg _) hvol.le)
    _ = _ := by
      change height^2 / (U.card : ℝ) * (((d : ℝ) * (U.card : ℝ)) * (C / height^2)^2) =
        (d : ℝ) * C^2 / height^2
      field_simp [ne_of_gt hheight, ne_of_gt hvol]

/-- Literal source b-delta integral under its original inhomogeneous law. -/
theorem waterCube_sourceBulkB_supercritical_bound
    (d : ℕ) (i : Fin d) (r R : ℕ) (δ : ℝ) (p s P0 : unitInterval)
    (hp : (p : ℝ) ≤ (P0 : ℝ)) (hs : (s : ℝ) ≤ (P0 : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hArm : ∀ x : Vertex d, (percolation d P0).real
      (extrinsicRadiusArmEvent x (δ * (2*(r:ℝ)+1) / 2)) ≤ C / (2*(r:ℝ)+1)^2) :
    (∫ ω, sourceMaskedQuenchedB (waterCube d i r R) i
      (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) ω
        ∂bulkPercolation (waterCube d i r R) i (2*(r:ℝ)+1) δ p s) ≤
      (d : ℝ) * C^2 / (2*(r:ℝ)+1)^2 := by
  rw [← annealedBulkB_eq_sourceIntegral]
  exact waterCube_annealedBulkB_supercritical_bound d i r R δ p s P0 hp hs C hC hArm

end NearCritical
