module

public import NearCritical.WaterCubeBulkBandGeometry
public import NearCritical.WaterCubeOrdinaryArms
public import NearCritical.BulkSupercriticalBound

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

private theorem reachable_of_unique_first_step {V : Type*} {G : SimpleGraph V}
    {head tail y : V} (hy : head ≠ y)
    (hstep : ∀ v, G.Adj head v → v = tail) (h : G.Reachable head y) :
    G.Reachable tail y := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => exact (hy rfl).elim
  | @cons _ v _ h w => exact ⟨(hstep v h) ▸ w⟩

/-- An issued exterior head can reach a target avoiding it only by first
returning along its unique issued bond to the base tail. -/
theorem rectangularBox_exterior_head_connection_subset {d : ℕ} (ρ : Fin d → ℕ)
    (e : IssuedBond (rectangularBox ρ)) (A : Set (DomainVertex (rectangularBox ρ)))
    (he : bondTip e.val ∉ rectangularBox ρ)
    (hA : (issuedNetwork (rectangularBox ρ)).head e ∉ A) :
    latticeBoundaryConnectionEvent (rectangularBox ρ)
        ((issuedNetwork (rectangularBox ρ)).head e) A ⊆
      latticeBoundaryConnectionEvent (rectangularBox ρ)
        ((issuedNetwork (rectangularBox ρ)).tail e) A := by
  let U := rectangularBox ρ
  let G := issuedNetwork U
  intro ω hω
  obtain ⟨y, hy, hreach⟩ := hω
  refine ⟨y, hy, reachable_of_unique_first_step (fun h => hA (by rwa [h])) ?_ hreach⟩
  intro v hv
  obtain ⟨_, _, _, f, _, hends⟩ := hv
  rcases hends with ⟨hhead, _⟩ | ⟨htail, hhead⟩
  · have hfU : (G.tail f).val ∈ U := (Finset.mem_product.mp f.property).1
    have htip : (G.tail f).val = bondTip e.val := congrArg Subtype.val hhead
    exact (he (htip ▸ hfU)).elim
  · have htip : bondTip e.val = bondTip f.val :=
      (congrArg Subtype.val hhead).symm
    have hef := rectangularBox_issued_tip_outside_unique ρ e f he htip
    subst f
    exact htail.symm

/-- The ordinary near-face bound under the actual masked law. The source may
be an exterior head, and the target depth may be zero. -/
theorem maskedWaterCube_face_probability_le_ordinary {d : ℕ} {Co : ℝ}
    (ordinary : OrdinaryArmWindowInput d Co) (p q : unitInterval) (hqp : q ≤ p)
    (i : Fin d) (r R : ℕ) (δ : ℝ) (upper : Bool)
    (x : DomainVertex (waterCube d i r R))
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ)+(((2*r+1 : ℕ) : ℝ)^2)⁻¹) :
    (bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).real
      (waterCubeFaceConnectionEvent i r R upper x) ≤
      4*max 1 Co/(waterCubeTargetDepth i r upper x.val+1 : ℝ)^2 := by
  let U := waterCube d i r R
  let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
  let D := waterCubeTargetDepth i r upper x.val
  let C := max 1 Co
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (percolationProfile d _)
    infer_instance
  change μ.real (waterCubeFaceConnectionEvent i r R upper x) ≤ 4*C/(D+1 : ℝ)^2
  by_cases hD : D=0
  · have hsmall : μ.real (waterCubeFaceConnectionEvent i r R upper x) ≤ 1 :=
      measureReal_le_one
    exact hsmall.trans (by rw [hD]; simp only [Nat.cast_zero, zero_add, one_pow, div_one]; linarith)
  · have hDp : 0 < (D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD
    have hD1 : 1 ≤ D := by omega
    have hDH : (D : ℝ) ≤ ((2*r+1 : ℕ) : ℝ) := by
      exact_mod_cast waterCube_targetDepth_le_height i r R upper x
    have hpD : (p : ℝ) ≤ (criticalPoint d : ℝ)+((D : ℝ)^2)⁻¹ := by
      have hi : (((2*r+1 : ℕ) : ℝ)^2)⁻¹ ≤ ((D : ℝ)^2)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hDp)
          ((sq_le_sq₀ hDp.le (hDp.le.trans hDH)).mpr hDH)
      exact hp.trans (add_le_add_right hi _)
    let E := extrinsicRadiusArmEvent x.val ((D : ℝ)/2)
    have hsub : waterCubeFaceConnectionEvent i r R upper x ⊆ E :=
      waterCube_face_subset_extrinsicArm i r R upper x
        (by change (D : ℝ)/2 < D; linarith)
    have hdom : μ.real E ≤ (percolation d p).real E := by
      change (bulkPercolation U i (2*(r : ℝ)+1) δ p q).real E ≤ _
      rw [bulkPercolation_eq_masked]
      exact maskedPercolation_event_real_le_homogeneous _ p q p le_rfl hqp
        (measurableSet_extrinsicRadiusArmEvent _ _) (extrinsicRadiusArmEvent_increasing _ _)
    calc
      _ ≤ μ.real E := measureReal_mono hsub (measure_ne_top μ E)
      _ ≤ (percolation d p).real E := hdom
      _ ≤ Co/(D : ℝ)^2 := ordinary p x.val D hD1 hpD
      _ ≤ C/(D : ℝ)^2 := div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
      _ ≤ _ := by
        have hD1R : 1 ≤ (D : ℝ) := by exact_mod_cast hD1
        have hsq : ((D : ℝ)+1)^2 ≤ 4*(D : ℝ)^2 := by nlinarith
        apply (div_le_div_iff₀ (sq_pos_of_pos hDp) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hsq hC₀]

end NearCritical
