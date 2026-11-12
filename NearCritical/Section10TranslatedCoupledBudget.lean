module

public import NearCritical.Section10CoupledCubic
public import NearCritical.ConductivityTranslation
public import NearCritical.Section10Conductance

/-! Coupled flow budgets on a TRANSLATED cube (symmetry adapter, translation
half).

The Section 10 construction produces its flow in the box
`U = translateSites aC (centeredBox d r)`. Instead of transporting flows, the
Thomson bound is proved directly in `U` and the annealed conductivity is moved
back by `annealedFull_translation`.

* `translated_negativeFace_coordinate`, `translated_positiveFace_coordinate`:
  the two faces of `U` sit at heights `aC i - r` and `aC i + r + 1`.
* `translated_cube_flow_lower`: a supported unit flow across `U` bounds the
  local conductivity of `U` below.
* `annealed_translated_cube_lower_coupled`: `annealed_cube_lower_coupled` for `U`.
* `translatedCoupledCubeFlowBudget p0 q aC i r a C`: the hypothesis list of
  `coupledCubeFlowBudget` with `centeredBox d r` replaced by `U` in the issued
  bonds, network and faces; same product law, same right-hand side.
* `annealed_cube_cubic_lower_of_translatedBudget`: such a budget gives
  `(a^2/C)(p - p_c)^3 <= annealedFull (centeredBox d r) i p`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

lemma translated_box_bounds {d r : ℕ} (aC : Vertex d) (i : Fin d) :
    ∀ y ∈ translateSites aC (centeredBox d r),
      aC i - (r:ℤ) ≤ y i ∧ y i ≤ aC i + (r:ℤ) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have h := (mem_centeredBox.mp hx) i
  simp only [Pi.add_apply]
  omega

lemma translated_negativeFace_coordinate {d r : ℕ} (aC : Vertex d) (i : Fin d)
    {x : DomainVertex (translateSites aC (centeredBox d r))}
    (hx : x ∈ negativeFace (translateSites aC (centeredBox d r)) i) : x.val i = aC i - (r:ℤ) := by
  have hq : aC + Function.update (0 : Vertex d) i (-(r:ℤ)) ∈ translateSites aC (centeredBox d r) := by
    rw [mem_translateSites]
    apply mem_centeredBox.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      omega
    · simp only [Function.update_of_ne hj, Pi.zero_apply]
      omega
  have hmin := hx.2 _ (base_mem_sitesPlus hq)
  simp only [Pi.add_apply, Function.update_self] at hmin
  have hr := sitesPlus_coordinate_bounds _ i (translated_box_bounds aC i) x.val x.property
  omega

lemma translated_positiveFace_coordinate {d r : ℕ} (aC : Vertex d) (i : Fin d)
    {x : DomainVertex (translateSites aC (centeredBox d r))}
    (hx : x ∈ positiveFace (translateSites aC (centeredBox d r)) i) : x.val i = aC i + (r:ℤ) + 1 := by
  have hq : aC + Function.update (0 : Vertex d) i (r:ℤ) ∈ translateSites aC (centeredBox d r) := by
    rw [mem_translateSites]
    apply mem_centeredBox.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      omega
    · simp only [Function.update_of_ne hj, Pi.zero_apply]
      omega
  have hmax := hx.2 _ (tip_mem_sitesPlus hq i)
  simp only [bondTip, Function.update_self, Pi.add_apply] at hmax
  have hr := sitesPlus_coordinate_bounds _ i (translated_box_bounds aC i) x.val x.property
  omega

theorem translated_cube_flow_lower {d r : ℕ} (aC : Vertex d) (i : Fin d)
    (η : IssuedBond (translateSites aC (centeredBox d r)) → Bool)
    (θ : IssuedBond (translateSites aC (centeredBox d r)) → ℝ)
    (hsupport : Network.FlowSupported (cubeFlowWeights η) θ)
    (hθ : (issuedNetwork (translateSites aC (centeredBox d r))).IsBoundaryUnitFlow
      (negativeFace (translateSites aC (centeredBox d r)) i) (positiveFace (translateSites aC (centeredBox d r)) i) θ) :
    0 < Network.flowEnergy (cubeFlowWeights η) θ ∧
      ((2*(r:ℝ)+1)^2/Network.flowEnergy (cubeFlowWeights η) θ)/(((translateSites aC (centeredBox d r))).card:ℝ) ≤
        localFullConductivity (translateSites aC (centeredBox d r)) i η := by
  have hsource (x : DomainVertex (translateSites aC (centeredBox d r))) (hx : x ∈ negativeFace (translateSites aC (centeredBox d r)) i) :
      coordinateData i x = (aC i : ℝ) - (r:ℝ) := by
    have h := translated_negativeFace_coordinate aC i hx
    change (x.val i:ℝ) = _
    exact_mod_cast h
  have htarget (x : DomainVertex (translateSites aC (centeredBox d r))) (hx : x ∈ positiveFace (translateSites aC (centeredBox d r)) i) :
      coordinateData i x = (aC i : ℝ) - (r:ℝ) + (2*(r:ℝ)+1) := by
    have h := translated_positiveFace_coordinate aC i hx
    have hr : (x.val i:ℝ) = (aC i : ℝ) + (r:ℝ) + 1 := by exact_mod_cast h
    change (x.val i:ℝ) = _
    linarith
  have hw0 : ∀ e, 0 ≤ cubeFlowWeights η e := by
    intro e
    dsimp [cubeFlowWeights]
    split <;> norm_num
  have hb := (issuedNetwork (translateSites aC (centeredBox d r))).conductance_ge_boundary_unit_flow
    (cubeFlowWeights η) θ hw0 hsupport
    (fullBoundary (translateSites aC (centeredBox d r))) (negativeFace (translateSites aC (centeredBox d r)) i) (positiveFace (translateSites aC (centeredBox d r)) i) (coordinateData i)
    (fun _ hx => hx.1) (fun _ hx => hx.1) hθ ((aC i : ℝ) - (r:ℝ)) (2*(r:ℝ)+1)
    (by positivity) hsource htarget
  exact ⟨hb.1, div_le_div_of_nonneg_right hb.2 (Nat.cast_nonneg _)⟩

theorem annealed_translated_cube_lower_coupled {d r : ℕ} (aC : Vertex d) (i : Fin d) (p q : unitInterval)
    (R : Finset (LBond d))
    (orb : (R → Bool) → IssuedBond (translateSites aC (centeredBox d r)) → Bool)
    (horb : ∀ z : Configuration d × Configuration d, orb (R.restrict (layerVal z)) =
      (issuedBondSet (translateSites aC (centeredBox d r))).restrict (sprinkleOrConfiguration z.1 z.2))
    (θ : (R → Bool) → IssuedBond (translateSites aC (centeredBox d r)) → ℝ) (A : Set (R → Bool)) {a K : ℝ}
    (ha : 0 < a) (hK : 0 < K)
    (hflow : ∀ b ∈ A, Network.FlowSupported (cubeFlowWeights (orb b)) (θ b) ∧
      (issuedNetwork (translateSites aC (centeredBox d r))).IsBoundaryUnitFlow
        (negativeFace (translateSites aC (centeredBox d r)) i) (positiveFace (translateSites aC (centeredBox d r)) i) (θ b))
    (hA : a ≤ ∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then (1:ℝ) else 0)
        ∂((percolation d p).prod (percolation d q)))
    (henergy : (∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then
        Network.flowEnergy (cubeFlowWeights (orb (R.restrict (layerVal z))))
          (θ (R.restrict (layerVal z))) else 0)
        ∂((percolation d p).prod (percolation d q))) ≤ K) :
    (((2*(r:ℝ)+1)^2/((translateSites aC (centeredBox d r)).card:ℝ))*a^2)/K ≤
      annealedFull (translateSites aC (centeredBox d r)) i ((orParameter p q : unitInterval) : ℝ) := by
  obtain ⟨μ, hμdef⟩ : ∃ μ : (R → Bool) → ℝ, μ = fun b =>
      ∫ z : Configuration d × Configuration d,
        (if R.restrict (layerVal z) = b then (1:ℝ) else 0)
          ∂((percolation d p).prod (percolation d q)) := ⟨_, rfl⟩
  have hμ0 : ∀ b, 0 ≤ μ b := fun b => by
    rw [hμdef]
    exact integral_nonneg (fun z => by split_ifs <;> norm_num)
  have hcard : 0 < (((translateSites aC (centeredBox d r))).card:ℝ) := by
    rw [card_translateSites]
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨0, mem_centeredBox.mpr ?_⟩
    intro j
    change -(r:ℤ) ≤ 0 ∧ 0 ≤ (r:ℤ)
    omega
  have hs : 0 < (2*(r:ℝ)+1)^2/((translateSites aC (centeredBox d r)).card:ℝ) := by positivity
  have he : ∀ b : R → Bool, 0 ≤ Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) := by
    intro b
    apply Finset.sum_nonneg
    intro e _
    apply div_nonneg (sq_nonneg _)
    dsimp [cubeFlowWeights]
    split <;> norm_num
  have hpoint : ∀ b ∈ A, (2*(r:ℝ)+1)^2/((translateSites aC (centeredBox d r)).card:ℝ) ≤
      localFullConductivity (translateSites aC (centeredBox d r)) i (orb b) *
        Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) := by
    intro b hb
    obtain ⟨hpos, hle⟩ := translated_cube_flow_lower aC i (orb b) (θ b) (hflow b hb).1 (hflow b hb).2
    rw [div_right_comm] at hle
    exact (div_le_iff₀ hpos).mp hle
  have hA' : a ≤ ∑ b, if b ∈ A then μ b else 0 := by
    have h := integral_bits_eq_sum p q R (fun b => if b ∈ A then (1:ℝ) else 0)
    rw [h] at hA
    refine hA.trans (le_of_eq (Finset.sum_congr rfl (fun b _ => ?_)))
    rw [hμdef]
    simp only [mul_ite, mul_one, mul_zero]
  have henergy' : (∑ b, if b ∈ A then
      μ b * Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) else 0) ≤ K := by
    have h := integral_bits_eq_sum p q R (fun b => if b ∈ A then
      Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) else 0)
    rw [h] at henergy
    refine (le_of_eq (Finset.sum_congr rfl (fun b _ => ?_))).trans henergy
    rw [hμdef]
    simp only [mul_ite, mul_zero]
  have hb := mean_conductivity_lower_of_energy_bound μ
    (fun b => localFullConductivity (translateSites aC (centeredBox d r)) i (orb b))
    (fun b => Network.flowEnergy (cubeFlowWeights (orb b)) (θ b)) A hμ0
    (fun b => localFullConductivity_nonneg (translateSites aC (centeredBox d r)) i (orb b)) he hs ha hK hpoint hA'
    henergy'
  have hmean : (∑ b, μ b * localFullConductivity (translateSites aC (centeredBox d r)) i (orb b)) =
      annealedFull (translateSites aC (centeredBox d r)) i ((orParameter p q : unitInterval) : ℝ) := by
    have h := integral_bits_eq_sum p q R
      (fun b => localFullConductivity (translateSites aC (centeredBox d r)) i (orb b))
    rw [hμdef]
    rw [← h]
    simp only [horb]
    have hmap := percolation_sprinkleOr_map d p q
    rw [annealedFull, ← percolation_cylinder_expectation d (orParameter p q)
      (issuedBondSet (translateSites aC (centeredBox d r))) (localFullConductivity (translateSites aC (centeredBox d r)) i), ← hmap]
    have hmeas : Measurable (fun ω : Configuration d =>
        localFullConductivity (translateSites aC (centeredBox d r)) i
          ((issuedBondSet (translateSites aC (centeredBox d r))).restrict ω)) :=
      (measurable_of_finite (localFullConductivity (translateSites aC (centeredBox d r)) i)).comp
        (Finset.measurable_restrict (issuedBondSet (translateSites aC (centeredBox d r))))
    exact (integral_map measurable_sprinkleOrConfiguration.aemeasurable
      hmeas.aestronglyMeasurable).symm
  rw [hmean] at hb
  exact hb

/-- Flow budget on the coupled law for the translated cube. -/
def translatedCoupledCubeFlowBudget {d : ℕ} (p0 q : unitInterval) (aC : Vertex d) (i : Fin d)
    (r : ℕ) (a C : ℝ) : Prop :=
  ∃ (R : Finset (LBond d))
    (orb : (R → Bool) → IssuedBond (translateSites aC (centeredBox d r)) → Bool)
    (θ : (R → Bool) → IssuedBond (translateSites aC (centeredBox d r)) → ℝ) (A : Set (R → Bool)),
    (∀ z : Configuration d × Configuration d, orb (R.restrict (layerVal z)) =
      (issuedBondSet (translateSites aC (centeredBox d r))).restrict (sprinkleOrConfiguration z.1 z.2)) ∧
    (∀ b ∈ A, Network.FlowSupported (cubeFlowWeights (orb b)) (θ b) ∧
      (issuedNetwork (translateSites aC (centeredBox d r))).IsBoundaryUnitFlow
        (negativeFace (translateSites aC (centeredBox d r)) i) (positiveFace (translateSites aC (centeredBox d r)) i) (θ b)) ∧
    a ≤ (∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then (1:ℝ) else 0)
        ∂((percolation d p0).prod (percolation d q))) ∧
    (∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then
        Network.flowEnergy (cubeFlowWeights (orb (R.restrict (layerVal z))))
          (θ (R.restrict (layerVal z))) else 0)
        ∂((percolation d p0).prod (percolation d q))) ≤
      C * cubeFlowNormalization d r *
        (chemicalCorrelationScale d (orParameter p0 q) : ℝ) ^ 6

theorem annealed_cube_cubic_lower_of_translatedBudget {d : ℕ} (p0 q : unitInterval)
    (aC : Vertex d) (i : Fin d)
    (hp : criticalPoint d < orParameter p0 q) (r : ℕ) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hbudget : translatedCoupledCubeFlowBudget p0 q aC i r a C) :
    (a^2/C) * (((orParameter p0 q : unitInterval) : ℝ) - (criticalPoint d : ℝ))^3 ≤
      annealedFull (centeredBox d r) i ((orParameter p0 q : unitInterval) : ℝ) := by
  obtain ⟨R, orb, θ, A, horb, hflow, hA, henergy⟩ := hbudget
  have hs := cubeFlowNormalization_pos d r
  have hstar : 0 < (chemicalCorrelationScale d (orParameter p0 q) : ℝ) := by
    exact_mod_cast (show 0 < chemicalCorrelationScale d (orParameter p0 q) by
      have h := chemicalCorrelationScale_pos (orParameter p0 q) hp
      omega)
  have hK : 0 < C * cubeFlowNormalization d r *
      (chemicalCorrelationScale d (orParameter p0 q) : ℝ) ^ 6 := by positivity
  have hb := annealed_translated_cube_lower_coupled aC i p0 q R orb horb θ A ha hK hflow hA henergy
  rw [card_translateSites, annealedFull_translation] at hb
  have hinv : a^2/(C * (chemicalCorrelationScale d (orParameter p0 q) : ℝ)^6) ≤
      annealedFull (centeredBox d r) i ((orParameter p0 q : unitInterval) : ℝ) := by
    calc a^2/(C * (chemicalCorrelationScale d (orParameter p0 q) : ℝ)^6)
        = (cubeFlowNormalization d r * a^2) /
          (C * cubeFlowNormalization d r *
            (chemicalCorrelationScale d (orParameter p0 q) : ℝ)^6) := by
          field_simp [hC.ne', hs.ne', hstar.ne']
      _ ≤ _ := hb
  apply cubic_lower_of_inverse_scale_bound (orParameter p0 q) hp (div_nonneg (sq_nonneg _) hC.le)
  simpa only [div_div] using hinv

end NearCritical.Section10
