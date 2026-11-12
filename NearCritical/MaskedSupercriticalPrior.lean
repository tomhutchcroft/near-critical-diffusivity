module
public import NearCritical.BulkSupercriticalBound
public import NearCritical.WaterCubeAuxiliaryPrior

/-! NEW supercritical masked conductivity prior. Only the sampling law is
masked; the conductivity energy keeps ALL issued bonds. Both source arm
orientations are retained and dominated under a genuine homogeneous law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Finset

lemma latticeBoundaryConnectionEvent_increasing {d : ℕ} (U : Finset (Vertex d))
    (x : DomainVertex U) (A : Set (DomainVertex U)) :
    BK.Increasing (latticeBoundaryConnectionEvent U x A) := by
  intro ω η h hω
  exact ((issuedNetwork U).boundaryConnectionEvent_increasing x A)
    (fun e he => h e.val he) hω

lemma sourceTwoArm_increasing {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (e : IssuedBond U) : BK.Increasing {ω | sourceTwoArm U i ω e} := by
  intro ω η h hω
  rcases hω with hω | hω
  · exact Or.inl (increasing_disjointOccurrence
      (latticeBoundaryConnectionEvent_increasing U _ _)
      (latticeBoundaryConnectionEvent_increasing U _ _) h hω)
  · exact Or.inr (increasing_disjointOccurrence
      (latticeBoundaryConnectionEvent_increasing U _ _)
      (latticeBoundaryConnectionEvent_increasing U _ _) h hω)

/-- Actual masked law comparison followed by genuine homogeneous BK. -/
theorem masked_sourceTwoArm_le_connectionProducts {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (M : Finset (IssuedBond U)) (p s P0 : unitInterval)
    (hp : (p:ℝ) ≤ (P0:ℝ)) (hs : (s:ℝ) ≤ (P0:ℝ)) (e : IssuedBond U) :
    (maskedPercolation d (M.image Subtype.val) p s).real {ω | sourceTwoArm U i ω e} ≤
      boundaryConnectionProducts U i P0 e := by
  exact (maskedPercolation_event_real_le_homogeneous _ p s P0 hp hs
    (measurableSet_sourceTwoArm U i e) (sourceTwoArm_increasing U i e)).trans
      (sourceTwoArm_probability_le U i P0 e)

/-- The source a-delta sum runs over ALL issued bonds, even outside M. -/
theorem annealedMaskedRelaxed_le_homogeneous_connectionProducts {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (M : Finset (IssuedBond U))
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p s P0 : unitInterval) (hp : (p:ℝ) ≤ (P0:ℝ)) (hs : (s:ℝ) ≤ (P0:ℝ)) :
    annealedMaskedRelaxed U i M (p:ℝ) (s:ℝ) ≤
      ((coordinateData i h-coordinateData i l)^2/(U.card:ℝ))*
        ∑ e : IssuedBond U, boundaryConnectionProducts U i P0 e := by
  exact (annealedMaskedRelaxed_le_sourceTwoArm_probabilities U i M hl hh p s).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum (fun e _ =>
      masked_sourceTwoArm_le_connectionProducts U i M p s P0 hp hs e))
        (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))

/-- Conditional completion of the issued-edge summation in eq.aa_bound_step2.
The harmless `1 + log h` retains the degenerate h=1 cube explicitly. -/
theorem annealedMaskedRelaxed_waterCube_le_of_productEnvelope {d : ℕ} (i : Fin d)
    (r R : ℕ) {l h : DomainVertex (waterCube d i r R)}
    (hl : l ∈ negativeFace (waterCube d i r R) i)
    (hh : h ∈ positiveFace (waterCube d i r R) i)
    (M : Finset (IssuedBond (waterCube d i r R))) (p s P0 : unitInterval)
    (hp : (p:ℝ) ≤ (P0:ℝ)) (hs : (s:ℝ) ≤ (P0:ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (henv : WaterCubeConnectionProductEnvelope i r R P0 C) :
    annealedMaskedRelaxed (waterCube d i r R) i M (p:ℝ) (s:ℝ) ≤
      2 * (d : ℝ) * C * (1 + Real.log (2 * r + 1 : ℕ)) /
        (2 * (r : ℝ) + 1) ^ 2 := by
  have hlayers := sum_issued_waterCube_inverse_depth_le i r R
  have hsum : (∑ e : IssuedBond (waterCube d i r R),
      boundaryConnectionProducts (waterCube d i r R) i P0 e) ≤
      (C / (2 * (r : ℝ) + 1) ^ 3) *
        (2 * (d : ℝ) * ((2 * R + 1) ^ (d - 1) : ℕ) *
          (1 + Real.log (2 * r + 1 : ℕ))) := by
    calc
      _ ≤ ∑ e : IssuedBond (waterCube d i r R),
          (C / (2 * (r : ℝ) + 1) ^ 3) *
            (1 / (waterCubeBaseDepth i r e.val.1 + 1 : ℝ)) :=
        sum_le_sum fun e _ => henv e
      _ = _ := by rw [← mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlayers (div_nonneg hC (by positivity))
  have hr : (0 : ℝ) < 2 * (r : ℝ) + 1 := by positivity
  have hM : (0 : ℝ) < ((2 * R + 1) ^ (d - 1) : ℕ) := by positivity
  calc
    _ ≤ ((coordinateData i h - coordinateData i l) ^ 2 /
        ((waterCube d i r R).card : ℝ)) *
        ∑ e : IssuedBond (waterCube d i r R),
          boundaryConnectionProducts (waterCube d i r R) i P0 e :=
      annealedMaskedRelaxed_le_homogeneous_connectionProducts _ i M hl hh p s P0 hp hs
    _ ≤ ((coordinateData i h - coordinateData i l) ^ 2 /
        ((waterCube d i r R).card : ℝ)) *
        ((C / (2 * (r : ℝ) + 1) ^ 3) *
          (2 * (d : ℝ) * ((2 * R + 1) ^ (d - 1) : ℕ) *
            (1 + Real.log (2 * r + 1 : ℕ)))) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      rw [waterCube_face_height d i r R hl hh, card_waterCube]
      push_cast
      field_simp

/-- NEW masked prior with the homogeneous product envelope DISCHARGED from
named STANDARD inputs. ONE amplitude precedes every mask, scale and parameter.
The max endpoint is supercritical because the exterior p is supercritical.
This includes the source bulk mask, and retains the full conductivity sum. -/
theorem maskedRelaxed_supercritical_prior_of_standard_inputs {d : ℕ} (i : Fin d)
    {C E A B b : ℝ} (hC : 1 ≤ C) (hE : 0 < E) (hA : 0 < A)
    (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d:ℝ)) (hpc1 : (criticalPoint d:ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p s : unitInterval) (r R : ℕ)
      (M : Finset (IssuedBond (waterCube d i r R))), 1 ≤ r →
      (criticalPoint d:ℝ) < (p:ℝ) →
      (p:ℝ) ≤ (criticalPoint d:ℝ)+(((2*r+1:ℕ):ℝ)^2)⁻¹ →
      (s:ℝ) ≤ (criticalPoint d:ℝ)+(((2*r+1:ℕ):ℝ)^2)⁻¹ →
      annealedMaskedRelaxed (waterCube d i r R) i M (p:ℝ) (s:ℝ) ≤
        2*(d:ℝ)*K*Real.log (2*r+1:ℕ)/(2*(r:ℝ)+1)^2 := by
  obtain ⟨M0,hM0,hprior⟩ := waterCube_supercritical_prior_of_standard_inputs i hC
    hE hA hB hb hpc hpc1 ordinary criticalArm pioneers entropic
  let K := M0*(1+1/Real.log 3)
  have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro p s r R M hr hp hwp hws
  let P0 := max p s
  have hpP0 : (p:ℝ) ≤ (P0:ℝ) := le_max_left _ _
  have hsP0 : (s:ℝ) ≤ (P0:ℝ) := le_max_right _ _
  have hP0 : (criticalPoint d:ℝ) < (P0:ℝ) := hp.trans_le hpP0
  have hwP0 : (P0:ℝ) ≤ (criticalPoint d:ℝ)+(((2*r+1:ℕ):ℝ)^2)⁻¹ := by
    change max (p:ℝ) (s:ℝ) ≤ _
    exact max_le hwp hws
  obtain ⟨l,hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h,hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  exact (annealedMaskedRelaxed_waterCube_le_of_productEnvelope i r R hl hh M p s P0
    hpP0 hsP0 hM0.le (hprior P0 r R hP0 hwP0).1).trans
      (waterCube_prior_prefactor_le_log d r hr hM0.le)

end NearCritical
