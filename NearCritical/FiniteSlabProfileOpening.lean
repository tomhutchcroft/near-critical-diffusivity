module

public import NearCritical.FiniteSlabDifferential
public import NearCritical.FiniteProfilePivotalAvoidance
public import NearCritical.ProfileCountableBKStrict

/-! Actual finite-slab opening bounds for independent coordinate profiles.
The old tested bond is closed and the two finite forcing certificates avoid
it, before Mecke cancellation and profile BK. Both orientations are kept. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset BernoulliCalculus MeasureTheory ProbabilityTheory
open scoped Classical

/-- The actual finite-cutoff connection probability under the full profile
law equals the literal restricted-profile finite expectation. -/
lemma finiteSlabConnectionEvent_profile_probability {d : ℕ}
    (r : Bond d → unitInterval) (U : Finset (Vertex d)) (i : Fin d)
    (m n : ℤ) (x y : Vertex d) :
    (percolationProfile d r).real (finiteSlabConnectionEvent U i m n x y) =
      BK.profileEventProbability (fun e : internalBondSet U ↦ (r e.val : ℝ))
        (finiteSlabLocalConnectionEvent U i m n x y) := by
  rw [finiteSlabConnectionEvent_eq_preimage]
  exact (profileEventProbability_cylinder d r (internalBondSet U)
    (finiteSlabLocalConnectionEvent U i m n x y)).symm

private lemma finiteSlab_profile_opening_indicator_le {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) (e : internalBondSet U)
    (η : (j : internalBondSet U) → Bool) :
    (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y then (1 : ℝ) else 0) -
      (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0) ≤
    (if η e then 0 else 1) * (if AvoidingDisjointOccurrence e
      (finiteSlabLocalConnectionEvent U i m n x e.val.1)
      (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y) η then 1 else 0) +
    (if η e then 0 else 1) * (if AvoidingDisjointOccurrence e
      (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
      (finiteSlabLocalConnectionEvent U i m n e.val.1 y) η then 1 else 0) := by
  let g1 : ℝ := (if η e then 0 else 1) * (if AvoidingDisjointOccurrence e
    (finiteSlabLocalConnectionEvent U i m n x e.val.1)
    (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y) η then 1 else 0)
  let g2 : ℝ := (if η e then 0 else 1) * (if AvoidingDisjointOccurrence e
    (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
    (finiteSlabLocalConnectionEvent U i m n e.val.1 y) η then 1 else 0)
  change _ ≤ g1 + g2
  have hg1 : 0 ≤ g1 := by dsimp [g1]; split_ifs <;> norm_num
  have hg2 : 0 ≤ g2 := by dsimp [g2]; split_ifs <;> norm_num
  by_cases hnew : forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y
  · by_cases hold : η ∈ finiteSlabLocalConnectionEvent U i m n x y
    · simp only [ite_eq_left hnew, ite_eq_left hold, sub_self]
      exact add_nonneg hg1 hg2
    · obtain ⟨hclosed, hav⟩ := finiteSlab_local_opening_avoiding_support U i m n x y e η hnew hold
      rcases hav with ha | hb
      · have heq : g1 = 1 := by simp [g1, hclosed, ha]
        rw [ite_eq_left hnew, ite_eq_right hold, heq]
        linarith
      · have heq : g2 = 1 := by simp [g2, hclosed, hb]
        rw [ite_eq_left hnew, ite_eq_right hold, heq]
        linarith
  · by_cases hold : η ∈ finiteSlabLocalConnectionEvent U i m n x y
    · simp only [ite_eq_right hnew, ite_eq_left hold]
      linarith
    · simp only [ite_eq_right hnew, ite_eq_right hold, sub_self]
      exact add_nonneg hg1 hg2

/-- Per-connection Russo opening contribution under the actual independent
profile. The common P<1 bound allows both zero rates and different phases. -/
theorem finiteSlab_profile_opening_expectation_le {d : ℕ}
    (r : Bond d → unitInterval) (P : unitInterval) (hP : (P : ℝ) < 1)
    (hr : ∀ b, r b ≤ P) (U : Finset (Vertex d)) (i : Fin d)
    (m n : ℤ) (x y : Vertex d) (e : internalBondSet U) :
    (1-(r e.val : ℝ))⁻¹ * finiteExpectationProfile
      (fun f : internalBondSet U ↦ (r f.val : ℝ)) (fun η ↦
        (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y then (1 : ℝ) else 0) -
          (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0)) ≤
      (percolationProfile d r).real (finiteSlabConnectionEvent U i m n x e.val.1) *
        (percolationProfile d r).real (finiteSlabConnectionEvent U i m n (bondTip e.val) y) +
      (percolationProfile d r).real (finiteSlabConnectionEvent U i m n x (bondTip e.val)) *
        (percolationProfile d r).real (finiteSlabConnectionEvent U i m n e.val.1 y) := by
  let g1 := fun η : (j : internalBondSet U) → Bool ↦ (if η e then (0 : ℝ) else 1) *
    (if AvoidingDisjointOccurrence e (finiteSlabLocalConnectionEvent U i m n x e.val.1)
      (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y) η then 1 else 0)
  let g2 := fun η : (j : internalBondSet U) → Bool ↦ (if η e then (0 : ℝ) else 1) *
    (if AvoidingDisjointOccurrence e (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
      (finiteSlabLocalConnectionEvent U i m n e.val.1 y) η then 1 else 0)
  have hmono : finiteExpectationProfile (fun f : internalBondSet U ↦ (r f.val : ℝ))
      (fun η ↦ (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y then (1 : ℝ) else 0) -
        (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0)) ≤
      finiteExpectationProfile (fun f : internalBondSet U ↦ (r f.val : ℝ))
        (fun η ↦ g1 η+g2 η) := by
    unfold finiteExpectationProfile
    apply Finset.sum_le_sum
    intro η _
    apply mul_le_mul_of_nonneg_right (finiteSlab_profile_opening_indicator_le U i m n x y e η)
    apply Finset.prod_nonneg
    intro f _
    split_ifs
    · exact (r f.val).property.1
    · exact sub_nonneg.mpr (r f.val).property.2
  have hadd : finiteExpectationProfile (fun f : internalBondSet U ↦ (r f.val : ℝ))
      (fun η ↦ g1 η+g2 η) =
      finiteExpectationProfile (fun f : internalBondSet U ↦ (r f.val : ℝ)) g1 +
        finiteExpectationProfile (fun f : internalBondSet U ↦ (r f.val : ℝ)) g2 := by
    simp only [finiteExpectationProfile,add_mul,Finset.sum_add_distrib]
  have hprob (a b : Vertex d) :
      (Measure.pi (fun f : internalBondSet U ↦ bernoulliMeasure true false (r f.val))).real
        (finiteSlabLocalConnectionEvent U i m n a b) =
      (percolationProfile d r).real (finiteSlabConnectionEvent U i m n a b) := by
    calc
      _ = BK.profileEventProbability (fun f : internalBondSet U ↦ (r f.val : ℝ))
          (finiteSlabLocalConnectionEvent U i m n a b) :=
        (BK.profileEventProbability_eq_measureReal (fun f : internalBondSet U ↦ r f.val) _).symm
      _ = _ := (finiteSlabConnectionEvent_profile_probability r U i m n a b).symm
  calc
    _ ≤ (1-(r e.val : ℝ))⁻¹ * finiteExpectationProfile
        (fun f : internalBondSet U ↦ (r f.val : ℝ)) (fun η ↦ g1 η+g2 η) :=
      mul_le_mul_of_nonneg_left hmono
        (inv_nonneg.mpr (sub_nonneg.mpr (r e.val).property.2))
    _ = (1-(r e.val : ℝ))⁻¹ * finiteExpectationProfile
          (fun f : internalBondSet U ↦ (r f.val : ℝ)) g1 +
        (1-(r e.val : ℝ))⁻¹ * finiteExpectationProfile
          (fun f : internalBondSet U ↦ (r f.val : ℝ)) g2 := by rw [hadd,mul_add]
    _ ≤ _ := by
      have h1 := finite_profile_avoiding_russo_bk (fun f : internalBondSet U ↦ r f.val) P hP
        (fun f ↦ hr f.val) e (finiteSlabLocalConnectionEvent U i m n x e.val.1)
        (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y)
        (finiteSlabLocalConnectionEvent_increasing U i m n x e.val.1)
        (finiteSlabLocalConnectionEvent_increasing U i m n (bondTip e.val) y)
      have h2 := finite_profile_avoiding_russo_bk (fun f : internalBondSet U ↦ r f.val) P hP
        (fun f ↦ hr f.val) e (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
        (finiteSlabLocalConnectionEvent U i m n e.val.1 y)
        (finiteSlabLocalConnectionEvent_increasing U i m n x (bondTip e.val))
        (finiteSlabLocalConnectionEvent_increasing U i m n e.val.1 y)
      simpa only [hprob] using! add_le_add h1 h2

end NearCritical
