module

public import NearCritical.Section8SlabBoundaryMass
public import NearCritical.Section10BoxFaceFromPioneer
public import NearCritical.ThreePointTreeGraphDerivation

/-! Bound the slab second moment by the critical half-space pioneer mass
and the restricted three-point tree-graph inequality. -/
@[expose] public section
noncomputable section

namespace NearCritical.Section8

open MeasureTheory
open scoped Classical BigOperators

private theorem slab_root_plane_mass_le {d n m : ℕ} (i : Fin d) {K : ℝ} (hK : 0 ≤ K)
    (hp : halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K)
    (Q : Finset (Vertex d)) (hQ : ∀ y ∈ Q, 0 ≤ y i ∧ y i ≤ (n : ℤ)) :
    ∑ y ∈ slabTopTargets Q i m, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (Q : Set (Vertex d)) 0 {y}) ≤ K := by
  let μ := percolation d (criticalPoint d)
  let H : Set (Vertex d) := {z | 0 ≤ z i}
  let F := slabTopTargets Q i m
  let f (y : Vertex d) := if y i = (m : ℤ) then μ (connectionToSetEvent H 0 {y}) else 0
  have hsub : (Q : Set (Vertex d)) ⊆ H := fun y hy => (hQ y hy).1
  have hsum : ∑ y ∈ F, μ (connectionToSetEvent (Q : Set (Vertex d)) 0 {y}) ≤ ENNReal.ofReal K := by
    calc
      _ ≤ ∑ y ∈ F, f y := by
        apply Finset.sum_le_sum
        intro y hy
        rw [show f y = μ (connectionToSetEvent H 0 {y}) from
          if_pos (Finset.mem_filter.mp hy).2]
        exact measure_mono (connectionToSetEvent_mono hsub subset_rfl _)
      _ ≤ ∑' y, f y := ENNReal.sum_le_tsum _
      _ = halfSpacePioneerMass (criticalPoint d) i (m : ℤ) := halfSpace_prefix_sum _ i _
      _ ≤ _ := hp
  have he := ENNReal.toReal_le_of_le_ofReal hK hsum
  rwa [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at he

private theorem slab_top_mass_le {d n : ℕ} (i : Fin d) {K : ℝ} (hK : 0 ≤ K)
    (hp : ∀ m : ℕ, halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K)
    (Q : Finset (Vertex d)) (hQ : ∀ y ∈ Q, 0 ≤ y i ∧ y i ≤ (n : ℤ))
    (u : Vertex d) (hu : u ∈ Q) :
    ∑ y ∈ slabTopTargets Q i n, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (Q : Set (Vertex d)) u {y}) ≤ K := by
  let p := criticalPoint d
  let μ := percolation d p
  let H : Set (Vertex d) := {z | z i ≤ (n : ℤ)}
  let H' : Set (Vertex d) := {z | -(n : ℤ) ≤ z i}
  let F := slabTopTargets Q i n
  have hsub : (Q : Set (Vertex d)) ⊆ H := fun y hy => (hQ y hy).2
  have hinv (y : Vertex d) : μ (connectionToSetEvent H u {y}) =
      μ (connectionToSetEvent H' (-u) {-y}) := by
    have h := connectionToSet_probability_inversion p u H {y}
    rw [show Neg.neg '' H = H' from Section10.neg_image_upper_halfSpace i (n : ℤ),
      Set.image_singleton] at h
    exact h.symm
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (-u) i - -(n : ℤ) by
    rw [Pi.neg_apply]; exact sub_nonneg.mpr (neg_le_neg (hQ u hu).2))
  have hsum : ∑ y ∈ F, μ (connectionToSetEvent (Q : Set (Vertex d)) u {y}) ≤ ENNReal.ofReal K := by
    calc
      _ ≤ ∑ y ∈ F, μ (connectionToSetEvent H u {y}) :=
        Finset.sum_le_sum fun y _ => measure_mono (connectionToSetEvent_mono hsub subset_rfl u)
      _ = ∑ y ∈ F.image Neg.neg, μ (connectionToSetEvent H' (-u) {y}) := by
        rw [Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
        exact Finset.sum_congr rfl fun y _ => hinv y
      _ ≤ halfSpacePioneerMass p i ((-u) i - -(n : ℤ)) :=
        Section10.halfSpace_face_sum_le_pioneer p i _ (-u) _ (by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
          rw [Pi.neg_apply, (Finset.mem_filter.mp hz).2])
      _ ≤ _ := by rw [hm]; exact hp m
  have he := ENNReal.toReal_le_of_le_ofReal hK hsum
  rwa [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at he

private theorem slab_root_mass_le {d n : ℕ} (i : Fin d) {K : ℝ} (hK : 0 ≤ K)
    (hp : ∀ m : ℕ, halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K)
    (Q : Finset (Vertex d)) (hQ : ∀ y ∈ Q, 0 ≤ y i ∧ y i ≤ (n : ℤ)) :
    ∑ y ∈ Q, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (Q : Set (Vertex d)) 0 {y}) ≤ ((n : ℝ) + 1) * K := by
  let h (y : Vertex d) := (y i).toNat
  let P (y : Vertex d) := (percolation d (criticalPoint d)).real
    (connectionToSetEvent (Q : Set (Vertex d)) 0 {y})
  have hh : ∀ y ∈ Q, h y ∈ Finset.range (n + 1) := by
    intro y hy
    apply Finset.mem_range.mpr
    have := (hQ y hy).2
    dsimp [h]
    omega
  have hF (m : ℕ) : Q.filter (fun y => h y = m) = slabTopTargets Q i m := by
    ext y
    simp only [slabTopTargets, Finset.mem_filter]
    constructor <;> rintro ⟨hy, hm⟩ <;> refine ⟨hy, ?_⟩
    · have := (hQ y hy).1
      dsimp [h] at hm
      omega
    · simp [h, hm]
  change ∑ y ∈ Q, P y ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hh P]
  calc
    _ ≤ ∑ _m ∈ Finset.range (n + 1), K := by
      apply Finset.sum_le_sum
      intro m _
      rw [hF]
      exact slab_root_plane_mass_le i hK (hp m) Q hQ
    _ = _ := by simp [nsmul_eq_mul]


private theorem heart_count_sq_le_tripod {d : ℕ} (p : unitInterval)
    (Q Y : Finset (Vertex d)) (x : Vertex d) :
    let μ := percolation d p
    let P := fun a b => μ.real (connectionToSetEvent (Q : Set (Vertex d)) a {b})
    (∫ θ, heartConnectionCount Q Y x θ ^ 2 ∂μ) ≤
      ∑ u ∈ Q, P x u * (∑ y ∈ Y, P u y) ^ 2 := by
  intro μ P
  let D := (Q : Set (Vertex d))
  let A (y : Vertex d) := connectionToSetEvent D x {y}
  let J (E : Set (Configuration d)) := E.indicator (fun _ => (1 : ℝ))
  have hcount (θ : Configuration d) : heartConnectionCount Q Y x θ = ∑ y ∈ Y, J (A y) θ := by
    rw [heartConnectionCount_eq_sum]
    apply Finset.sum_congr rfl
    intro y _
    have he : y ∈ finiteBoxCluster θ Q x ↔ θ ∈ A y := by
      rw [mem_finiteBoxCluster]
      constructor
      · rintro ⟨hy, ⟨w⟩⟩
        have hx : x ∈ D := restrictedWalk_support w.reverse hy x w.reverse.end_mem_support
        exact ⟨hx, y, rfl, hy, ⟨w⟩⟩
      · rintro ⟨_, z, hz, hzD, hpath⟩
        have hzy : z = y := hz
        subst z
        exact ⟨hzD, hpath⟩
    simp only [J, Set.indicator_apply, he]
  have hsq (θ : Configuration d) : heartConnectionCount Q Y x θ ^ 2 =
      ∑ y ∈ Y, ∑ z ∈ Y, J (A y ∩ A z) θ := by
    rw [hcount, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    by_cases hy : θ ∈ A y <;> by_cases hz : θ ∈ A z <;> simp [J, hy, hz]
  have hI (y z : Vertex d) : Integrable (J (A y ∩ A z)) μ :=
    (integrable_const _).indicator ((measurableSet_connectionToSetEvent _ _ _).inter
      (measurableSet_connectionToSetEvent _ _ _))
  calc
    _ = ∑ y ∈ Y, ∑ z ∈ Y, μ.real (A y ∩ A z) := by
      simp_rw [hsq]
      rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ (fun z _ => hI y z))]
      apply Finset.sum_congr rfl
      intro y _
      rw [integral_finsetSum _ (fun z _ => hI y z)]
      exact Finset.sum_congr rfl fun z _ => integral_indicator_one
        ((measurableSet_connectionToSetEvent _ _ _).inter (measurableSet_connectionToSetEvent _ _ _))
    _ ≤ ∑ y ∈ Y, ∑ z ∈ Y, ∑ u ∈ Q, P x u * P u y * P u z := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro z _
      refine (restricted_tripod_connection_probability_le p Q x y z).trans_eq ?_
      apply Finset.sum_congr rfl
      intro u _
      have hz : P z u = P u z := congrArg μ.real (connectionToSetEvent_singleton_symm D z u)
      change P x u * P u y * P z u = _
      rw [hz]
    _ = _ := by
      have hs (y : Vertex d) :
          (∑ z ∈ Y, ∑ u ∈ Q, P x u * P u y * P u z) =
            ∑ u ∈ Q, ∑ z ∈ Y, P x u * P u y * P u z := Finset.sum_comm
      simp_rw [hs]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

/-- The nearest-neighbor slab count second moment follows from the
critical half-space pioneer upper bound. -/
theorem slabBoundarySecondMomentUpper_of_pioneerMass {d : ℕ} (i : Fin d)
    {K : ℝ} (hK : 0 ≤ K)
    (hp : ∀ m : ℕ, halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K) :
    SlabBoundarySecondMomentUpper i (2 * K ^ 3) := by
  intro n hn Q hQ
  let Y := slabTopTargets Q i n
  let P (x y : Vertex d) := (percolation d (criticalPoint d)).real
    (connectionToSetEvent (Q : Set (Vertex d)) x {y})
  refine (heart_count_sq_le_tripod (criticalPoint d) Q Y 0).trans ?_
  change (∑ u ∈ Q, P 0 u * (∑ y ∈ Y, P u y) ^ 2) ≤ _
  calc
    _ ≤ ∑ u ∈ Q, P 0 u * K ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
        (slab_top_mass_le i hK hp Q hQ u hu) 2
    _ = (∑ u ∈ Q, P 0 u) * K ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (((n : ℝ) + 1) * K) * K ^ 2 :=
      mul_le_mul_of_nonneg_right (slab_root_mass_le i hK hp Q hQ) (sq_nonneg _)
    _ = (K ^ 3) * ((n : ℝ) + 1) := by ring
    _ ≤ (K ^ 3) * (2 * (n : ℝ)) := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hK _)
    _ = _ := by ring

end NearCritical.Section8
