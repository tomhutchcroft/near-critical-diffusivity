module

public import NearCritical.TwoPhaseSlabTranslation
public import NearCritical.SlabPioneerConvolution

/-! Whole-plane sums for the literal two-phase slab law. Phase interface m,
profile top n and domain S_(0,n) remain fixed in every factor. Endpoint-label
reversal uses transverse translation, never reflection of environments. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped ENNReal

/-- Point transverse translation under the SAME actual profile. The domain
image is simplified only using the zero distinguished-coordinate shift. -/
lemma twoPhaseSlab_point_probability_transverse {d : ℕ} (i : Fin d) (m n : ℤ)
    (p q : unitInterval) (a x y : Vertex d) (ha : a i = 0) :
    percolationProfile d (twoPhaseSlabProfile i m n p q)
      (connectionToSetEvent (finiteHeightSlab i 0 n) (a+x) {a+y}) =
    percolationProfile d (twoPhaseSlabProfile i m n p q)
      (connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) := by
  simpa only [translate_finiteHeightSlab i 0 n a ha,Set.image_singleton] using
    twoPhaseSlab_connection_probability_transverse i m n p q a ha x
      (finiteHeightSlab i 0 n) {y}

/-- Reverse a full plane of endpoint labels. No phase or configuration is
reflected; the required actual law equality is only transverse translation. -/
theorem twoPhaseSlab_plane_sum_reverse {d : ℕ} (i : Fin d) (p q : unitInterval)
    (m n j : ℤ) (v : Vertex d) :
    (∑' u : Vertex d, if u i = j then
      percolationProfile d (twoPhaseSlabProfile i m n p q)
        (connectionToSetEvent (finiteHeightSlab i 0 n) u {v}) else 0) =
      twoPhaseSlabPioneerMass i p q m n j (v i) := by
  let b : Vertex d := Pi.single i j+v
  rw [← (slabReverseLabels b).tsum_eq]
  unfold twoPhaseSlabPioneerMass profileSlabPioneerMass
  apply tsum_congr
  intro w
  have hcond : ((slabReverseLabels b) w) i = j ↔ w i = v i := by
    change (b-w) i = j ↔ w i = v i
    simp only [b,Pi.sub_apply,Pi.add_apply,Pi.single_eq_same]
    omega
  by_cases hw : w i = v i
  · rw [ite_eq_left (hcond.mpr hw),ite_eq_left hw]
    let u := (slabReverseLabels b) w
    let a : Vertex d := Pi.single i j-u
    have hui : u i = j := hcond.mpr hw
    have ha : a i = 0 := by simp [a,hui]
    have hax : a+u = Pi.single i j := by
      ext t
      change ((Pi.single i j : Vertex d) t-u t)+u t = (Pi.single i j : Vertex d) t
      omega
    have hay : a+v = w := by
      ext t
      change ((Pi.single i j : Vertex d) t-((Pi.single i j : Vertex d) t+v t-w t))+v t = w t
      omega
    have ht := twoPhaseSlab_point_probability_transverse i m n p q a u v ha
    rw [hax,hay] at ht
    exact ht.symm
  · simp only [ite_eq_right (mt hcond.mp hw),ite_eq_right hw]

/-- Two-phase canonical source/target-height symmetry, even for infinite mass.
The profile interface and top are identical on both sides. -/
theorem twoPhaseSlabPioneerMass_symm {d : ℕ} (i : Fin d) (p q : unitInterval)
    (m n k j : ℤ) :
    twoPhaseSlabPioneerMass i p q m n k j = twoPhaseSlabPioneerMass i p q m n j k := by
  calc
    _ = ∑' u : Vertex d, if u i = j then
        percolationProfile d (twoPhaseSlabProfile i m n p q)
          (connectionToSetEvent (finiteHeightSlab i 0 n) u {Pi.single i k}) else 0 := by
      unfold twoPhaseSlabPioneerMass profileSlabPioneerMass
      apply tsum_congr
      intro u
      rw [connectionToSetEvent_singleton_symm]
    _ = _ := by simpa using twoPhaseSlab_plane_sum_reverse i p q m n j (Pi.single i k)

/-- An arbitrary-source whole-plane row is exactly the actual canonical mass
at its source height, without moving or identifying any finite cutoff. -/
theorem twoPhaseSlab_plane_sum_forward {d : ℕ} (i : Fin d) (p q : unitInterval)
    (m n : ℤ) (x : Vertex d) (j : ℤ) :
    (∑' y : Vertex d, if y i = j then
      percolationProfile d (twoPhaseSlabProfile i m n p q)
        (connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) else 0) =
      twoPhaseSlabPioneerMass i p q m n (x i) j := by
  calc
    _ = ∑' y : Vertex d, if y i = j then
        percolationProfile d (twoPhaseSlabProfile i m n p q)
          (connectionToSetEvent (finiteHeightSlab i 0 n) y {x}) else 0 := by
      apply tsum_congr
      intro y
      rw [connectionToSetEvent_singleton_symm]
    _ = twoPhaseSlabPioneerMass i p q m n j (x i) := twoPhaseSlab_plane_sum_reverse i p q m n j x
    _ = _ := twoPhaseSlabPioneerMass_symm i p q m n j (x i)

/-- Exact double-plane factorization under one FIXED two-phase profile/domain.
All summands are ENNReal, so no finite-mass or real-summability premise occurs. -/
theorem twoPhaseSlab_double_plane_sum {d : ℕ} (i : Fin d) (p q : unitInterval)
    (m n t j : ℤ) (x : Vertex d) :
    (∑' u : Vertex d, if u i = j then ∑' v : Vertex d, if v i = t then
      percolationProfile d (twoPhaseSlabProfile i m n p q)
        (connectionToSetEvent (finiteHeightSlab i 0 n) x {v}) *
      percolationProfile d (twoPhaseSlabProfile i m n p q)
        (connectionToSetEvent (finiteHeightSlab i 0 n) u {v}) else 0 else 0) =
      twoPhaseSlabPioneerMass i p q m n (x i) t *
        twoPhaseSlabPioneerMass i p q m n j t := by
  calc
    _ = ∑' u : Vertex d, ∑' v : Vertex d, if v i = t then
        percolationProfile d (twoPhaseSlabProfile i m n p q)
          (connectionToSetEvent (finiteHeightSlab i 0 n) x {v}) *
        (if u i = j then percolationProfile d (twoPhaseSlabProfile i m n p q)
          (connectionToSetEvent (finiteHeightSlab i 0 n) u {v}) else 0) else 0 := by
      apply tsum_congr
      intro u
      by_cases hu : u i = j
      · simp only [ite_eq_left hu]
      · simp [hu]
    _ = ∑' v : Vertex d, ∑' u : Vertex d, if v i = t then
        percolationProfile d (twoPhaseSlabProfile i m n p q)
          (connectionToSetEvent (finiteHeightSlab i 0 n) x {v}) *
        (if u i = j then percolationProfile d (twoPhaseSlabProfile i m n p q)
          (connectionToSetEvent (finiteHeightSlab i 0 n) u {v}) else 0) else 0 := ENNReal.tsum_comm
    _ = ∑' v : Vertex d, (if v i = t then
        percolationProfile d (twoPhaseSlabProfile i m n p q)
          (connectionToSetEvent (finiteHeightSlab i 0 n) x {v}) else 0) *
        twoPhaseSlabPioneerMass i p q m n j t := by
      apply tsum_congr
      intro v
      by_cases hv : v i = t
      · simp only [ite_eq_left hv]
        rw [ENNReal.tsum_mul_left,twoPhaseSlab_plane_sum_reverse,hv]
      · simp only [ite_eq_right hv,tsum_zero,zero_mul]
    _ = (∑' v : Vertex d, if v i = t then
        percolationProfile d (twoPhaseSlabProfile i m n p q)
          (connectionToSetEvent (finiteHeightSlab i 0 n) x {v}) else 0) *
        twoPhaseSlabPioneerMass i p q m n j t := ENNReal.tsum_mul_right
    _ = _ := by rw [twoPhaseSlab_plane_sum_forward]

end NearCritical
