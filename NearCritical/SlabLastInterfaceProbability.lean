module
public import NearCritical.SlabLastInterface
public import NearCritical.TwoPhaseSlab
public import NearCritical.ProfileHybridBK

/-! Literal source critical Case(b): retain the strict-upper-phase q factor
while homogenizing only the prefix, using the PROVED actual-profile hybrid BK. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Actual probability version of the last-interface decomposition. The
interface crossing is omitted (bounded by1), and the low suffix is retained.
No probability, disjointness or inhomogeneous BK bound is a hypothesis. -/
theorem twoPhaseSlab_connection_last_interface_bound {d : ℕ} (i : Fin d)
    (m n : ℤ) (hm : 0 ≤ m) (p q : unitInterval) (hqp : q ≤ p)
    (x y : Vertex d) (hx : x i ≤ m) (hy : m < y i) :
    percolationProfile d (twoPhaseSlabProfile i m n p q)
      (connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) ≤
    ∑' v : Vertex d, if v i = m then
      percolation d q (connectionToSetEvent (finiteHeightSlab i (m+1) n)
        (v+Pi.single i 1) {y}) *
      percolation d p (connectionToSetEvent (finiteHeightSlab i 0 n) x {v}) else 0 := by
  let r := twoPhaseSlabProfile i m n p q
  let S := finiteHeightSlab i 0 n
  let T := finiteHeightSlab i (m+1) n
  let D : Vertex d → Set (Configuration d) := fun v =>
    if v i = m then {ω | DisjointOccurrence
      (connectionToSetEvent T (v+Pi.single i 1) {y})
      (connectionToSetEvent S x {v}) ω} else ∅
  have hdom : ∀ e, (r e : ℝ) ≤ (p : ℝ) := by
    intro e
    dsimp [r,twoPhaseSlabProfile]
    split
    · exact hqp
    · exact le_rfl
  have hsub : connectionToSetEvent S x {y} ⊆ ⋃ v, D v := by
    intro ω hω
    obtain ⟨v,hv,hdis⟩ := slab_connection_last_interface_split i n m x y hm hx hy hω
    apply Set.mem_iUnion.mpr
    refine ⟨v,?_⟩
    dsimp [D]
    rw [ite_eq_left hv]
    obtain ⟨F,H,hF,hH,hFH,hforceF,hforceH⟩ := hdis
    exact ⟨H,F,hH,hF,hFH.symm,hforceH,hforceF⟩
  calc
    _ ≤ percolationProfile d r (⋃ v, D v) := measure_mono hsub
    _ ≤ ∑' v, percolationProfile d r (D v) := measure_iUnion_le D
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : v i = m
      · simp only [D,ite_eq_left hv]
        have hb := profile_hybrid_bk p r hdom
          (connectionToSetEvent T (v+Pi.single i 1) {y})
          (connectionToSetEvent S x {v})
          (measurableSet_connectionToSetEvent _ _ _)
          (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
        have hq := twoPhaseSlab_connection_upper_law i m n p q T
          (Subset.rfl) (v+Pi.single i 1) {y}
        exact hb.trans_eq (by rw [hq])
      · simp [D,hv]

/-- Forward plane mass from an arbitrary vertex, obtained from the proved
plane reversal and endpoint symmetry rather than a new stationarity input. -/
lemma slab_plane_sum_forward {d : ℕ} (p : unitInterval) (i : Fin d)
    (a n j : ℤ) (v : Vertex d) :
    (∑' u : Vertex d, if u i = j then
      percolation d p (connectionToSetEvent (finiteHeightSlab i a n) v {u}) else 0) =
      slabPioneerMass p i a n (v i) j := by
  have he (u : Vertex d) := connectionToSetEvent_singleton_symm (finiteHeightSlab i a n) v u
  simp_rw [he]
  rw [slab_plane_sum_reverse,slabPioneerMass_symm]

/-- Exact source Case(b) product, retaining the literal strict-phase lower
height m+1. No loss of the subcritical suffix factor occurs in the sums. -/
theorem twoPhaseSlabPioneerMass_last_interface_bound {d : ℕ} (i : Fin d)
    (m n k j : ℤ) (hm : 0 ≤ m) (hkm : k ≤ m) (hmj : m < j)
    (p q : unitInterval) (hqp : q ≤ p) :
    twoPhaseSlabPioneerMass i p q m n k j ≤
      slabPioneerMass p i 0 n k m * slabPioneerMass q i (m+1) n (m+1) j := by
  let S := finiteHeightSlab i 0 n
  let T := finiteHeightSlab i (m+1) n
  let x : Vertex d := Pi.single i k
  let Q : Vertex d → Vertex d → ℝ≥0∞ := fun v u =>
    percolation d q (connectionToSetEvent T (v+Pi.single i 1) {u})
  let P : Vertex d → ℝ≥0∞ := fun v =>
    percolation d p (connectionToSetEvent S x {v})
  calc
    _ ≤ ∑' u : Vertex d, if u i = j then ∑' v : Vertex d,
        if v i = m then Q v u * P v else 0 else 0 := by
      unfold twoPhaseSlabPioneerMass profileSlabPioneerMass
      apply ENNReal.tsum_le_tsum
      intro u
      by_cases hu : u i = j
      · simp only [ite_eq_left hu]
        exact twoPhaseSlab_connection_last_interface_bound i m n hm p q hqp x u
          (by simpa [x] using hkm) (by omega)
      · simp [hu]
    _ = ∑' u : Vertex d, ∑' v : Vertex d, if v i = m then
        (if u i = j then Q v u else 0) * P v else 0 := by
      apply tsum_congr
      intro u
      by_cases hu : u i = j
      · simp only [ite_eq_left hu]
      · simp [hu]
    _ = ∑' v : Vertex d, ∑' u : Vertex d, if v i = m then
        (if u i = j then Q v u else 0) * P v else 0 := ENNReal.tsum_comm
    _ = ∑' v : Vertex d, (if v i = m then
        slabPioneerMass q i (m+1) n (m+1) j * P v else 0) := by
      apply tsum_congr
      intro v
      by_cases hv : v i = m
      · simp only [ite_eq_left hv]
        rw [ENNReal.tsum_mul_right]
        have hplane := slab_plane_sum_forward q i (m+1) n j (v+Pi.single i 1)
        have hheight : ((v+Pi.single i 1) : Vertex d) i = m+1 := by simp [hv]
        rw [hheight] at hplane
        exact congrArg (fun z => z * P v) hplane
      · simp [hv]
    _ = slabPioneerMass q i (m+1) n (m+1) j * slabPioneerMass p i 0 n k m := by
      unfold slabPioneerMass
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      by_cases hv : v i = m
      · simp only [ite_eq_left hv]
        rfl
      · simp [hv]
    _ = _ := mul_comm _ _

/-- Source Case(c), at any cut lying strictly inside the upper phase. Unlike
the interface cut, the suffix including its cut vertex already has the q-law. -/
theorem twoPhaseSlab_connection_upper_cut_bound {d : ℕ} (i : Fin d)
    (m n t : ℤ) (hm : 0 ≤ m) (ht : m+1 ≤ t)
    (p q : unitInterval) (hqp : q ≤ p)
    (x y : Vertex d) (hx : x i ≤ t) (hy : t ≤ y i) :
    percolationProfile d (twoPhaseSlabProfile i m n p q)
      (connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) ≤
    ∑' v : Vertex d, if v i = t then
      percolation d q (connectionToSetEvent (finiteHeightSlab i t n) v {y}) *
      percolation d p (connectionToSetEvent (finiteHeightSlab i 0 n) x {v}) else 0 := by
  let r := twoPhaseSlabProfile i m n p q
  let S := finiteHeightSlab i 0 n
  let T := finiteHeightSlab i t n
  let D : Vertex d → Set (Configuration d) := fun v =>
    if v i = t then {ω | DisjointOccurrence
      (connectionToSetEvent T v {y}) (connectionToSetEvent S x {v}) ω} else ∅
  have hdom : ∀ e, (r e : ℝ) ≤ (p : ℝ) := by
    intro e
    dsimp [r,twoPhaseSlabProfile]
    split
    · exact hqp
    · exact le_rfl
  have hST : S ∩ {z | t ≤ z i} = T := by
    ext z
    change ((0 ≤ z i ∧ z i ≤ n) ∧ t ≤ z i) ↔ (t ≤ z i ∧ z i ≤ n)
    omega
  have hT : T ⊆ finiteHeightSlab i (m+1) n := by
    intro z hz
    exact ⟨ht.trans hz.1,hz.2⟩
  have hsub : connectionToSetEvent S x {y} ⊆ ⋃ v, D v := by
    intro ω hω
    obtain ⟨v,hv,hdis⟩ := connectionToSet_last_height_split S {y} x i t hx
      (by intro z hz; have hzy : z = y := hz; subst z; exact hy) hω
    rw [hST] at hdis
    apply Set.mem_iUnion.mpr
    refine ⟨v,?_⟩
    dsimp [D]
    rw [ite_eq_left hv]
    obtain ⟨F,H,hF,hH,hFH,hforceF,hforceH⟩ := hdis
    exact ⟨H,F,hH,hF,hFH.symm,hforceH,hforceF⟩
  calc
    _ ≤ percolationProfile d r (⋃ v, D v) := measure_mono hsub
    _ ≤ ∑' v, percolationProfile d r (D v) := measure_iUnion_le D
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : v i = t
      · simp only [D,ite_eq_left hv]
        have hb := profile_hybrid_bk p r hdom
          (connectionToSetEvent T v {y}) (connectionToSetEvent S x {v})
          (measurableSet_connectionToSetEvent _ _ _)
          (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
        have hq := twoPhaseSlab_connection_upper_law i m n p q T hT v {y}
        exact hb.trans_eq (by rw [hq])
      · simp [D,hv]

/-- Summed source Case(c) reduction at a genuine upper-phase cut. Cut selection
and the exceptional cut=m geometry are deliberately not hidden in this lemma. -/
theorem twoPhaseSlabPioneerMass_upper_cut_bound {d : ℕ} (i : Fin d)
    (m n k j t : ℤ) (hm : 0 ≤ m) (ht : m+1 ≤ t) (hkt : k ≤ t) (htj : t ≤ j)
    (p q : unitInterval) (hqp : q ≤ p) :
    twoPhaseSlabPioneerMass i p q m n k j ≤
      slabPioneerMass p i 0 n k t * slabPioneerMass q i t n t j := by
  let S := finiteHeightSlab i 0 n
  let T := finiteHeightSlab i t n
  let x : Vertex d := Pi.single i k
  let Q : Vertex d → Vertex d → ℝ≥0∞ := fun v u =>
    percolation d q (connectionToSetEvent T v {u})
  let P : Vertex d → ℝ≥0∞ := fun v =>
    percolation d p (connectionToSetEvent S x {v})
  calc
    _ ≤ ∑' u : Vertex d, if u i = j then ∑' v : Vertex d,
        if v i = t then Q v u * P v else 0 else 0 := by
      unfold twoPhaseSlabPioneerMass profileSlabPioneerMass
      apply ENNReal.tsum_le_tsum
      intro u
      by_cases hu : u i = j
      · simp only [ite_eq_left hu]
        exact twoPhaseSlab_connection_upper_cut_bound i m n t hm ht p q hqp x u
          (by simpa [x] using hkt) (by omega)
      · simp [hu]
    _ = ∑' u : Vertex d, ∑' v : Vertex d, if v i = t then
        (if u i = j then Q v u else 0) * P v else 0 := by
      apply tsum_congr
      intro u
      by_cases hu : u i = j
      · simp only [ite_eq_left hu]
      · simp [hu]
    _ = ∑' v : Vertex d, ∑' u : Vertex d, if v i = t then
        (if u i = j then Q v u else 0) * P v else 0 := ENNReal.tsum_comm
    _ = ∑' v : Vertex d, (if v i = t then
        slabPioneerMass q i t n t j * P v else 0) := by
      apply tsum_congr
      intro v
      by_cases hv : v i = t
      · simp only [ite_eq_left hv]
        rw [ENNReal.tsum_mul_right]
        have hplane := slab_plane_sum_forward q i t n j v
        rw [hv] at hplane
        exact congrArg (fun z => z * P v) hplane
      · simp [hv]
    _ = slabPioneerMass q i t n t j * slabPioneerMass p i 0 n k t := by
      unfold slabPioneerMass
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      by_cases hv : v i = t
      · simp only [ite_eq_left hv]
        rfl
      · simp [hv]
    _ = _ := mul_comm _ _

/-- A midpoint cut constrained to lie in strict-upper q percolation.
The admissibility and rounding-loss hypotheses are made explicit below. -/
def twoPhaseUpperCut (m k j : ℤ) : ℤ := max (m+1) ((k+j)/2)

/-- The chosen cut is admissible whenever the target is above the interface.
The k=j case is included; its strict-upper suffix may have length zero. -/
lemma twoPhaseUpperCut_admissible {m k j : ℤ} (_hmk : m ≤ k) (hkj : k ≤ j)
    (hmj : m < j) :
    m+1 ≤ twoPhaseUpperCut m k j ∧ k ≤ twoPhaseUpperCut m k j ∧
      twoPhaseUpperCut m k j ≤ j := by
  unfold twoPhaseUpperCut
  rw [max_def]
  split <;> omega

/-- Explicit one-layer rounding loss. This is an integer-level estimate,
not an assumed exponential probability estimate. -/
lemma twoPhaseUpperCut_gap {m k j : ℤ} (hmk : m ≤ k) (_hkj : k ≤ j)
    (hmj : m < j) :
    j-k ≤ 2*(j-twoPhaseUpperCut m k j)+2 := by
  unfold twoPhaseUpperCut
  rw [max_def]
  split <;> omega

/-- Actual source Case(c) product at an automatically admissible midpoint.
The one-layer loss is exposed separately; no exceptional cut=m is used. -/
theorem twoPhaseSlabPioneerMass_midpoint_bound {d : ℕ} (i : Fin d)
    (m n k j : ℤ) (hm : 0 ≤ m) (hmk : m ≤ k) (hkj : k ≤ j) (hmj : m < j)
    (p q : unitInterval) (hqp : q ≤ p) :
    twoPhaseSlabPioneerMass i p q m n k j ≤
      slabPioneerMass p i 0 n k (twoPhaseUpperCut m k j) *
        slabPioneerMass q i (twoPhaseUpperCut m k j) n (twoPhaseUpperCut m k j) j := by
  obtain ⟨ht,hkt,htj⟩ := twoPhaseUpperCut_admissible hmk hkj hmj
  exact twoPhaseSlabPioneerMass_upper_cut_bound i m n k j _ hm ht hkt htj p q hqp

end NearCritical
