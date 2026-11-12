module

public import NearCritical.HalfSpaceInteriorReduction
public import Mathlib.Tactic.Abel

/-! Literal slab pioneer masses and source prop.A.basic(2). Slabs have finite
height and infinite transverse extent. Probabilities and sums are ENNReal;
no finiteness, convolution, or reflection-law input is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Source S_{m,n}, with any selected coordinate as the first direction. -/
def finiteHeightSlab {d : ℕ} (i : Fin d) (m n : ℤ) : Set (Vertex d) :=
  {x | m ≤ x i ∧ x i ≤ n}

/-- Literal source A_p(m,n;k,j): the actual mass of connections from k*e_i
inside S_{m,n} to vertices of level j. Infinite values are retained. -/
def slabPioneerMass {d : ℕ} (p : unitInterval) (i : Fin d) (m n k j : ℤ) : ℝ≥0∞ :=
  ∑' u : Vertex d, if u i = j then
    percolation d p (connectionToSetEvent (finiteHeightSlab i m n) (Pi.single i k) {u}) else 0

/-- A maximum of a finite simple open path, chosen by minimizing negative
height, splits it into two edge-disjoint paths in S_{m,height(u)}. -/
theorem slab_connection_maximum_split {d : ℕ} {ω : Configuration d}
    (i : Fin d) (m n : ℤ) (x y : Vertex d)
    (hω : ω ∈ connectionToSetEvent (finiteHeightSlab i m n) x {y}) :
    ∃ u : Vertex d, max (x i) (y i) ≤ u i ∧ u i ≤ n ∧
      DisjointOccurrence
        (connectionToSetEvent (finiteHeightSlab i m (u i)) x {u})
        (connectionToSetEvent (finiteHeightSlab i m (u i)) y {u}) ω := by
  obtain ⟨hx, z, hz, _, ⟨w⟩⟩ := hω
  have hzy : z = y := hz
  subst z
  have hle : restrictedGraph ω (finiteHeightSlab i m n) ≤ openGraph ω := fun _ _ h ↦ h.1
  let q : (openGraph ω).Walk x y :=
    (w.toPath : (restrictedGraph ω (finiteHeightSlab i m n)).Walk x y).mapLe hle
  have hq : q.IsPath := w.toPath.property.mapLe _
  have hqS : ∀ z ∈ q.support, z ∈ finiteHeightSlab i m n := by
    simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using
      restrictedWalk_support (w.toPath : (restrictedGraph ω (finiteHeightSlab i m n)).Walk x y) hx
  obtain ⟨u, hu, hmin⟩ := q.support.toFinset.exists_min_image (fun z ↦ -(z i)) ⟨x, by simp⟩
  have hu' : u ∈ q.support := List.mem_toFinset.mp hu
  have hmax : ∀ z ∈ q.support, z i ≤ u i := by
    intro z hz
    have hh := hmin z (List.mem_toFinset.mpr hz)
    omega
  refine ⟨u, max_le (hmax x q.start_mem_support) (hmax y q.end_mem_support),
    (hqS u hu').2, ?_⟩
  have hsplit := simplePath_split_occurrence q hq hu'
    (finiteHeightSlab i m (u i)) (finiteHeightSlab i m (u i)) {y}
    (fun z hz ↦ ⟨(hqS z (q.support_takeUntil_subset_support hu' hz)).1,
      hmax z (q.support_takeUntil_subset_support hu' hz)⟩)
    (fun z hz ↦ ⟨(hqS z (q.support_dropUntil_subset_support hu' hz)).1,
      hmax z (q.support_dropUntil_subset_support hu' hz)⟩) rfl
  rw [connectionToSetEvent_singleton_symm (finiteHeightSlab i m (u i)) u y] at hsplit
  exact hsplit

lemma translate_finiteHeightSlab {d : ℕ} (i : Fin d) (m n : ℤ)
    (a : Vertex d) (ha : a i = 0) :
    (fun z ↦ a + z) '' finiteHeightSlab i m n = finiteHeightSlab i m n := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [finiteHeightSlab, ha] using hy
  · intro hz
    refine ⟨-a + z, ?_, by simp⟩
    simpa [finiteHeightSlab, ha] using hz

/-- Transverse translation of the actual restricted-domain law. -/
lemma slab_connection_probability_translation {d : ℕ} (p : unitInterval)
    (i : Fin d) (m n : ℤ) (a x y : Vertex d) (ha : a i = 0) :
    percolation d p (connectionToSetEvent (finiteHeightSlab i m n) (a + x) {a + y}) =
      percolation d p (connectionToSetEvent (finiteHeightSlab i m n) x {y}) := by
  simpa only [translate_finiteHeightSlab i m n a ha, Set.image_singleton] using
    connectionToSet_probability_translation p a x (finiteHeightSlab i m n) {y}

/-- A bijection of endpoint labels; it is NOT a reflection of environments. -/
def slabReverseLabels {d : ℕ} (b : Vertex d) : Vertex d ≃ Vertex d where
  toFun u := b - u
  invFun u := b - u
  left_inv u := by ext t; change b t - (b t - u t) = u t; omega
  right_inv u := by ext t; change b t - (b t - u t) = u t; omega

/-- Plane reversal follows from transverse stationarity and endpoint reversal.
No reflection-invariance law is used. -/
theorem slab_plane_sum_reverse {d : ℕ} (p : unitInterval) (i : Fin d)
    (m n j : ℤ) (v : Vertex d) :
    (∑' u : Vertex d, if u i = j then
      percolation d p (connectionToSetEvent (finiteHeightSlab i m n) u {v}) else 0) =
      slabPioneerMass p i m n j (v i) := by
  let b : Vertex d := Pi.single i j + v
  rw [← (slabReverseLabels b).tsum_eq]
  unfold slabPioneerMass
  apply tsum_congr
  intro w
  have hcond : ((slabReverseLabels b) w) i = j ↔ w i = v i := by
    change (b - w) i = j ↔ w i = v i
    simp only [b, Pi.sub_apply, Pi.add_apply, Pi.single_eq_same]
    omega
  by_cases hw : w i = v i
  · rw [ite_eq_left (hcond.mpr hw), ite_eq_left hw]
    let u := (slabReverseLabels b) w
    let a : Vertex d := Pi.single i j - u
    have hui : u i = j := hcond.mpr hw
    have ha : a i = 0 := by simp [a, hui]
    have hax : a + u = Pi.single i j := by
      ext t
      change ((Pi.single i j : Vertex d) t - u t) + u t = (Pi.single i j : Vertex d) t
      omega
    have hay : a + v = w := by
      ext t
      change ((Pi.single i j : Vertex d) t - ((Pi.single i j : Vertex d) t + v t - w t)) + v t = w t
      omega
    have ht := slab_connection_probability_translation p i m n a u v ha
    rw [hax, hay] at ht
    exact ht.symm
  · simp only [ite_eq_right (mt hcond.mp hw), ite_eq_right hw]

/-- Source eq.A.identity1, without a reflection law or a finiteness premise. -/
theorem slabPioneerMass_symm {d : ℕ} (p : unitInterval) (i : Fin d)
    (m n k j : ℤ) : slabPioneerMass p i m n k j = slabPioneerMass p i m n j k := by
  calc
    _ = ∑' u : Vertex d, if u i = j then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m n) u {Pi.single i k}) else 0 := by
      unfold slabPioneerMass
      apply tsum_congr
      intro u
      rw [connectionToSetEvent_singleton_symm]
    _ = _ := by simpa using slab_plane_sum_reverse p i m n j (Pi.single i k)

/-- The actual maximum-height union bound and BK, regrouped by its finite
height interval. All probability products are proved, not premises. -/
theorem slab_connection_maximum_bk {d : ℕ} (p : unitInterval)
    (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    percolation d p (connectionToSetEvent (finiteHeightSlab i m n) x {y}) ≤
      ∑ t ∈ Finset.Icc (max (x i) (y i)) n, ∑' v : Vertex d, if v i = t then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m t) x {v}) *
          percolation d p (connectionToSetEvent (finiteHeightSlab i m t) y {v}) else 0 := by
  let C := fun v : Vertex d ↦ {ω : Configuration d | max (x i) (y i) ≤ v i ∧ v i ≤ n ∧
    DisjointOccurrence (connectionToSetEvent (finiteHeightSlab i m (v i)) x {v})
      (connectionToSetEvent (finiteHeightSlab i m (v i)) y {v}) ω}
  have hsub : connectionToSetEvent (finiteHeightSlab i m n) x {y} ⊆ ⋃ v, C v := by
    intro ω hω
    obtain ⟨v, hxyv, hvn, hdis⟩ := slab_connection_maximum_split i m n x y hω
    exact Set.mem_iUnion.mpr ⟨v, hxyv, hvn, hdis⟩
  calc
    _ ≤ percolation d p (⋃ v, C v) := measure_mono hsub
    _ ≤ ∑' v, percolation d p (C v) := measure_iUnion_le _
    _ ≤ ∑' v : Vertex d, if max (x i) (y i) ≤ v i ∧ v i ≤ n then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m (v i)) x {v}) *
          percolation d p (connectionToSetEvent (finiteHeightSlab i m (v i)) y {v}) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : max (x i) (y i) ≤ v i ∧ v i ≤ n
      · rw [ite_eq_left hv]
        exact (measure_mono (show C v ⊆ {ω | DisjointOccurrence
          (connectionToSetEvent (finiteHeightSlab i m (v i)) x {v})
          (connectionToSetEvent (finiteHeightSlab i m (v i)) y {v}) ω} from
            fun _ h ↦ h.2.2)).trans (connectionToSet_bk_ennreal p _ _ _ _ _ _)
      · have hempty : C v = ∅ := by
          ext ω
          simp only [C, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h ↦ hv ⟨h.1, h.2.1⟩
        simp only [ite_eq_right hv, hempty, measure_empty, le_refl]
    _ = _ := by
      rw [tsum_height_interval]
      apply Finset.sum_congr rfl
      intro t _
      apply tsum_congr
      intro v
      by_cases hv : v i = t
      · simp only [hv]
      · simp only [ite_eq_right hv]

private lemma slab_tsum_finsetSum {X J : Type*} (s : Finset J) (f : J → X → ℝ≥0∞) :
    (∑' x, ∑ j ∈ s, f j x) = ∑ j ∈ s, ∑' x, f j x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp only [Finset.sum_insert hj, ENNReal.tsum_add, ih]

/-- The double plane sum factors exactly by transverse stationarity and the
proved plane reversal. ENNReal permits all sums, including infinite values. -/
theorem slab_double_plane_sum {d : ℕ} (p : unitInterval) (i : Fin d)
    (m t j : ℤ) (x : Vertex d) :
    (∑' u : Vertex d, if u i = j then ∑' v : Vertex d, if v i = t then
      percolation d p (connectionToSetEvent (finiteHeightSlab i m t) x {v}) *
        percolation d p (connectionToSetEvent (finiteHeightSlab i m t) u {v}) else 0 else 0) =
      (∑' v : Vertex d, if v i = t then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m t) x {v}) else 0) *
          slabPioneerMass p i m t j t := by
  calc
    _ = ∑' u : Vertex d, ∑' v : Vertex d, if v i = t then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m t) x {v}) *
          (if u i = j then percolation d p
            (connectionToSetEvent (finiteHeightSlab i m t) u {v}) else 0) else 0 := by
      apply tsum_congr
      intro u
      by_cases hu : u i = j
      · simp only [ite_eq_left hu]
      · simp [hu]
    _ = ∑' v : Vertex d, ∑' u : Vertex d, if v i = t then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m t) x {v}) *
          (if u i = j then percolation d p
            (connectionToSetEvent (finiteHeightSlab i m t) u {v}) else 0) else 0 :=
      ENNReal.tsum_comm
    _ = ∑' v : Vertex d, (if v i = t then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m t) x {v}) else 0) *
          slabPioneerMass p i m t j t := by
      apply tsum_congr
      intro v
      by_cases hv : v i = t
      · simp only [ite_eq_left hv]
        rw [ENNReal.tsum_mul_left, slab_plane_sum_reverse, hv]
      · simp only [ite_eq_right hv, tsum_zero, zero_mul]
    _ = _ := ENNReal.tsum_mul_right

/-- Literal source prop.A.basic(2), eq.A.convolution. The endpoints and domains
are the actual source events; no convolution or finite-mass input is assumed.
The stronger all-integer statement uses empty events for endpoints outside S. -/
theorem slabPioneerMass_convolution {d : ℕ} (p : unitInterval) (i : Fin d)
    (m n k j : ℤ) :
    slabPioneerMass p i m n k j ≤
      ∑ t ∈ Finset.Icc (max k j) n,
        slabPioneerMass p i m t k t * slabPioneerMass p i m t j t := by
  calc
    _ ≤ ∑' u : Vertex d, ∑ t ∈ Finset.Icc (max k j) n,
        if u i = j then ∑' v : Vertex d, if v i = t then
          percolation d p (connectionToSetEvent (finiteHeightSlab i m t) (Pi.single i k) {v}) *
            percolation d p (connectionToSetEvent (finiteHeightSlab i m t) u {v}) else 0 else 0 := by
      unfold slabPioneerMass
      apply ENNReal.tsum_le_tsum
      intro u
      by_cases hu : u i = j
      · simp only [ite_eq_left hu]
        simpa only [Pi.single_eq_same, hu] using
          slab_connection_maximum_bk p i m n (Pi.single i k) u
      · simp [hu]
    _ = ∑ t ∈ Finset.Icc (max k j) n, ∑' u : Vertex d,
        if u i = j then ∑' v : Vertex d, if v i = t then
          percolation d p (connectionToSetEvent (finiteHeightSlab i m t) (Pi.single i k) {v}) *
            percolation d p (connectionToSetEvent (finiteHeightSlab i m t) u {v}) else 0 else 0 :=
      slab_tsum_finsetSum _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      exact slab_double_plane_sum p i m t j (Pi.single i k)

end NearCritical
