module

public import NearCritical.SplitCrossFinitePattern
public import NearCritical.SplitCrossBranchMargins
public import NearCritical.BulkDomain

/-! Each branch star has short continuations in its tip balls. The prescribed
bonds include every bond incident to an interior vertex of these continuations. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical

theorem starTip_add {d : ℕ} (b : Vertex d) (i : Fin d) (R k : ℕ) :
    starTip b i (R + k) = starTip (starTip b i R) i k := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [starTip, coordinateRay, Pi.add_apply, Nat.cast_add, add_assoc]
  · simp [starTip, coordinateRay, Pi.add_apply, hj]

private theorem bondTip_eq_add_ray {d : ℕ} (e : Bond d) :
    bondTip e = e.1 + coordinateRay e.2 1 := by
  ext j
  by_cases hj : j = e.2
  · subst j
    simp [bondTip, coordinateRay, Pi.add_apply]
  · simp [bondTip, coordinateRay, Pi.add_apply, hj]

private theorem incident_in_box {d r : ℕ} {a v : Vertex d} (hr : 0 < r)
    (hv : v ∈ translateSites a (centeredBox d (r - 1))) {e : Bond d}
    (h : e.1 = v ∨ bondTip e = v) :
    e ∈ internalBondSet (translateSites a (centeredBox d r)) := by
  have hv' : v ∈ translateSites a (centeredBox d r) := by
    have hz : (0 : Vertex d) ∈ centeredBox d 0 := by
      simp [mem_centeredBox, Pi.zero_apply]
    simpa using translatedBox_add_mem (by omega : r - 1 + 0 ≤ r) hv hz
  refine (mem_internalBondSet _ _).mpr ?_
  rcases h with hb | ht
  · refine ⟨hb ▸ hv', ?_⟩
    rw [bondTip_eq_add_ray, hb]
    exact translatedBox_add_mem (by omega : r - 1 + 1 ≤ r) hv
      (coordinateRay_mem_centeredBox e.2 le_rfl)
  · refine ⟨?_, ht ▸ hv'⟩
    have hneg : -coordinateRay e.2 1 ∈ centeredBox d 1 := by
      apply mem_centeredBox.mpr
      intro i
      have hh := mem_centeredBox.mp (coordinateRay_mem_centeredBox e.2 (le_rfl : 1 ≤ 1)) i
      simp only [Pi.neg_apply]
      omega
    have hsum : v + -coordinateRay e.2 1 = e.1 := by
      rw [← ht, bondTip_eq_add_ray, add_assoc, add_neg_cancel, add_zero]
    rw [← hsum]
    exact translatedBox_add_mem (by omega : r - 1 + 1 ≤ r) hv hneg

/-- The non-tip vertices of the extended star and the interiors of its
tip balls are removed from the outside graph. -/
def branchMoatVertices {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R r : ℕ) :
    Finset (Vertex d) :=
  starNonTipVertices b axes (R + r) ∪ axes.biUnion (fun i =>
    translateSites (starTip b i R) (centeredBox d (r - 1)))

/-- Exactly the bonds incident to the removed vertices are prescribed. -/
def branchGuardBonds {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R r : ℕ) :
    Finset (Bond d) :=
  (branchMoatVertices b axes R r).biUnion External.vertexIncidentBonds

theorem branchGuardBonds_card_le {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R r : ℕ) :
    (branchGuardBonds b axes R r).card ≤
      (axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d) * (2 * d) := by
  have hstar : (starNonTipVertices b axes (R + r)).card ≤ axes.card * (R + r) := by
    rw [← starBonds_card b axes (R + r)]
    exact Finset.card_image_le
  have hballs : (axes.biUnion (fun i =>
      translateSites (starTip b i R) (centeredBox d (r - 1)))).card ≤
        axes.card * (2 * (r - 1) + 1) ^ d := by
    refine Finset.card_biUnion_le.trans ?_
    simp [card_translateSites, card_centeredBox_exact]
  have hvertices : (branchMoatVertices b axes R r).card ≤
      axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hstar hballs)
  unfold branchGuardBonds
  calc
    _ ≤ ∑ v ∈ branchMoatVertices b axes R r, (External.vertexIncidentBonds v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ branchMoatVertices b axes R r, 2 * d :=
      Finset.sum_le_sum (fun v _ => External.card_vertexIncidentBonds_le v)
    _ = (branchMoatVertices b axes R r).card * (2 * d) := by simp
    _ ≤ _ := Nat.mul_le_mul_right (2 * d) hvertices

theorem branchExitTip_not_mem_moat {d : ℕ} (b : Vertex d) (axes : Finset (Fin d))
    (i : Fin d) (R : ℕ) {r : ℕ} (hr : 0 < r) :
    starTip b i (R + r) ∉ branchMoatVertices b axes R r := by
  intro h
  rcases Finset.mem_union.mp h with hstar | hball
  · exact starTip_not_mem_nonTip b axes i (by omega) hstar
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hball
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hj
    have hcoord := congrFun he i
    have hz' := mem_centeredBox.mp hz i
    by_cases hij : i = j
    · subst j
      simp [starTip, coordinateRay, Pi.add_apply, Nat.cast_add] at hcoord
      omega
    · simp [starTip, coordinateRay, Pi.add_apply, Nat.cast_add, hij] at hcoord
      omega

theorem branchGuard_disjoint_outside {d : ℕ} (b : Vertex d) (axes : Finset (Fin d))
    (R r : ℕ) (U : Finset (Vertex d)) :
    Disjoint (branchGuardBonds b axes R r)
      (internalBondSet (U \ branchMoatVertices b axes R r)) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨v, hv, hinc⟩ := Finset.mem_biUnion.mp he
  obtain ⟨hb, ht⟩ := (mem_internalBondSet _ _).mp he'
  rcases (External.mem_vertexIncidentBonds _ _).mp hinc with h | h
  · exact (Finset.mem_sdiff.mp hb).2 (h ▸ hv)
  · exact (Finset.mem_sdiff.mp ht).2 (h ▸ hv)

theorem branchGuard_endpoints {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R r : ℕ)
    {e : Bond d} (he : e ∈ branchGuardBonds b axes R r) :
    e.1 ∈ translateSites b (centeredBox d (R + r + 1)) ∧
      bondTip e ∈ translateSites b (centeredBox d (R + r + 1)) := by
  obtain ⟨v, hv, hinc⟩ := Finset.mem_biUnion.mp he
  apply (mem_internalBondSet _ _).mp
  refine incident_in_box (r := R + r + 1) (by omega) ?_
    ((External.mem_vertexIncidentBonds _ _).mp hinc)
  rw [show R + r + 1 - 1 = R + r by omega]
  rcases Finset.mem_union.mp hv with hstar | hball
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hstar
    obtain ⟨i, _, hqi⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hqi
    exact starTip_mem_box b i (Nat.le_of_lt (Finset.mem_range.mp hk))
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hball
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    exact translatedBox_add_mem (by omega : R + (r - 1) ≤ R + r)
      (starTip_mem_box b i le_rfl) hu

private theorem translatedBox_dist_center_le {d r : ℕ} {b x : Vertex d}
    (hx : x ∈ translateSites b (centeredBox d r)) : dist x b ≤ (r : ℝ) := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  apply (dist_pi_le_iff (Nat.cast_nonneg r : (0 : ℝ) ≤ r)).mpr
  intro i
  have hb := mem_centeredBox.mp hu i
  have hcast : ((|u i| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) :=
    Int.cast_le.mpr (abs_le.mpr hb)
  rw [Int.dist_eq]
  simpa [Pi.add_apply, Int.cast_add, Int.cast_abs] using hcast

theorem branchGuards_disjoint {d : ℕ} {b c : Vertex d} (axes : Finset (Fin d)) (R r : ℕ)
    (h : 2 * ((R + r + 1 : ℕ) : ℝ) < dist b c) :
    Disjoint (branchGuardBonds b axes R r) (branchGuardBonds c axes R r) := by
  rw [Finset.disjoint_left]
  intro e he he'
  have hb := translatedBox_dist_center_le (branchGuard_endpoints b axes R r he).1
  have hc := translatedBox_dist_center_le (branchGuard_endpoints c axes R r he').1
  have hdist := dist_triangle b e.1 c
  rw [dist_comm b e.1] at hdist
  linarith

/-- Every bond incident to a non-tip vertex of the extended star is
prescribed. -/
theorem incident_mem_branchGuard {d : ℕ} {b v : Vertex d} {axes : Finset (Fin d)}
    {R r : ℕ} {e : Bond d}
    (hv : v ∈ starNonTipVertices b axes (R + r)) (h : e.1 = v ∨ bondTip e = v) :
    e ∈ branchGuardBonds b axes R r :=
  Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_left _ hv,
    (External.mem_vertexIncidentBonds _ _).mpr h⟩

theorem extendedStarBonds_subset_branchGuard {d : ℕ}
    (b : Vertex d) (axes : Finset (Fin d)) (R r : ℕ) :
    starBonds b axes (R + r) ⊆ branchGuardBonds b axes R r := by
  intro e he
  exact incident_mem_branchGuard (Finset.mem_image.mpr ⟨e, he, rfl⟩) (Or.inl rfl)

/-- All extended-star bonds are open and all other prescribed bonds closed. -/
def branchPattern {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R r : ℕ) :
    Set (Configuration d) :=
  (branchGuardBonds b axes R r).restrict ⁻¹'
    ({(fun e : ↥(branchGuardBonds b axes R r) => decide (e.val ∈ starBonds b axes (R + r)))} :
      Set (↥(branchGuardBonds b axes R r) → Bool))

theorem branchPattern_open {d : ℕ} {b : Vertex d} {axes : Finset (Fin d)} {R r : ℕ}
    {ω : Configuration d} (hω : ω ∈ branchPattern b axes R r) :
    ∀ e ∈ starBonds b axes (R + r), ω e = true := by
  intro e he
  have hη : (branchGuardBonds b axes R r).restrict ω =
      (fun f : ↥(branchGuardBonds b axes R r) => decide (f.val ∈ starBonds b axes (R + r))) :=
    Set.mem_singleton_iff.mp hω
  have h := congrFun hη ⟨e, extendedStarBonds_subset_branchGuard b axes R r he⟩
  simpa [he, Finset.restrict] using h

theorem branchPattern_incident_open {d : ℕ} {b : Vertex d} {axes : Finset (Fin d)}
    {R r : ℕ} {ω : Configuration d} (hω : ω ∈ branchPattern b axes R r)
    {e : Bond d} {v : Vertex d} (hv : v ∈ starNonTipVertices b axes (R + r))
    (he : ω e = true) (h : e.1 = v ∨ bondTip e = v) :
    e ∈ starBonds b axes (R + r) := by
  have hη : (branchGuardBonds b axes R r).restrict ω =
      (fun f : ↥(branchGuardBonds b axes R r) => decide (f.val ∈ starBonds b axes (R + r))) :=
    Set.mem_singleton_iff.mp hω
  have hstate := congrFun hη ⟨e, incident_mem_branchGuard hv h⟩
  exact of_decide_eq_true (by simpa [Finset.restrict, he] using hstate.symm)

theorem branchPattern_reachable {d : ℕ} {b : Vertex d} {axes : Finset (Fin d)}
    {R r : ℕ} {ω : Configuration d} (hω : ω ∈ branchPattern b axes R r)
    (D : Set (Vertex d)) (hD : (translateSites b (centeredBox d (R + r)) : Set (Vertex d)) ⊆ D)
    (i : Fin d) (hi : i ∈ axes) :
    (restrictedGraph ω D).Reachable b (starTip b i (R + r)) :=
  star_reachable_restricted ω D b axes (R + r) hD (branchPattern_open hω) i hi

theorem branchPattern_with_outside_lower {d : ℕ} (p : unitInterval)
    (b : Vertex d) (axes : Finset (Fin d)) (R r : ℕ) (T : Finset (Bond d))
    (hd : Disjoint (branchGuardBonds b axes R r) T) (A : Set (T → Bool)) :
    (min (p : ℝ) (1 - (p : ℝ))) ^
        ((axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d) * (2 * d)) *
        (percolation d p).real (T.restrict ⁻¹' A) ≤
      (percolation d p).real (branchPattern b axes R r ∩ T.restrict ⁻¹' A) := by
  unfold branchPattern
  rw [prescribed_bonds_factor p _ T hd]
  exact mul_le_mul_of_nonneg_right
    (prescribed_bonds_probability_lower p _ _ (branchGuardBonds_card_le b axes R r))
    measureReal_nonneg

end NearCritical.SplitCrossDirect
