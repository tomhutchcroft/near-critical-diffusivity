module

public import NearCritical.SplitCrossTreePattern
public import NearCritical.ThreePointDiagram

/-! Positions beyond a branch's exit tip avoid its moat. Linear separation
between branches keeps those positions out of the other moats. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open scoped Classical

theorem latticeDistance_eq_vertex_dist {d : ℕ} (x y : Vertex d) :
    latticeDistance x y = dist x y := by
  unfold latticeDistance
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    simpa only [vertexReal, Real.dist_eq, Int.dist_eq] using dist_le_pi_dist x y i
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    simpa only [vertexReal, Real.dist_eq, Int.dist_eq] using
      dist_le_pi_dist (vertexReal x) (vertexReal y) i

theorem dist_starTip_center {d : ℕ} (b : Vertex d) (i : Fin d) (n : ℕ) :
    dist (starTip b i n) b = (n : ℝ) := by
  apply le_antisymm
  · apply (dist_pi_le_iff (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).mpr
    intro j
    by_cases hj : j = i
    · subst j
      simp [Int.dist_eq, starTip, coordinateRay, Pi.add_apply, Int.cast_add, abs_of_nonneg]
    · simp [Int.dist_eq, starTip, coordinateRay, Pi.add_apply, hj]
  · simpa [Int.dist_eq, starTip, coordinateRay, Pi.add_apply, Int.cast_add, abs_of_nonneg] using
      dist_le_pi_dist (starTip b i n) b i

theorem starTip_same_ray_gap {d : ℕ} (b : Vertex d) (i : Fin d) (n k : ℕ) :
    (n : ℝ) - (k : ℝ) ≤ latticeDistance (starTip b i n) (starTip b i k) := by
  rw [latticeDistance_eq_vertex_dist]
  refine le_trans ?_ (dist_le_pi_dist (starTip b i n) (starTip b i k) i)
  rw [Int.dist_eq]
  have hEq : ((starTip b i n i : ℤ) : ℝ) - ((starTip b i k i : ℤ) : ℝ) =
      (n : ℝ) - (k : ℝ) := by simp [starTip, coordinateRay, Pi.add_apply, Int.cast_add]
  rw [hEq]
  exact le_abs_self _

theorem starTip_other_ray_gap {d : ℕ} (b : Vertex d) {i j : Fin d} (hij : i ≠ j)
    (n k : ℕ) :
    (n : ℝ) ≤ latticeDistance (starTip b i n) (starTip b j k) := by
  rw [latticeDistance_eq_vertex_dist]
  refine le_trans ?_ (dist_le_pi_dist (starTip b i n) (starTip b j k) i)
  simp [Int.dist_eq, starTip, coordinateRay, Pi.add_apply, Int.cast_add, hij, abs_of_nonneg]

theorem starTip_past_exit_not_mem_moat {d : ℕ} (b : Vertex d) (axes : Finset (Fin d))
    (i : Fin d) (R r k : ℕ) (hr : 0 < r) :
    starTip b i (R + r + k) ∉ branchMoatVertices b axes R r := by
  intro h
  rcases Finset.mem_union.mp h with hstar | hball
  · obtain ⟨e, he, hEq⟩ := Finset.mem_image.mp hstar
    obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp he
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hej
    change starTip b j l = starTip b i (R + r + k) at hEq
    have hl' := Finset.mem_range.mp hl
    by_cases hij : i = j
    · subst j
      have he := coordinateRay_injective i (add_left_cancel hEq)
      omega
    · exact starTip_distinct_rays b hij (by omega) hEq.symm
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

theorem moatVertex_dist_center_le {d : ℕ} {b x : Vertex d} {axes : Finset (Fin d)}
    {R r : ℕ} (hx : x ∈ branchMoatVertices b axes R r) (i : Fin d) :
    dist x b ≤ ((R + r + 1 : ℕ) : ℝ) := by
  have he : (x, i) ∈ branchGuardBonds b axes R r := by
    exact Finset.mem_biUnion.mpr ⟨x, hx, (External.mem_vertexIncidentBonds _ _).mpr (Or.inl rfl)⟩
  have hm := (branchGuard_endpoints b axes R r he).1
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  apply (dist_pi_le_iff (Nat.cast_nonneg _)).mpr
  intro j
  have hb := mem_centeredBox.mp hu j
  have hcast : ((|u j| : ℤ) : ℝ) ≤ (((R + r + 1 : ℕ) : ℤ) : ℝ) :=
    Int.cast_le.mpr (abs_le.mpr hb)
  rw [Int.dist_eq]
  simpa [Pi.add_apply, Int.cast_add, Int.cast_abs] using hcast

/-- For a separated family of branches the whole outward segment remains in
the common outside graph as soon as its vertices are in the ambient tube. -/
theorem outwardRay_mem_treeOutside {d : ℕ} {ι : Type*} (I : Finset ι)
    (b : ι → Vertex d) (axes : Finset (Fin d)) (R r ρ : ℕ) (hr : 0 < r)
    {v : ι} (hv : v ∈ I) (i : Fin d)
    (hsep : ∀ w ∈ I, v ≠ w →
      ((R + r + ρ : ℕ) : ℝ) + ((R + r + 1 : ℕ) : ℝ) < dist (b v) (b w))
    (U : Finset (Vertex d)) (hU : ∀ k ≤ ρ, starTip (b v) i (R + r + k) ∈ U) :
    ∀ k ≤ ρ, starTip (starTip (b v) i (R + r)) i k ∈ U \ treeMoatVertices I b axes R r := by
  intro k hk
  rw [← starTip_add]
  refine Finset.mem_sdiff.mpr ⟨hU k hk, ?_⟩
  intro hm
  obtain ⟨w, hw, hmw⟩ := Finset.mem_biUnion.mp hm
  by_cases h : v = w
  · subst w
    exact starTip_past_exit_not_mem_moat (b v) axes i R r k hr hmw
  · have h₁ := dist_starTip_center (b v) i (R + r + k)
    have h₂ := moatVertex_dist_center_le hmw i
    have htri := dist_triangle (b v) (starTip (b v) i (R + r + k)) (b w)
    rw [dist_comm (b v) (starTip (b v) i (R + r + k))] at htri
    have hk' : ((R + r + k : ℕ) : ℝ) ≤ ((R + r + ρ : ℕ) : ℝ) := by
      exact_mod_cast (by omega : R + r + k ≤ R + r + ρ)
    linarith [hsep w hw h]

end NearCritical.SplitCrossDirect
