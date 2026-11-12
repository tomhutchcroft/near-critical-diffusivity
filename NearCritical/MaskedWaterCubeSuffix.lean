module

public import NearCritical.WaterCubeOrdinaryArms
public import NearCritical.BulkSupercriticalBound

/-! Actual masked-law suffix bounds for arbitrary physical domains. The
connection event may be larger than the finite issued face event; only its
face-distance implication and genuine homogeneous domination are used. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- A connection in ANY restricted domain to the actual positive face is an
ordinary arm beyond every radius strictly smaller than the target depth. -/
theorem maskedWaterCube_suffix_subset_extrinsicArm {d : ℕ}
    (i : Fin d) (r R : ℕ) (S : Set (Vertex d))
    (v : DomainVertex (waterCube d i r R)) {t : ℝ}
    (ht : t < waterCubeTargetDepth i r true v.val) :
    connectionToSetEvent S v.val
      (Subtype.val '' positiveFace (waterCube d i r R) i) ⊆
        extrinsicRadiusArmEvent v.val t := by
  intro ω hω
  obtain ⟨_,y,⟨z,hz,rfl⟩,_,hvy⟩ := hω
  refine ⟨z.val,ht.trans_le (waterCube_face_dist_ge_targetDepth i r R true v z hz),?_⟩
  have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h => h.1
  exact SimpleGraph.Reachable.mono hle hvy

private lemma positive_targetDepth_of_base {d : ℕ} (i : Fin d) (r R : ℕ)
    (v : Vertex d) (hv : v ∈ waterCube d i r R) :
    1 ≤ waterCubeTargetDepth i r true v := by
  have hvi := (mem_rectangularBox.mp hv) i
  simp only [ite_true] at hvi
  simp only [waterCubeTargetDepth,waterCubeOppositeDepth,Bool.not_true,
    Bool.false_eq_true,ite_false]
  omega

/-- The actual bulk-law suffix to the positive face, including the full slab
suffix, is bounded by the named ordinary-arm input. No finite-face event
probability estimate or inside-U domain hypothesis is used. -/
theorem maskedWaterCube_suffix_probability_le_ordinary {d : ℕ} {Co : ℝ}
    (ordinary : OrdinaryArmWindowInput d Co) (p q : unitInterval) (hqp : q ≤ p)
    (i : Fin d) (r R : ℕ) (δ : ℝ) (S : Set (Vertex d))
    (v : Vertex d) (hv : v ∈ waterCube d i r R)
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ)+(((2*r+1 : ℕ) : ℝ)^2)⁻¹) :
    (bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).real
      (connectionToSetEvent S v (Subtype.val '' positiveFace (waterCube d i r R) i)) ≤
        Co/(waterCubeTargetDepth i r true v : ℝ)^2 := by
  let D := waterCubeTargetDepth i r true v
  let x : DomainVertex (waterCube d i r R) := ⟨v,base_mem_sitesPlus hv⟩
  have hD : 1 ≤ D := positive_targetDepth_of_base i r R v hv
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hDH : (D : ℝ) ≤ (2*r+1 : ℕ) := by
    exact_mod_cast waterCube_targetDepth_le_height i r R true x
  have hwindow : (p : ℝ) ≤ (criticalPoint d : ℝ)+((D : ℝ)^2)⁻¹ := by
    have hinv : (((2*r+1 : ℕ) : ℝ)^2)⁻¹ ≤ ((D : ℝ)^2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hDpos)
        (show (D : ℝ)^2 ≤ ((2*r+1 : ℕ) : ℝ)^2 by nlinarith)
    linarith
  have hsub : connectionToSetEvent S v
      (Subtype.val '' positiveFace (waterCube d i r R) i) ⊆
        extrinsicRadiusArmEvent v ((D : ℝ)/2) :=
    maskedWaterCube_suffix_subset_extrinsicArm i r R S x
      (by change (D : ℝ)/2 < D; linarith)
  have hdom : (bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).real
      (connectionToSetEvent S v (Subtype.val '' positiveFace (waterCube d i r R) i)) ≤
      (percolation d p).real
        (connectionToSetEvent S v (Subtype.val '' positiveFace (waterCube d i r R) i)) := by
    rw [bulkPercolation_eq_masked]
    exact maskedPercolation_event_real_le_homogeneous _ p q p le_rfl hqp
      (measurableSet_connectionToSetEvent _ _ _) (connectionToSetEvent_increasing _ _ _)
  exact hdom.trans ((measureReal_mono hsub).trans (ordinary p v D hD hwindow))

end NearCritical
