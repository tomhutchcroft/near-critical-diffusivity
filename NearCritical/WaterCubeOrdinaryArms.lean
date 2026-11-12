module
public import NearCritical.WaterCubeFaceBounds
public import NearCritical.BulkArmGeometry

/-! Source eq.onearm_low: actual finite-face paths give ordinary extrinsic
arms. The cited ordinary-arm estimate is an explicit STANDARD input, not an
assumed finite-face or energy bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

/-- Distance in the distinguished coordinate to the TARGET face. -/
def waterCubeTargetDepth {d : ℕ} (i : Fin d) (r : ℕ)
    (upper : Bool) (x : Vertex d) : ℕ :=
  waterCubeOppositeDepth i r (!upper) x

lemma waterCube_targetDepth_le_height {d : ℕ} (i : Fin d) (r R : ℕ)
    (upper : Bool) (x : DomainVertex (waterCube d i r R)) :
    waterCubeTargetDepth i r upper x.val ≤ 2 * r + 1 := by
  have hx := waterCube_sitesPlus_coordinate i r R x
  cases upper <;> simp only [waterCubeTargetDepth, waterCubeOppositeDepth,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- Every point on the chosen face has at least the exact coordinate-depth
sup distance from x, also when x lies in the enlarged issued support. -/
lemma waterCube_face_dist_ge_targetDepth {d : ℕ} (i : Fin d) (r R : ℕ)
    (upper : Bool) (x y : DomainVertex (waterCube d i r R))
    (hy : y ∈ (if upper then positiveFace _ i else negativeFace _ i)) :
    (waterCubeTargetDepth i r upper x.val : ℝ) ≤ dist x.val y.val := by
  have hx := waterCube_sitesPlus_coordinate i r R x
  have hp := dist_le_pi_dist x.val y.val i
  rw [Int.dist_eq] at hp
  cases upper
  · have hyc := rectangularBox_negativeFace_coordinate
      (fun j => if j = i then r else R) i hy
    simp only [ite_true] at hyc
    have hm : ((waterCubeTargetDepth i r false x.val : ℕ) : ℤ) = x.val i + (r : ℤ) := by
      simp only [waterCubeTargetDepth, waterCubeOppositeDepth, Bool.not_false, ite_true]
      omega
    have hmr : (waterCubeTargetDepth i r false x.val : ℝ) = (x.val i : ℝ) + (r : ℝ) := by
      exact_mod_cast hm
    rw [hmr]
    have hn : (0 : ℝ) ≤ (x.val i : ℝ) + (r : ℝ) := by
      exact_mod_cast (show 0 ≤ x.val i + (r : ℤ) by omega)
    rw [hyc, Int.cast_neg, Int.cast_natCast, sub_neg_eq_add, abs_of_nonneg hn] at hp
    exact hp
  · have hyc := rectangularBox_positiveFace_coordinate
      (fun j => if j = i then r else R) i hy
    simp only [ite_true] at hyc
    have hm : ((waterCubeTargetDepth i r true x.val : ℕ) : ℤ) = (r : ℤ) + 1 - x.val i := by
      simp only [waterCubeTargetDepth, waterCubeOppositeDepth, Bool.not_true, Bool.false_eq_true, ite_false]
      omega
    have hmr : (waterCubeTargetDepth i r true x.val : ℝ) = (r : ℝ) + 1 - (x.val i : ℝ) := by
      exact_mod_cast hm
    rw [hmr]
    rw [hyc, Int.cast_add, Int.cast_one, Int.cast_natCast, abs_of_nonpos (by exact_mod_cast
      (show x.val i - ((r : ℤ) + 1) ≤ 0 by omega))] at hp
    linarith

/-- The genuine finite-domain face event is an ordinary full-lattice arm
beyond every radius strictly smaller than the exact target depth. -/
theorem waterCube_face_subset_extrinsicArm {d : ℕ} (i : Fin d) (r R : ℕ)
    (upper : Bool) (x : DomainVertex (waterCube d i r R))
    {t : ℝ} (ht : t < waterCubeTargetDepth i r upper x.val) :
    waterCubeFaceConnectionEvent i r R upper x ⊆ extrinsicRadiusArmEvent x.val t := by
  intro ω hω
  obtain ⟨_, y, ⟨z, hz, rfl⟩, _, hp⟩ := latticeBoundaryConnectionEvent_subset
    (waterCube d i r R) x _ hω
  refine ⟨z.val, ht.trans_le (waterCube_face_dist_ge_targetDepth i r R upper x z hz), ?_⟩
  have hle : restrictedGraph ω (sitesPlus (waterCube d i r R) : Set (Vertex d)) ≤ openGraph ω :=
    fun _ _ h => h.1
  exact SimpleGraph.Reachable.mono hle hp

/-- Named STANDARD ordinary-arm critical-window input (source eq.onearm_super,
with radius n/2 and constants rescaled). No finite-face event appears here.
Subcritical p are included via ordinary parameter monotonicity. -/
def OrdinaryArmWindowInput (d : ℕ) (C : ℝ) : Prop :=
  ∀ (p : unitInterval) (x : Vertex d) (n : ℕ), 1 ≤ n →
    (p : ℝ) ≤ (criticalPoint d : ℝ) + ((n : ℝ) ^ 2)⁻¹ →
    (percolation d p).real (extrinsicRadiusArmEvent x ((n : ℝ) / 2)) ≤ C / (n : ℝ) ^ 2

/-- NEW finite-face near-arm estimate, including zero depth. The constant is
uniform in both faces, the transverse size and the endpoint. -/
theorem waterCube_face_probability_le_ordinary {d : ℕ} {C : ℝ} (hC : 1 ≤ C)
    (ordinary : OrdinaryArmWindowInput d C) (p : unitInterval)
    (i : Fin d) (r R : ℕ) (upper : Bool) (x : DomainVertex (waterCube d i r R))
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ) + (((2 * r + 1 : ℕ) : ℝ) ^ 2)⁻¹) :
    (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
      4 * C / (waterCubeTargetDepth i r upper x.val + 1 : ℝ) ^ 2 := by
  let m := waterCubeTargetDepth i r upper x.val
  by_cases hm : m = 0
  · have hprob : (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤ 1 :=
      measureReal_le_one
    simpa only [← show m = waterCubeTargetDepth i r upper x.val from rfl, hm,
      Nat.cast_zero, zero_add, one_pow, div_one] using hprob.trans (by linarith : (1 : ℝ) ≤ 4 * C)
  · have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    have hmh : (m : ℝ) ≤ (2 * r + 1 : ℕ) := by
      exact_mod_cast waterCube_targetDepth_le_height i r R upper x
    have hwindow : (p : ℝ) ≤ (criticalPoint d : ℝ) + ((m : ℝ) ^ 2)⁻¹ := by
      have hi : (((2 * r + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ ((m : ℝ) ^ 2)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hmpos)
          (show (m : ℝ) ^ 2 ≤ ((2 * r + 1 : ℕ) : ℝ) ^ 2 by nlinarith)
      linarith
    have hbound := ordinary p x.val m (by omega) hwindow
    have hle : (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
        C / (m : ℝ) ^ 2 := by
      apply (measureReal_mono (waterCube_face_subset_extrinsicArm i r R upper x
        (show (m : ℝ) / 2 < waterCubeTargetDepth i r upper x.val by change (m : ℝ) / 2 < m; linarith))).trans hbound
    apply hle.trans
    change C / (m : ℝ) ^ 2 ≤ 4 * C / (m + 1 : ℝ) ^ 2
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    apply (div_le_div_iff₀ (sq_pos_of_pos hmpos) (by positivity)).mpr
    have hsq : (m + 1 : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ C by linarith)]

end NearCritical
