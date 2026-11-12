module

public import NearCritical.Section7LowerWaterAll
public import NearCritical.WaterCubeOrdinaryArms

/-! Source `lem.arm.2dspanning`, upper half of `eq.arm.2dspanning`, from the
cited ordinary one-arm bound.

For a root `x` in `Lambda_{n/16}` a `2d`-spanning component reaches a face at
sup-distance at least `N - N/16 > N/2` from `x`, so the spanning event is
contained in the ordinary extrinsic arm event of radius `N/2`. The existing
named input `OrdinaryArmWindowInput` then gives `P[spanning] <= C' n^(-2)`.

Consequently Section 7 needs from `lem.arm.2dspanning` only its LOWER bound
(`Arm2dSpanningLower`), which is the paper's new argument.

 -/
@[expose] public section
noncomputable section
namespace NearCritical.Section7
open MeasureTheory
open scoped Classical

/-- Lower half of `eq.arm.2dspanning`: the new part of source `lem.arm.2dspanning`. -/
def Arm2dSpanningLower (d : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d (N/16) →
    c/(2*(N:ℝ)+1)^2 ≤ (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x)

/-- A spanning component of a root in `Lambda_{n/16}` is an ordinary arm of
radius `N/2`. -/
theorem spanning_subset_extrinsicArm {d : ℕ} (i : Fin d) {N : ℕ} (hN : 1 ≤ N)
    {x : Vertex d} (hx : x ∈ centeredBox d (N/16)) :
    finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x ⊆
      extrinsicRadiusArmEvent x ((N:ℝ)/2) := by
  intro ω hω
  obtain ⟨y, hy⟩ := hω (i, true)
  have hyC := (Finset.mem_inter.mp hy).1
  have hyi : y i = (N:ℤ) := by
    have h := mem_signedCubeFace_coord (Finset.mem_inter.mp hy).2
    simpa using h
  have hreach := ((mem_finiteBoxCluster ω (centeredBox d N) x y).mp hyC).2
  have hle : restrictedGraph ω (centeredBox d N : Set (Vertex d)) ≤ openGraph ω :=
    fun _ _ h => h.1
  refine ⟨y, ?_, SimpleGraph.Reachable.mono hle hreach⟩
  have hxi : x i ≤ ((N/16 : ℕ) : ℤ) := ((mem_centeredBox.mp hx) i).2
  have hxiR : ((x i : ℤ) : ℝ) ≤ ((N/16 : ℕ) : ℝ) := by
    have h : ((x i : ℤ) : ℝ) ≤ (((N/16 : ℕ) : ℤ) : ℝ) := Int.cast_le.mpr hxi
    rwa [Int.cast_natCast] at h
  have hdiv : ((N/16 : ℕ) : ℝ) ≤ (N:ℝ)/16 := Nat.cast_div_le
  have hyiR : ((y i : ℤ) : ℝ) = (N:ℝ) := by exact_mod_cast hyi
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hcoord : dist (x i) (y i) ≤ dist x y := dist_le_pi_dist x y i
  rw [Int.dist_eq] at hcoord
  have habs := neg_le_abs (((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ))
  linarith

/-- Two-sided `eq.arm.2dspanning` from its lower half and the cited ordinary
one-arm bound. -/
theorem arm2dSpanning_of_lower_and_ordinary {d : ℕ} (i : Fin d) {C : ℝ}
    (ordinary : OrdinaryArmWindowInput d C) (hlow : Arm2dSpanningLower d) :
    Arm2dSpanningStatement d := by
  obtain ⟨c, hc, hlo⟩ := hlow
  refine ⟨c, max (9*C) 1, hc, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro N x hx
  refine ⟨hlo N x hx, ?_⟩
  have hNn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hn : (0:ℝ) < (2*(N:ℝ)+1)^2 := by positivity
  by_cases hN0 : N = 0
  · subst hN0
    have h1 : (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d 0) (signedCubeFace d 0) x) ≤ 1 :=
      measureReal_le_one
    refine le_trans h1 ?_
    rw [le_div_iff₀ hn]
    have : (1:ℝ) ≤ max (9*C) 1 := le_max_right _ _
    simpa using this
  · have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hN2 : (0:ℝ) < (N:ℝ)^2 := by positivity
    have hpc : ((criticalPoint d : unitInterval) : ℝ) ≤
        (criticalPoint d : ℝ) + ((N:ℝ)^2)⁻¹ := by
      have : (0:ℝ) ≤ ((N:ℝ)^2)⁻¹ := by positivity
      linarith
    have hord := ordinary (criticalPoint d) x N hN hpc
    have hsub := measureReal_mono (μ := percolation d (criticalPoint d))
      (spanning_subset_extrinsicArm i hN hx) (measure_ne_top _ _)
    have hC0 : 0 ≤ C := by
      by_contra hneg
      have hlt := div_neg_of_neg_of_pos (not_le.mp hneg) hN2
      have h0 : (0:ℝ) ≤ (percolation d (criticalPoint d)).real
          (extrinsicRadiusArmEvent x ((N:ℝ)/2)) := measureReal_nonneg
      linarith
    have h9 : (2*(N:ℝ)+1)^2 ≤ 9*(N:ℝ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hN1) hNn, hN1]
    have hstep : C/(N:ℝ)^2 ≤ (9*C)/(2*(N:ℝ)+1)^2 := by
      rw [div_le_div_iff₀ hN2 hn]
      nlinarith [mul_le_mul_of_nonneg_left h9 hC0]
    exact le_trans hsub (le_trans hord (le_trans hstep
      (div_le_div_of_nonneg_right (le_max_left _ _) hn.le)))

/-- **Source `prop.lower_water`, `eq.lower_water_general`, at every scale**, from
assumption (A), `d >= 9`, the cited ordinary one-arm bound, the lower half of
`eq.arm.2dspanning`, the small-volume input and the face-reach tail. -/
theorem lower_water_general_all_of_arm_lower {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) {C : ℝ} (ordinary : OrdinaryArmWindowInput d C)
    (hlow : Arm2dSpanningLower d) (hvol : SpanningSmallVolumeInput d)
    (htail : FaceReachTail d) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
      c / (2*(r:ℝ)+1)^6 ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) :=
  lower_water_general_all_of_literal_inputs hd i hA
    (arm2dSpanning_of_lower_and_ordinary i ordinary hlow) hvol htail

end NearCritical.Section7
