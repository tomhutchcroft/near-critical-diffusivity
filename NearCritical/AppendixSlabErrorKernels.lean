module

public import NearCritical.Section8SourceFRD
public import NearCritical.Section8TwoSidedDistance

/-! Actual connection envelopes needed by the Appendix A error diagrams. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set Section8 AppendixVariance
open scoped Classical

/-- The distance to the closer of the two ends of an integer slab. -/
def appendixSlabDepth {d : ℕ} (i : Fin d) (a b : ℤ) (u : Vertex d) : ℕ :=
  min (u i - a).toNat (b - u i).toNat

/-- A point on either end plane bounds the slab depth by its lattice
distance. This holds even for branch points outside the slab. -/
theorem appendixSlabDepth_le_end_distance {d : ℕ} (i : Fin d) (a b : ℤ) (x u : Vertex d)
    (hx : x i = a ∨ x i = b) : appendixSlabDepth i a b u ≤ linfDist x u := by
  have hi : (x i - u i).natAbs ≤ linfDist x u :=
    Finset.le_sup (f := fun j => (x j - u j).natAbs) (Finset.mem_univ i)
  unfold appendixSlabDepth
  rcases hx with hx | hx
  · have h : (u i - a).toNat ≤ (x i - u i).natAbs := by omega
    exact (min_le_left _ _).trans (h.trans hi)
  · have h : (b - u i).toNat ≤ (x i - u i).natAbs := by omega
    exact (min_le_right _ _).trans (h.trans hi)

/-- The distance between points on opposite slab ends is at least its height. -/
theorem appendixSlab_height_le_distance {d : ℕ} (i : Fin d) (a : ℤ) (h : ℕ)
    (x w : Vertex d) (hx : x i = a) (hw : w i = a + (h : ℤ)) : h ≤ linfDist x w := by
  have hi : (x i - w i).natAbs ≤ linfDist x w :=
    Finset.le_sup (f := fun j => (x j - w j).natAbs) (Finset.mem_univ i)
  omega

private theorem slab_depth_cast {d : ℕ} (i : Fin d) {a b : ℤ} (u : Vertex d)
    (ha : a ≤ u i) (hb : u i ≤ b) :
    (appendixSlabDepth i a b u : ℝ) = min ((u i : ℝ) - a) ((b : ℝ) - u i) := by
  unfold appendixSlabDepth
  have h₁ : (((u i - a).toNat : ℕ) : ℝ) = (u i : ℝ) - a := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr ha), Int.cast_sub]
  have h₂ : (((b - u i).toNat : ℕ) : ℝ) = (b : ℝ) - u i := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hb), Int.cast_sub]
  rw [Nat.cast_min, h₁, h₂]

private theorem slab_depth_halfspace {d : ℕ} (Q : Finset (Vertex d)) (i : Fin d) {a b : ℤ}
    (hQ : ∀ u ∈ Q, a ≤ u i ∧ u i ≤ b) (u : Vertex d) (hu : u ∈ Q) :
    ∃ (cut : ℤ) (s : Bool), (Q : Set (Vertex d)) ⊆ coordinateHalfSpace i cut s ∧
      coordinateDepth i cut s u = (appendixSlabDepth i a b u : ℝ) := by
  obtain ⟨ha, hb⟩ := hQ u hu
  rw [slab_depth_cast i u ha hb]
  by_cases hc : (u i : ℝ) - a ≤ (b : ℝ) - u i
  · refine ⟨a, true, ?_, by simp [coordinateDepth, min_eq_left hc]⟩
    intro v hv
    change 0 ≤ coordinateDepth i a true v
    have hb' : (a : ℝ) ≤ (v i : ℝ) := by
      exact_mod_cast (hQ v hv).1
    simpa [coordinateDepth, sub_nonneg] using hb'
  · refine ⟨b, false, ?_, by simp [coordinateDepth, min_eq_right (le_of_not_ge hc)]⟩
    intro v hv
    change 0 ≤ coordinateDepth i b false v
    have hb' : (v i : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (hQ v hv).2
    simpa [coordinateDepth, sub_nonneg] using hb'

private theorem distance_negative_power_le_shift {d : ℕ} (x y : Vertex d) (e : ℕ) :
    (max 1 (latticeDistance x y)) ^ (-(e : ℝ)) ≤
      (2 : ℝ) ^ e / ((linfDist x y + 1 : ℕ) : ℝ) ^ e := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_eq_one_div]
  have hs : (1 : ℝ) ≤ ((linfDist x y + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ linfDist x y + 1 by omega)
  simpa only [Nat.cast_one, max_eq_right hs] using literal_kernel_le (r := 1) le_rfl x y e

/-- The one-sided and two-sided slab kernels, with the same depth at the
branch vertex. The root of the two-sided estimate may lie on either end. -/
theorem appendix_slab_error_kernels {d : ℕ} (hd : 1 ≤ d) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B) :
    ∃ U V : ℝ, 0 ≤ U ∧ 0 ≤ V ∧ ∀ (Q : Finset (Vertex d)) (i : Fin d) (a b : ℤ),
      (∀ u ∈ Q, a ≤ u i ∧ u i ≤ b) →
      let P (x y : Vertex d) := (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y})
      (∀ u ∈ Q, ∀ v ∈ Q, P v u ≤ V * (1 + (appendixSlabDepth i a b u : ℝ)) /
        ((linfDist v u + 1 : ℕ) : ℝ) ^ (d - 1)) ∧
      (∀ x ∈ Q, x i = a ∨ x i = b → ∀ u ∈ Q,
        P x u ≤ U * (1 + (appendixSlabDepth i a b u : ℝ)) / ((linfDist x u + 1 : ℕ) : ℝ) ^ d) := by
  let J : ℝ := 4 * C + ((2 * (d : ℝ)) * (4 * C * (A + B) * (9 : ℝ) ^ (d - 1)) * (2 * C)) *
    (4 : ℝ) ^ d
  let V : ℝ := (2 * C) * (2 : ℝ) ^ (d - 1)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨J * (2 : ℝ) ^ d, V, by positivity, by dsimp [V]; positivity, ?_⟩
  intro Q i a b hQ P
  have hlow : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace i a true := by
    intro w hw
    change 0 ≤ coordinateDepth i a true w
    have hb' : (a : ℝ) ≤ (w i : ℝ) := by
      exact_mod_cast (hQ w hw).1
    simpa [coordinateDepth, sub_nonneg] using hb'
  have hupp : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace i b false := by
    intro w hw
    change 0 ≤ coordinateDepth i b false w
    have hb' : (w i : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (hQ w hw).2
    simpa [coordinateDepth, sub_nonneg] using hb'
  constructor
  · intro u hu v hv
    obtain ⟨cut, s, hs, hdepth⟩ := slab_depth_halfspace Q i hQ u hu
    have hp := restricted_halfSpace_one_sided C hC panis i cut s (Q : Set (Vertex d)) hs u v hu hv
    have he : (1 : ℝ) - (d : ℝ) = -((d - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hd, Nat.cast_one]
      ring
    rw [hdepth, he, connectionToSetEvent_singleton_symm (Q : Set (Vertex d)) u v] at hp
    have hb := distance_negative_power_le_shift v u (d - 1)
    rw [latticeDistance_comm v u] at hb
    refine hp.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_)
    dsimp only [V]
    ring
  · intro x hx hxface u hu
    obtain ⟨cut, s, hs, hdepth⟩ := slab_depth_halfspace Q i hQ u hu
    have hp : P x u ≤ J * (1 + (appendixSlabDepth i a b u : ℝ)) *
        (max 1 (latticeDistance x u)) ^ (-(d : ℝ)) := by
      rcases hxface with ha | hb
      · have ht := two_halfspaces_connection_le_distance hd C A B hC hA hB panis arm second
          Q x u hx hu i i a cut true s hlow hs
        rw [hdepth] at ht
        simpa [P, J, coordinateDepth, ha] using ht
      · have ht := two_halfspaces_connection_le_distance hd C A B hC hA hB panis arm second
          Q x u hx hu i i b cut false s hupp hs
        rw [hdepth] at ht
        simpa [P, J, coordinateDepth, hb] using ht
    exact hp.trans ((mul_le_mul_of_nonneg_left (distance_negative_power_le_shift x u d)
      (by positivity)).trans_eq (by ring))

end NearCritical
