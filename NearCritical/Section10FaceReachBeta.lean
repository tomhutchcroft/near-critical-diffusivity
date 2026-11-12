module

public import NearCritical.Section10CrossAllSpanning

/-! The constant `beta`: a root near the centre reaches a split face only by a
long arm.

* `cluster_meets_splitFace_le`: for `t >= 8` and a root `x` in
  `centeredBox d ((t-1)/32)`, at `p_c`,
  `P[C(x) meets a split face of the origin typical cube] <= C / (t/4)^2`,
  from the cited ordinary one-arm window input (`t/4` is the natural-number
  quotient).
* `crossAll_lower_failure_numeric`: the lower-count failure on the all-faces
  crossing event with both constants in place:
  `P[crossAll and some split face has < b points]
      <= 4 d floor(b) (C/t^2) (C/(t/4)^2)`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem cluster_meets_splitFace_le {d : ℕ} {C : ℝ} (ordinary : OrdinaryArmWindowInput d C)
    (t : ℕ) (ht : 8 ≤ t) {x : Vertex d} (hx : x ∈ centeredBox d ((t - 1) / 32))
    (i : (Fin d × Bool) × Bool) :
    (percolation d (criticalPoint d)).real
      {ω | (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
        typPatch t (0 : Vertex d) i).Nonempty} ≤ C / ((t / 4 : ℕ) : ℝ) ^ 2 := by
  have hn : 1 ≤ t / 4 := by omega
  obtain ⟨n, hn4⟩ : ∃ n, t / 4 = n := ⟨_, rfl⟩
  rw [hn4] at hn ⊢
  have hsub : {ω : Configuration d | (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
        typPatch t (0 : Vertex d) i).Nonempty} ⊆
      extrinsicRadiusArmEvent x ((n : ℝ) / 2) := by
    rintro ω ⟨y, hy⟩
    obtain ⟨hyC, hyP⟩ := Finset.mem_inter.mp hy
    obtain ⟨⟨j, s⟩, pl⟩ := i
    have hyS : y ∈ typicalSplitFace t (0 : Vertex d) (j, s) pl := hyP
    obtain ⟨hface, _⟩ := Finset.mem_filter.mp hyS
    obtain ⟨_, hyj⟩ := Finset.mem_filter.mp hface
    have hyj' : y j = if s then (((t - 1) / 2 : ℕ) : ℤ) else -(((t - 1) / 2 : ℕ) : ℤ) := by
      simpa using hyj
    have hxj := mem_centeredBox.mp hx j
    have hreach : (openGraph ω).Reachable x y :=
      SimpleGraph.Reachable.mono
        (show restrictedGraph ω (typicalCube t (0 : Vertex d) : Set (Vertex d)) ≤ openGraph ω from
          fun _ _ h => h.1) ((mem_finiteBoxCluster ω _ x y).mp hyC).2
    refine ⟨y, ?_, hreach⟩
    have hcoord : dist (x j) (y j) ≤ dist x y := dist_le_pi_dist x y j
    rw [Int.dist_eq] at hcoord
    have hint : (n : ℤ) < 2 * |x j - y j| := by
      cases s
      · simp only [Bool.false_eq_true, if_false] at hyj'
        have : (0:ℤ) ≤ x j - y j := by omega
        rw [abs_of_nonneg this]
        omega
      · simp only [if_true] at hyj'
        have : x j - y j ≤ 0 := by omega
        rw [abs_of_nonpos this]
        omega
    have hreal : ((n : ℤ) : ℝ) < ((2 * |x j - y j| : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at hreal
    linarith
  refine (measureReal_mono (μ := percolation d (criticalPoint d)) hsub
    (measure_ne_top _ _)).trans ?_
  refine ordinary (criticalPoint d) x n hn ?_
  have : (0:ℝ) ≤ (((n : ℝ)) ^ 2)⁻¹ := by positivity
  linarith

/-- **Lower split-face counts on the crossing event, with numerical constants.** -/
theorem crossAll_lower_failure_numeric {d : ℕ} {C : ℝ} (ordinary : OrdinaryArmWindowInput d C)
    (t : ℕ) (ht : 8 ≤ t) {x : Vertex d} (hx : x ∈ centeredBox d ((t - 1) / 32))
    (hxQ : x ∈ typicalCube t (0 : Vertex d)) {b : ℝ} (hb : 0 ≤ b) :
    (percolation d (criticalPoint d)).real (crossAll t t x ∩ {ω | ¬ ∀ i : (Fin d × Bool) × Bool,
        b ≤ ((finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
          typPatch t (0 : Vertex d) i).card : ℝ)}) ≤
      4 * (d : ℝ) * ((⌊b⌋₊ : ℝ) * (C / (t : ℝ) ^ 2) * (C / ((t / 4 : ℕ) : ℝ) ^ 2)) := by
  have ht1 : 1 ≤ t := by omega
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  exact crossAll_lower_failure (criticalPoint d) t ht1 t hxQ (r := (t : ℝ) / 2)
    (by linarith) hb (fun y => ordinaryArm_alpha ordinary t ht1 y)
    (fun i => cluster_meets_splitFace_le ordinary t ht hx i)

end NearCritical.Section10
