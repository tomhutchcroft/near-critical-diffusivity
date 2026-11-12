module

public import NearCritical.Section10PropertyFromCrossing

/-! Two-sided spanning probability for roots near the centre of the origin
typical cube (inputs `hspanlo`, `hspanhi` of `hcand_of_raw`).

* `span_lower_of_splitCross`: `(c/4)/(N+1)^2 <= P_{p_c}[spanning]` from the
  cited `SplitCrossInput` (all-faces crossing implies spanning).
* `span_upper_of_ordinary`: `P_{p_c}[spanning] <= 64 C/(N+1)^2` from the cited
  ordinary one-arm input (spanning forces an arm of length about `t/2` from a
  root in `centeredBox((t-1)/32)`), for `t >= 8`.

Here `N = (t-1)/2` and the cube is `centeredBox d N` with faces
`typicalFace t 0`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem span_lower_of_splitCross {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (hcross : SplitCrossInput d c)
    (t N : ℕ) (ht : 1 ≤ t) (hN : (t - 1) / 2 = N) (htCross : hcross.threshold ≤ t) {x : Vertex d}
    (hx : x ∈ centeredBox d ((t - 1) / 32)) :
    (c / 4) / (N + 1 : ℝ) ^ 2 ≤ (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) := by
  have hcube : typicalCube t (0 : Vertex d) = centeredBox d N := by
    rw [typicalCube_zero t ht, hN]
  have hxN : x ∈ centeredBox d N := by
    rw [mem_centeredBox] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> omega
  have hxQ : x ∈ typicalCube t (0 : Vertex d) := by
    rw [hcube]
    exact hxN
  have hsub := crossAll_subset_spanning t ht t hxQ
  rw [hcube] at hsub
  have hS := hcross.crossing t htCross x hx
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hNt : (t : ℝ) ≤ 2 * ((N : ℝ) + 1) := by
    have : t ≤ 2 * (N + 1) := by omega
    exact_mod_cast this
  have h1 : (c / 4) / (N + 1 : ℝ) ^ 2 ≤ c / (t : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (t : ℝ) ^ 2 ≤ 4 * ((N : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  exact h1.trans (hS.trans (measureReal_mono hsub (measure_ne_top _ _)))

theorem span_upper_of_ordinary {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (ordinary : OrdinaryArmWindowInput d C) (t N : ℕ) (ht : 8 ≤ t) (hN : (t - 1) / 2 = N)
    {x : Vertex d} (hx : x ∈ centeredBox d ((t - 1) / 32)) (f : Fin d × Bool) :
    (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
      64 * C / (N + 1 : ℝ) ^ 2 := by
  have ht1 : 1 ≤ t := by omega
  obtain ⟨n, hn4⟩ : ∃ n, t / 4 = n := ⟨_, rfl⟩
  have hn : 1 ≤ n := by omega
  have hsub : finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x ⊆
      extrinsicRadiusArmEvent x ((n : ℝ) / 2) := by
    intro ω hω
    obtain ⟨y, hy⟩ := hω f
    obtain ⟨hyC, hyF⟩ := Finset.mem_inter.mp hy
    obtain ⟨j, s⟩ := f
    obtain ⟨_, hyj⟩ := Finset.mem_filter.mp hyF
    have hyj' : y j = if s then (((t - 1) / 2 : ℕ) : ℤ) else -(((t - 1) / 2 : ℕ) : ℤ) := by
      simpa using hyj
    have hxj := mem_centeredBox.mp hx j
    have hreach : (openGraph ω).Reachable x y :=
      SimpleGraph.Reachable.mono
        (show restrictedGraph ω (centeredBox d N : Set (Vertex d)) ≤ openGraph ω from
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
  have harm : (percolation d (criticalPoint d)).real (extrinsicRadiusArmEvent x ((n : ℝ) / 2)) ≤
      C / (n : ℝ) ^ 2 := by
    refine ordinary (criticalPoint d) x n hn ?_
    have : (0:ℝ) ≤ (((n : ℝ)) ^ 2)⁻¹ := by positivity
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (harm.trans ?_)
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNn : ((N : ℝ) + 1) ≤ 8 * (n : ℝ) := by
    have : N + 1 ≤ 8 * n := by omega
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ((N : ℝ) + 1) ^ 2 ≤ 64 * (n : ℝ) ^ 2 := by nlinarith
  nlinarith

end NearCritical.Section10
