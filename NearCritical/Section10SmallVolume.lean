module

public import NearCritical.Section10CandidateOrigin

/-! Small-volume control on the spanning event (`hlow` of `hcand_of_raw`),
DERIVED from the cited cluster-size estimate.

* `ClusterSizeInput d α c`: source `eq.cluster_size` (upper half; CHS23 Thm 4,
  KN11), stated for the translated box `z + Lambda_m`:
  `P_pc[|C_{z+Lambda_m}(z)| <= lam m^4, z <-> dist > m-1]
     <= exp(-c lam^(-1/3)) P_pc[z <-> dist > m-1]` whenever
  `(log m)^α / m^3 < lam`. The event `dist > m-1` is `z <-> boundary of
  z+Lambda_m`. By translation invariance this is the origin statement.
* `hlow_of_clusterSize`: source prop.num_spanning_new Step 1. For a root `x` in
  `Lambda_k`, `k = (t-1)/32`, with `m = N - k`: `C_N(x)` contains
  `C_{x+Lambda_m}(x)`, spanning forces the arm to distance `m`, the one-arm
  upper bound and `span_lower_of_splitCross` compare the two normalisations.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- Source `eq.cluster_size`, upper bound, translated box. The source asserts
it for each `α > 3d/2` (with `c` depending on `α`), for the side-`n` box; the
radius-`m` box used here differs by a factor 2 in `n`, absorbed by the explicit
threshold constant `A` and by `c`. Instantiate with `α > 3d/2`.

The range is restricted to `lam ≤ lam0` for some cap `lam0 > 0` provided by the
citation (`ClusterSizeInput.cap`). Without an upper limit the statement is
false (and the input unsatisfiable for `c > 0`): at `m = 1` every `lam > 0`
passes the threshold, and for `lam ≥ 3^d` the volume condition is automatic, so
the inequality would force `P[arm] = 0`. The source display (main.tex
1190--1195) has the same defect for large `lambda`; the only use here is at a
small `lam`. -/
def ClusterSizeInput (d : ℕ) (α A c : ℝ) : Prop :=
  ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ (z : Vertex d) (m : ℕ) (lam : ℝ), 1 ≤ m →
    A * (Real.log (m : ℝ)) ^ α / (m : ℝ) ^ 3 < lam → lam ≤ lam0 →
    (percolation d (criticalPoint d)).real
      ({ω | ((finiteBoxCluster ω (translateSites z (centeredBox d m)) z).card : ℝ) ≤
          lam * (m : ℝ) ^ 4} ∩ extrinsicRadiusArmEvent z ((m : ℝ) - 1)) ≤
    Real.exp (-c * lam ^ (-(1 / 3 : ℝ))) *
      (percolation d (criticalPoint d)).real (extrinsicRadiusArmEvent z ((m : ℝ) - 1))

/-- The cap on `lam` supplied with the cited estimate. -/
noncomputable def ClusterSizeInput.cap {d : ℕ} {α A c : ℝ} (h : ClusterSizeInput d α A c) : ℝ :=
  Classical.choose h

theorem ClusterSizeInput.cap_pos {d : ℕ} {α A c : ℝ} (h : ClusterSizeInput d α A c) :
    0 < h.cap :=
  (Classical.choose_spec h).1

theorem hlow_of_clusterSize {d : ℕ} (hd : 1 ≤ d) {α A c c₀ Carm : ℝ} (hc₀ : 0 ≤ c₀)
    (hsize : ClusterSizeInput d α A c) (hcross : SplitCrossInput d c₀)
    (ordinary : OrdinaryArmWindowInput d Carm) (t N k m : ℕ) (ht : 64 ≤ t)
    (hN : (t - 1) / 2 = N) (htCross : hcross.threshold ≤ t) (hk : (t - 1) / 32 = k) (hm : N - k = m)
    {x : Vertex d} (hx : x ∈ centeredBox d k) {a lam δ : ℝ}
    (hlam : A * (Real.log (m : ℝ)) ^ α / (m : ℝ) ^ 3 < lam) (hlam1 : lam ≤ hsize.cap)
    (ha : a ≤ lam * (m : ℝ) ^ 4)
    (hδ : 0 ≤ δ) (hε : Real.exp (-c * lam ^ (-(1 / 3 : ℝ))) * Carm ≤ δ * (c₀ / 4)) :
    (percolation d (criticalPoint d)).real
      ({ω | ((finiteBoxCluster ω (centeredBox d N) x).card : ℝ) ≤ a} ∩
        finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
    δ * (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) := by
  have ht1 : 1 ≤ t := by omega
  have hm1 : 1 ≤ m := by omega
  have hbox : translateSites x (centeredBox d m) ⊆ centeredBox d N := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := (mem_translateSites_iff x _ y).mp hy
    rw [mem_centeredBox] at hx hw ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    obtain ⟨h3, h4⟩ := hw i
    rw [Pi.add_apply]
    constructor <;> omega
  have hsub : ({ω | ((finiteBoxCluster ω (centeredBox d N) x).card : ℝ) ≤ a} ∩
        finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ⊆
      ({ω | ((finiteBoxCluster ω (translateSites x (centeredBox d m)) x).card : ℝ) ≤
          lam * (m : ℝ) ^ 4} ∩ extrinsicRadiusArmEvent x ((m : ℝ) - 1)) := by
    rintro ω ⟨hsmall, hspan⟩
    refine ⟨?_, ?_⟩
    · have hcl : finiteBoxCluster ω (translateSites x (centeredBox d m)) x ⊆
          finiteBoxCluster ω (centeredBox d N) x := by
        intro y hy
        obtain ⟨hyU, hr⟩ := (mem_finiteBoxCluster ω _ x y).mp hy
        exact (mem_finiteBoxCluster ω _ x y).mpr ⟨hbox hyU,
          SimpleGraph.Reachable.mono
            (restrictedGraph_mono ω (Finset.coe_subset.mpr hbox)) hr⟩
      have hcard : ((finiteBoxCluster ω (translateSites x (centeredBox d m)) x).card : ℝ) ≤
          ((finiteBoxCluster ω (centeredBox d N) x).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcl
      exact hcard.trans ((show _ ≤ a from hsmall).trans ha)
    · obtain ⟨y, hy⟩ := hspan ((⟨0, by omega⟩ : Fin d), true)
      obtain ⟨hyC, hyF⟩ := Finset.mem_inter.mp hy
      obtain ⟨_, hyj⟩ := Finset.mem_filter.mp hyF
      have hyj' : y (⟨0, by omega⟩ : Fin d) = (((t - 1) / 2 : ℕ) : ℤ) := by
        simpa using hyj
      have hxj := (mem_centeredBox.mp hx) (⟨0, by omega⟩ : Fin d)
      have hreach : (openGraph ω).Reachable x y :=
        SimpleGraph.Reachable.mono
          (show restrictedGraph ω (centeredBox d N : Set (Vertex d)) ≤ openGraph ω from
            fun _ _ h => h.1) ((mem_finiteBoxCluster ω _ x y).mp hyC).2
      refine ⟨y, ?_, hreach⟩
      have hcoord : dist (x (⟨0, by omega⟩ : Fin d)) (y (⟨0, by omega⟩ : Fin d)) ≤ dist x y :=
        dist_le_pi_dist x y _
      rw [Int.dist_eq] at hcoord
      have hint : (m : ℤ) ≤ |x (⟨0, by omega⟩ : Fin d) - y (⟨0, by omega⟩ : Fin d)| := by
        have : x (⟨0, by omega⟩ : Fin d) - y (⟨0, by omega⟩ : Fin d) ≤ 0 := by omega
        rw [abs_of_nonpos this]
        omega
      have hreal : ((m : ℤ) : ℝ) ≤
          ((|x (⟨0, by omega⟩ : Fin d) - y (⟨0, by omega⟩ : Fin d)| : ℤ) : ℝ) := by
        exact_mod_cast hint
      push_cast at hreal
      linarith
  obtain ⟨n, hn2⟩ : ∃ n, 2 * (m - 1) = n := ⟨_, rfl⟩
  have hn : 1 ≤ n := by omega
  have hnR : (m : ℝ) - 1 = (n : ℝ) / 2 := by
    rw [← hn2, Nat.cast_mul, Nat.cast_sub hm1]
    norm_num
  have hNn : ((N : ℝ) + 1) ≤ (n : ℝ) := by
    have : N + 1 ≤ n := by omega
    exact_mod_cast this
  have hN0 : (0:ℝ) < (N : ℝ) + 1 := by positivity
  have harm : (percolation d (criticalPoint d)).real (extrinsicRadiusArmEvent x ((m : ℝ) - 1)) ≤
      Carm / (n : ℝ) ^ 2 := by
    rw [hnR]
    refine ordinary (criticalPoint d) x n hn ?_
    have : (0:ℝ) ≤ (((n : ℝ)) ^ 2)⁻¹ := by positivity
    linarith
  have hlo := span_lower_of_splitCross hc₀ hcross t N ht1 hN htCross (x := x) (by rw [hk]; exact hx)
  have hexp : 0 ≤ Real.exp (-c * lam ^ (-(1 / 3 : ℝ))) := (Real.exp_pos _).le
  have hsq : ((N : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hN0.le hNn 2
  calc _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := (Classical.choose_spec hsize).2 x m lam hm1 hlam hlam1
    _ ≤ Real.exp (-c * lam ^ (-(1 / 3 : ℝ))) * (Carm / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left harm hexp
    _ = (Real.exp (-c * lam ^ (-(1 / 3 : ℝ))) * Carm) / (n : ℝ) ^ 2 := by rw [mul_div_assoc]
    _ ≤ (δ * (c₀ / 4)) / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right hε (sq_nonneg _)
    _ ≤ (δ * (c₀ / 4)) / ((N : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    _ = δ * ((c₀ / 4) / ((N : ℝ) + 1) ^ 2) := by rw [mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo hδ

end NearCritical.Section10
