module

public import NearCritical.ClusterCountCriticalScale
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Source eq.PZ: actual two-sided count concentration with the n^(8-d) rate.
All scale data are explicit, and the limiting theorem only requires them eventually. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

private lemma actual_count_deviation_chebyshev {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {t : ℝ} (ht : 0 < t) :
    (percolation d p).real {ω | t ≤ |rootedPropertyCount U Z P ω-rootedPropertyCountMean p U Z P|} ≤
      (∫ ω, (rootedPropertyCount U Z P ω-rootedPropertyCountMean p U Z P)^2
        ∂percolation d p)/t^2 := by
  let g := fun ω : Configuration d =>
    (rootedPropertyCount U Z P ω-rootedPropertyCountMean p U Z P)^2
  have hi : Integrable g (percolation d p) := integrable_rootedPropertyCount_observable p U Z hZU P
    (fun x => (x-rootedPropertyCountMean p U Z P)^2)
  have hn : 0 ≤ᵐ[percolation d p] g := by
    filter_upwards [] with ω
    exact sq_nonneg _
  have hs : {ω : Configuration d | t ≤ |rootedPropertyCount U Z P ω-rootedPropertyCountMean p U Z P|} ⊆
      {ω | t^2 ≤ g ω} := by
    intro ω hω
    have hsq := (sq_le_sq₀ ht.le (abs_nonneg
      (rootedPropertyCount U Z P ω-rootedPropertyCountMean p U Z P))).mpr hω
    change t^2 ≤ (rootedPropertyCount U Z P ω-rootedPropertyCountMean p U Z P)^2
    simpa only [sq_abs] using hsq
  have hm := mul_meas_ge_le_integral_of_nonneg hn hi (t^2)
  have ht2 : 0 < t^2 := by positivity
  have hb : (percolation d p).real {ω | t^2 ≤ g ω} ≤
      (∫ ω, g ω ∂percolation d p)/t^2 := by
    apply (le_div_iff₀ ht2).mpr
    simpa only [mul_comm] using hm
  exact (measureReal_mono hs).trans hb

private lemma critical_count_relative_normalization {d : ℕ} (hd : 9 ≤ d)
    {n m C a c : ℝ} (hn : 1 ≤ n) (hC : 0 ≤ C) (ha : 0 < a) (hc : 0 < c)
    (hm : c*n^(d-2) ≤ m) :
    C*n^(d+4)/(a*m)^2 ≤ C/(a^2*c^2*n^(d-8)) := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hbase : 0 < c*n^(d-2) := mul_pos hc (pow_pos hnpos _)
  have hmpos : 0 < m := lt_of_lt_of_le hbase hm
  have hmul := mul_le_mul_of_nonneg_left hm ha.le
  have hden : (a*(c*n^(d-2)))^2 ≤ (a*m)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hmul
  have hdenpos : 0 < (a*(c*n^(d-2)))^2 := by positivity
  have hp : (n^(d-2))^2 = n^(d+4)*n^(d-8) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  calc
    _ ≤ C*n^(d+4)/(a*(c*n^(d-2)))^2 :=
      div_le_div_of_nonneg_left (by positivity) hdenpos hden
    _ = _ := by
      rw [mul_pow, mul_pow, hp]
      field_simp [ne_of_gt ha, ne_of_gt hc, ne_of_gt hnpos] <;> ring

/-- Actual source two-sided relative count-deviation rate. The ONE coefficient
is before all radii/sets/properties; no variance/failure estimate is an input. -/
theorem critical_rootedPropertyCount_deviation_rate {d : ℕ} (hd : 9 ≤ d)
    (hA : TwoPointAsymptotics d) {Cm Cv c a : ℝ}
    (hCm : 0 ≤ Cm) (hCv : 0 ≤ Cv) (hc : 0 < c) (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) (Z : Finset (Vertex d)), Z ⊆ centeredBox d N →
      ∀ (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop),
      c*(N+1:ℝ)^(d-2) ≤ rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P →
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P ≤ Cm*(N+1:ℝ)^(d-2) →
      (∀ ω r, r ∈ Z → rootedClusterProperty (centeredBox d N) r P ω →
        ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ Cv*(N+1:ℝ)^4) →
      (percolation d (criticalPoint d)).real {ω |
        a*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P ≤
        |rootedPropertyCount (centeredBox d N) Z P ω-
          rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P|} ≤
      D/(N+1:ℝ)^(d-8) := by
  obtain ⟨C, hC, hv⟩ := critical_rootedPropertyCount_variance_scale_of_box
    (by omega : 2 ≤ d) hA hCm hCv
  let D := C/(a^2*c^2)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro N Z hZ P hlo hhi hcap
  have hn : (1:ℝ) ≤ (N+1:ℝ) := by exact_mod_cast (Nat.le_add_left 1 N)
  have hnpos : (0:ℝ) < (N+1:ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hm : 0 < rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P :=
    lt_of_lt_of_le (mul_pos hc (pow_pos hnpos _)) hlo
  have ht := actual_count_deviation_chebyshev (criticalPoint d) (centeredBox d N) Z hZ P
    (mul_pos ha hm)
  have hvar := hv N Z hZ P hhi hcap
  have hnorm := critical_count_relative_normalization hd hn hC.le ha hc hlo
  calc
    _ ≤ (∫ ω, (rootedPropertyCount (centeredBox d N) Z P ω-
        rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P)^2
        ∂percolation d (criticalPoint d)) /
        (a*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P)^2 := ht
    _ ≤ C*(N+1:ℝ)^(d+4) /
        (a*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P)^2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ ≤ C/(a^2*c^2*(N+1:ℝ)^(d-8)) := hnorm
    _ = _ := by dsimp [D]; rw [div_div]

/-- The source n^(8-d) rate tends to zero for d>=9, including eventual-scale
uses where the probability bound is unavailable at finitely many small radii. -/
theorem critical_count_deviation_rate_zero {d : ℕ} (hd : 9 ≤ d) (D : ℝ) :
    Tendsto (fun N : ℕ => D/(N+1:ℝ)^(d-8)) atTop (𝓝 0) := by
  have hk : d-8 ≠ 0 := by omega
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow (d-8)
  have hp : Tendsto (fun N : ℕ => ((1:ℝ)/(N+1:ℝ))^(d-8)) atTop (𝓝 0) := by
    simpa only [zero_pow hk] using h
  have hD := (tendsto_const_nhds (x := D)).mul hp
  simpa only [div_eq_mul_inv,one_mul,inv_pow,mul_zero] using hD

/-- Actual source eq.PZ concentration with EVENTUAL raw scale data. No all-n
strengthening, probability-limit premise or uniform property assumption is added. -/
theorem critical_rootedPropertyCount_deviation_tendsto_zero {d : ℕ} (hd : 9 ≤ d)
    (hA : TwoPointAsymptotics d) {Cm Cv c a : ℝ}
    (hCm : 0 ≤ Cm) (hCv : 0 ≤ Cv) (hc : 0 < c) (ha : 0 < a)
    (Z : ℕ → Finset (Vertex d))
    (P : ℕ → SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (hdata : ∀ᶠ N : ℕ in atTop,
      Z N ⊆ centeredBox d N ∧
      c*(N+1:ℝ)^(d-2) ≤ rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N) ∧
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N) ≤ Cm*(N+1:ℝ)^(d-2) ∧
      (∀ ω r, r ∈ Z N → rootedClusterProperty (centeredBox d N) r (P N) ω →
        ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ Cv*(N+1:ℝ)^4)) :
    Tendsto (fun N : ℕ => (percolation d (criticalPoint d)).real {ω |
      a*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N) ≤
      |rootedPropertyCount (centeredBox d N) (Z N) (P N) ω-
        rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N)|})
      atTop (𝓝 0) := by
  obtain ⟨D, _hD, hb⟩ := critical_rootedPropertyCount_deviation_rate hd hA hCm hCv hc ha
  have hu : ∀ᶠ N : ℕ in atTop,
      (percolation d (criticalPoint d)).real {ω |
        a*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N) ≤
        |rootedPropertyCount (centeredBox d N) (Z N) (P N) ω-
          rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N)|} ≤
      D/(N+1:ℝ)^(d-8) := by
    filter_upwards [hdata] with N hN
    exact hb N (Z N) hN.1 (P N) hN.2.1 hN.2.2.1 hN.2.2.2
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) hu
    (critical_count_deviation_rate_zero hd D)

end NearCritical
