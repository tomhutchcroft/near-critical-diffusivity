module

public import NearCritical.ClusterCountCriticalConcentration
public import NearCritical.ClusterDistinctCount

/-! Quantitative actual distinct-component lower count for source Step3.
The actual mean/volume inputs remain explicit; no high-probability count is a premise. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

private lemma distinct_failure_subset_deviation {d : ℕ} (hd : 9 ≤ d)
    (N : ℕ) (Z : Finset (Vertex d)) (hZ : Z ⊆ centeredBox d N)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {c Cv a : ℝ}
    (hc : 0 < c) (hCv : 0 < Cv) (ha : 0 < a)
    (hlo : c*(N+1:ℝ)^(d-2) ≤
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P)
    (hcap : ∀ ω r, r ∈ Z → rootedClusterProperty (centeredBox d N) r P ω →
      ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ Cv*(N+1:ℝ)^4) :
    {ω | ((selectedPropertyComponents (centeredBox d N) Z P ω).card:ℝ) ≤
      (a*c/Cv)*(N+1:ℝ)^(d-6)} ⊆
    {ω | (1-a)*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P ≤
      |rootedPropertyCount (centeredBox d N) Z P ω-
        rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P|} := by
  have hn : (0:ℝ) < (N+1:ℝ) := by positivity
  have hV : 0 < Cv*(N+1:ℝ)^4 := by positivity
  have hp : (N+1:ℝ)^(d-2) = (N+1:ℝ)^(d-6)*(N+1:ℝ)^4 := by
    rw [← pow_add]
    congr 1
    omega
  have hthreshold : (a*c/Cv)*(N+1:ℝ)^(d-6) ≤
      a*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P /
        (Cv*(N+1:ℝ)^4) := by
    apply (le_div_iff₀ hV).mpr
    calc
      _ = a*(c*(N+1:ℝ)^(d-2)) := by
        rw [hp]
        field_simp [ne_of_gt hCv] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo ha.le
  have hs := selectedPropertyComponents_lower_tail_subset (centeredBox d N) Z hZ P hV hcap
    (a*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P)
  intro ω hω
  have hcount := hs (hω.trans hthreshold)
  calc
    _ = rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P -
        a*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P := by ring
    _ ≤ rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P -
        rootedPropertyCount (centeredBox d N) Z P ω := sub_le_sub_left hcount _
    _ ≤ |rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P -
        rootedPropertyCount (centeredBox d N) Z P ω| := le_abs_self _
    _ = _ := abs_sub_comm _ _

/-- The actual finite-source failure rate for distinct components. Coefficients
are fixed before all radii and properties; volume is raw selected-component data. -/
theorem critical_distinctPropertyCount_failure_rate {d : ℕ} (hd : 9 ≤ d)
    (hA : TwoPointAsymptotics d) {Cm Cv c a : ℝ}
    (hCm : 0 ≤ Cm) (hCv : 0 < Cv) (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) (Z : Finset (Vertex d)), Z ⊆ centeredBox d N →
      ∀ (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop),
      c*(N+1:ℝ)^(d-2) ≤ rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P →
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P ≤ Cm*(N+1:ℝ)^(d-2) →
      (∀ ω r, r ∈ Z → rootedClusterProperty (centeredBox d N) r P ω →
        ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ Cv*(N+1:ℝ)^4) →
      (percolation d (criticalPoint d)).real {ω |
        ((selectedPropertyComponents (centeredBox d N) Z P ω).card:ℝ) ≤
          (a*c/Cv)*(N+1:ℝ)^(d-6)} ≤ D/(N+1:ℝ)^(d-8) := by
  obtain ⟨D, hD, hb⟩ := critical_rootedPropertyCount_deviation_rate hd hA hCm hCv.le hc
    (sub_pos.mpr ha1)
  refine ⟨D, hD, ?_⟩
  intro N Z hZ P hlo hhi hcap
  exact (measureReal_mono (distinct_failure_subset_deviation hd N Z hZ P hc hCv ha hlo hcap)).trans
    (hb N Z hZ P hlo hhi hcap)

/-- Only EVENTUAL raw scale hypotheses are needed for the actual distinct
failure probability to vanish. No desired count-probability limit is an input. -/
theorem critical_distinctPropertyCount_failure_tendsto_zero {d : ℕ} (hd : 9 ≤ d)
    (hA : TwoPointAsymptotics d) {Cm Cv c a : ℝ}
    (hCm : 0 ≤ Cm) (hCv : 0 < Cv) (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1)
    (Z : ℕ → Finset (Vertex d))
    (P : ℕ → SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (hdata : ∀ᶠ N : ℕ in atTop,
      Z N ⊆ centeredBox d N ∧
      c*(N+1:ℝ)^(d-2) ≤ rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N) ∧
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N) ≤ Cm*(N+1:ℝ)^(d-2) ∧
      (∀ ω r, r ∈ Z N → rootedClusterProperty (centeredBox d N) r (P N) ω →
        ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ Cv*(N+1:ℝ)^4)) :
    Tendsto (fun N : ℕ => (percolation d (criticalPoint d)).real {ω |
      ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ) ≤
        (a*c/Cv)*(N+1:ℝ)^(d-6)}) atTop (𝓝 0) := by
  obtain ⟨D, _hD, hb⟩ := critical_distinctPropertyCount_failure_rate hd hA hCm hCv hc ha ha1
  have hu : ∀ᶠ N : ℕ in atTop,
      (percolation d (criticalPoint d)).real {ω |
        ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ) ≤
          (a*c/Cv)*(N+1:ℝ)^(d-6)} ≤ D/(N+1:ℝ)^(d-8) := by
    filter_upwards [hdata] with N hN
    exact hb N (Z N) hN.1 (P N) hN.2.1 hN.2.2.1 hN.2.2.2
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) hu
    (critical_count_deviation_rate_zero hd D)

/-- Actual high-probability distinct-component lower count, with an explicit
positive coefficient and eventual mean/volume data. Real outer probabilities
suffice: no unproved measurability premise for the family count is added. -/
theorem critical_distinctPropertyCount_success_tendsto_one {d : ℕ} (hd : 9 ≤ d)
    (hA : TwoPointAsymptotics d) {Cm Cv c a : ℝ}
    (hCm : 0 ≤ Cm) (hCv : 0 < Cv) (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1)
    (Z : ℕ → Finset (Vertex d))
    (P : ℕ → SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (hdata : ∀ᶠ N : ℕ in atTop,
      Z N ⊆ centeredBox d N ∧
      c*(N+1:ℝ)^(d-2) ≤ rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N) ∧
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) (Z N) (P N) ≤ Cm*(N+1:ℝ)^(d-2) ∧
      (∀ ω r, r ∈ Z N → rootedClusterProperty (centeredBox d N) r (P N) ω →
        ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ Cv*(N+1:ℝ)^4)) :
    Tendsto (fun N : ℕ => (percolation d (criticalPoint d)).real {ω |
      (a*c/Cv)*(N+1:ℝ)^(d-6) ≤
        ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ)}) atTop (𝓝 1) := by
  let F := fun N : ℕ => (percolation d (criticalPoint d)).real {ω |
    ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ) ≤
      (a*c/Cv)*(N+1:ℝ)^(d-6)}
  let S := fun N : ℕ => (percolation d (criticalPoint d)).real {ω |
    (a*c/Cv)*(N+1:ℝ)^(d-6) ≤
      ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ)}
  have hf : Tendsto F atTop (𝓝 0) :=
    critical_distinctPropertyCount_failure_tendsto_zero hd hA hCm hCv hc ha ha1 Z P hdata
  have hlow (N : ℕ) : 1-S N ≤ F N := by
    have hcvr : (Set.univ : Set (Configuration d)) ⊆
        {ω | ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ) ≤
          (a*c/Cv)*(N+1:ℝ)^(d-6)} ∪
        {ω | (a*c/Cv)*(N+1:ℝ)^(d-6) ≤
          ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ)} := by
      intro ω _hω
      change ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ) ≤
        (a*c/Cv)*(N+1:ℝ)^(d-6) ∨ (a*c/Cv)*(N+1:ℝ)^(d-6) ≤
          ((selectedPropertyComponents (centeredBox d N) (Z N) (P N) ω).card:ℝ)
      exact le_total _ _
    have h := (measureReal_mono (μ := percolation d (criticalPoint d)) hcvr).trans
      (measureReal_union_le _ _)
    have hu : (percolation d (criticalPoint d)).real Set.univ = 1 := by simp
    rw [hu] at h
    change 1 ≤ F N+S N at h
    linarith
  have hz : Tendsto (fun N => 1-S N) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sub_nonneg.mpr measureReal_le_one) hlow hf
  have hs := (tendsto_const_nhds (x := (1:ℝ))).sub hz
  simpa only [sub_sub_cancel, sub_zero] using hs

end NearCritical
