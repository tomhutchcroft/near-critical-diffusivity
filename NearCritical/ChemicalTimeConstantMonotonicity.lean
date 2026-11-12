module

public import NearCritical.ChemicalConverse

/-! The paper's monotone-coupling/connected-limit argument in prop.chem.upper,
source6042. Standard uniqueness and Garet–Marchand convergence are named inputs;
actual coupling and the time-constant comparison are proved here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The pointwise predicate used by the existing named AE convergence input. -/
def PointwiseConnectedChemicalLimit {d : ℕ} (ω : Configuration d) (u : Vertex d) (μ : ℝ) : Prop :=
  Tendsto (fun n : ℕ ↦ ((chemicalDistance ω 0 (n • u)).toNat : ℝ) / (n : ℝ))
    (atTop ⊓ principal {n : ℕ | (openGraph ω).Reachable 0 (n • u)}) (𝓝 μ)

/-- On a connected pair, opening bonds can only decrease the finite distance.
The disconnected toNat convention is not used in this comparison. -/
lemma chemicalDistance_toNat_mono {d : ℕ} {ω η : Configuration d}
    (h : BK.ConfigLE ω η) {x y : Vertex d} (hc : (openGraph ω).Reachable x y) :
    ((chemicalDistance η x y).toNat : ℝ) ≤ ((chemicalDistance ω x y).toNat : ℝ) := by
  have hd := SimpleGraph.edist_anti (u := x) (v := y) (openGraph_mono h)
  have hn := ENat.toNat_le_toNat hd (SimpleGraph.edist_ne_top_iff_reachable.mpr hc)
  exact_mod_cast hn

/-- Reversed proposed limits force the smaller configuration to have no
connections along the ray eventually. No common-subsequence existence is assumed. -/
lemma eventually_no_connection_of_reversed_limits {d : ℕ} {ω η : Configuration d}
    (h : BK.ConfigLE ω η) {u : Vertex d} {μ ν : ℝ}
    (hlo : PointwiseConnectedChemicalLimit ω u μ)
    (hhi : PointwiseConnectedChemicalLimit η u ν) (hgap : μ < ν) :
    ∀ᶠ n : ℕ in atTop, ¬ (openGraph ω).Reachable 0 (n • u) := by
  let a := (μ + ν) / 2
  have hμa : μ < a := by dsimp [a]; linarith
  have haν : a < ν := by dsimp [a]; linarith
  have hl := eventually_inf_principal.mp (hlo.eventually (gt_mem_nhds hμa))
  have hh := eventually_inf_principal.mp (hhi.eventually (lt_mem_nhds haν))
  filter_upwards [hl, hh] with n hnlo hnhi
  intro hconn
  have hconn' := SimpleGraph.Reachable.mono (openGraph_mono h) hconn
  have hd := div_le_div_of_nonneg_right (chemicalDistance_toNat_mono h hconn)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
  have hlow := hnlo hconn
  have hhigh := hnhi hconn'
  linarith

/-- Source6042: chemical time constants are antitone in the parameter, from
actual monotone coupling and named standard connected-subsequence limits. -/
theorem chemical_timeConstant_antitone {d : ℕ} (p q : unitInterval)
    (hp : criticalPoint d < p) (hpq : p ≤ q) (u : Vertex d) {μ ν : ℝ}
    (huniq : AEInfiniteClusterUniqueness d p)
    (hlimp : AEConnectedChemicalLimit d p u μ) (hlimq : AEConnectedChemicalLimit d q u ν) :
    ν ≤ μ := by
  by_contra h
  have hgap : μ < ν := lt_of_not_ge h
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt (criticalPoint d).2.1 hp
  have hq0 : 0 < (q : ℝ) := hp0.trans_le hpq
  let r : unitInterval := ⟨(p : ℝ) / (q : ℝ),
    div_nonneg p.2.1 q.2.1, (div_le_one hq0).mpr hpq⟩
  let ρ := (percolation d q).prod (percolation d r)
  have hr : (p : ℝ) = (q : ℝ) * (r : ℝ) := by dsimp [r]; field_simp
  have hmap : ρ.map thinConfiguration = percolation d p := percolation_thin_map d q r p hr
  have hlo : ∀ᵐ z ∂ρ, PointwiseConnectedChemicalLimit (thinConfiguration z) u μ := by
    apply ae_of_ae_map (μ := ρ) (f := thinConfiguration (E := Bond d))
      (p := fun ω : Configuration d ↦ PointwiseConnectedChemicalLimit ω u μ)
      measurable_thinConfiguration.aemeasurable
    rw [hmap]
    exact hlimp
  have hhi : ∀ᵐ z ∂ρ, PointwiseConnectedChemicalLimit z.1 u ν := by
    apply ae_of_ae_map (μ := ρ) (f := (Prod.fst : Configuration d × Configuration d → Configuration d))
      (p := fun ω : Configuration d ↦ PointwiseConnectedChemicalLimit ω u ν)
      measurable_fst.aemeasurable
    simp only [ρ, Measure.map_fst_prod, measure_univ, one_smul]
    exact hlimq
  have huni : ∀ᵐ z ∂ρ, ∀ x y : Vertex d,
      thinConfiguration z ∈ infiniteClusterAtEvent x →
      thinConfiguration z ∈ infiniteClusterAtEvent y →
        (openGraph (thinConfiguration z)).Reachable x y := by
    apply ae_of_ae_map (μ := ρ) (f := thinConfiguration (E := Bond d))
      (p := fun ω : Configuration d ↦ ∀ x y : Vertex d,
        ω ∈ infiniteClusterAtEvent x → ω ∈ infiniteClusterAtEvent y →
          (openGraph ω).Reachable x y)
      measurable_thinConfiguration.aemeasurable
    rw [hmap]
    exact huniq
  let E := fun n : ℕ ↦ infiniteClusterAtEvent (0 : Vertex d) ∩ infiniteClusterAtEvent (n • u)
  let F := fun n : ℕ ↦ thinConfiguration ⁻¹' E n
  have hE (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_infiniteClusterAtEvent 0).inter (measurableSet_infiniteClusterAtEvent (n • u))
  have hF (n : ℕ) : MeasurableSet (F n) := (hE n).preimage measurable_thinConfiguration
  have hzero := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := ρ) (L := atTop) (A := (∅ : Set (Configuration d × Configuration d)))
    MeasurableSet.empty hF (by
      filter_upwards [hlo, hhi, huni] with z hl hh hu
      have he := eventually_no_connection_of_reversed_limits (thinConfiguration_le_left z) hl hh hgap
      filter_upwards [he] with n hn
      simp only [mem_empty_iff_false, iff_false]
      intro hz
      exact hn (hu 0 (n • u) hz.1 hz.2))
  simp only [measure_empty] at hzero
  have hreal : Tendsto (fun n : ℕ ↦ ρ.real (F n)) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hzero
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using ht
  have hprob (n : ℕ) : ρ.real (F n) = (percolation d p).real (E n) := by
    have hm := map_measureReal_apply (μ := ρ) measurable_thinConfiguration (hE n)
    rw [hmap] at hm
    exact hm.symm
  have hpositive : 0 < density d p ^ 2 := pow_pos (density_pos_above_critical hp) 2
  obtain ⟨n, hn⟩ := (hreal.eventually (gt_mem_nhds hpositive)).exists
  have hlower : density d p ^ 2 ≤ ρ.real (F n) := by
    rw [hprob]
    exact infiniteCluster_intersection_probability d p 0 (n • u)
  exact (not_le_of_gt hn) hlower

/-- The macroscopic parameter part of prop.chem.upper: a fixed supercritical
anchor controls every larger parameter with an explicit positive prefactor. -/
theorem chemical_timeConstant_upper_macroscopic {d : ℕ} (p₁ p : unitInterval)
    (h₁ : criticalPoint d < p₁) (h₁p : p₁ ≤ p) (u : Vertex d) {μ₁ μ : ℝ}
    (huniq : AEInfiniteClusterUniqueness d p₁)
    (hlim₁ : AEConnectedChemicalLimit d p₁ u μ₁) (hlim : AEConnectedChemicalLimit d p u μ) :
    μ ≤ (|μ₁| + 1) / Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) := by
  have hmono := chemical_timeConstant_antitone p₁ p h₁ h₁p u huniq hlim₁ hlim
  have hδ : 0 < (p : ℝ) - (criticalPoint d : ℝ) := sub_pos.mpr (h₁.trans_le h₁p)
  have hδ1 : (p : ℝ) - (criticalPoint d : ℝ) ≤ 1 := by
    have hp1 := p.2.2
    have hpc0 := (criticalPoint d).2.1
    linarith
  have hspos : 0 < Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) := Real.sqrt_pos.mpr hδ
  have hsle : Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) ≤ 1 := by
    exact (Real.sqrt_le_sqrt hδ1).trans_eq (by norm_num)
  have hc : μ₁ ≤ |μ₁| + 1 := by linarith [le_abs_self μ₁]
  have hdiv : |μ₁| + 1 ≤ (|μ₁| + 1) / Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) := by
    apply (le_div_iff₀ hspos).mpr
    exact mul_le_of_le_one_right (by positivity) hsle
  exact hmono.trans (hc.trans hdiv)

end NearCritical
