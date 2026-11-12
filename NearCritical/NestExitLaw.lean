module

public import NearCritical.NestFreshTube
public import NearCritical.ChemicalCrossingGeometry
public import NearCritical.BulkDomain
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Terminal exit success law in source def.nw.chain. Exit edges leave B_L,
so they are fresh relative to all internal-bond reveals of that box. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory ProbabilityTheory
open scoped Classical

lemma finite_bernoulli_exists_open {E : Type*} [Fintype E] (p : unitInterval) :
    (Measure.pi (fun _ : E => bernoulliMeasure true false p)).real
      {η | ∃ e, η e=true} = 1-(1-(p:ℝ))^(Fintype.card E) := by
  have hm : MeasurableSet {η : E → Bool | ∃ e, η e=true} := (Set.toFinite _).measurableSet
  have hc : ({η : E → Bool | ∃ e, η e=true} : Set (E → Bool))ᶜ = {fun _ => false} := by
    ext η
    simp [funext_iff]
  have hfalse := finite_bernoulli_singleton_real (E:=E) p (fun _ => false)
  simp only [Bool.false_eq_true,ite_false,Finset.prod_const,Finset.card_univ] at hfalse
  have ht := measureReal_add_measureReal_compl
    (μ := Measure.pi (fun _ : E => bernoulliMeasure true false p)) hm
  rw [hc,hfalse,probReal_univ] at ht
  linarith

/-- Distinct regular-boundary vertices supply distinct positive exit bonds. -/
def nestExitBondSet {d : ℕ} (i : Fin d) (V : Finset (Vertex d)) : Finset (Bond d) :=
  V.image (fun x => (x,i))

lemma card_nestExitBondSet {d : ℕ} (i : Fin d) (V : Finset (Vertex d)) :
    (nestExitBondSet i V).card=V.card := by
  exact Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h)

/-- Freshness is derived from actual upper-face coordinates, not assumed. -/
lemma nestExitBondSet_disjoint_internal {d : ℕ} (i : Fin d) (U V : Finset (Vertex d))
    {hi : ℤ} (hU : ∀ x∈U, x i≤hi) (hV : ∀ x∈V, x i=hi) :
    Disjoint (nestExitBondSet i V) (internalBondSet U) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
  have ht := hU (bondTip (x,i)) ((mem_internalBondSet U (x,i)).1 hf).2
  simp only [bondTip,Function.update_self] at ht
  rw [hV x hx] at ht
  omega

lemma nestExitBondSet_disjoint_centered {d r : ℕ} (i : Fin d) (V : Finset (Vertex d))
    (hV : ∀ x∈V, x i=(r:ℤ)) :
    Disjoint (nestExitBondSet i V) (internalBondSet (centeredBox d r)) :=
  nestExitBondSet_disjoint_internal i _ V (fun _x hx => (mem_centeredBox.mp hx i).2) hV

/-- Exact source exit success probability under the original percolation law. -/
theorem percolation_exit_success_probability {d : ℕ} (p : unitInterval)
    (i : Fin d) (V : Finset (Vertex d)) :
    (percolation d p).real {ω | ∃ x∈V, ω (x,i)=true} = 1-(1-(p:ℝ))^V.card := by
  let T := nestExitBondSet i V
  have hm : (percolation d p).map T.restrict = Measure.pi (fun _ : T => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  have h := finite_bernoulli_exists_open (E:=T) p
  rw [← hm,map_measureReal_apply (Finset.measurable_restrict T) (Set.toFinite _).measurableSet] at h
  have he : (T.restrict : Configuration d → (T → Bool)) ⁻¹' {η | ∃ e, η e=true} =
      {ω : Configuration d | ∃ x∈V, ω (x,i)=true} := by
    ext ω
    simp [T,nestExitBondSet,Finset.restrict]
  rw [he] at h
  simpa only [T,Fintype.card_coe,card_nestExitBondSet] using h

/-- The finite fresh-block normalizer is exactly the same source formula. -/
lemma exit_fresh_success_probability {d : ℕ} (p : unitInterval)
    (S : Finset (Bond d)) (i : Fin d) (V : Finset (Vertex d)) (η : S → Bool) :
    freshTubeSuccessProbability p S (nestExitBondSet i V)
      (fun _ ξ => ∃ e, ξ e=true) η = 1-(1-(p:ℝ))^V.card := by
  simpa only [freshTubeSuccessProbability,Fintype.card_coe,card_nestExitBondSet] using
    finite_bernoulli_exists_open (E:=nestExitBondSet i V) p

lemma exit_success_probability_pos {d : ℕ} (p : unitInterval) (hp : 0<(p:ℝ))
    (V : Finset (Vertex d)) (hV : V.Nonempty) : 0<1-(1-(p:ℝ))^V.card := by
  apply sub_pos.mpr
  exact pow_lt_one₀ (sub_nonneg.mpr p.2.2) (by linarith)
    (Finset.card_ne_zero.mpr hV)

/-- Exact normalized exit-step identity against every interior-history observable.
The selected exit set V is fixed here; adaptive selection is a separate finite
history-partition step, not silently included in this statement. -/
theorem percolation_exit_weighted_mean {d : ℕ} (p : unitInterval) (hp : 0<(p:ℝ))
    (i : Fin d) (U V : Finset (Vertex d)) (hVne : V.Nonempty) {hi : ℤ}
    (hU : ∀ x∈U, x i≤hi) (hV : ∀ x∈V, x i=hi)
    (S : Finset (Bond d)) (hS : S⊆internalBondSet U) (H : (S → Bool) → ℝ) :
    (∫ ω : Configuration d, H (S.restrict ω) *
      (if ∃ x∈V, ω (x,i)=true then (1-(1-(p:ℝ))^V.card)⁻¹ else 0)
      ∂percolation d p) = ∫ ω : Configuration d, H (S.restrict ω) ∂percolation d p := by
  let T := nestExitBondSet i V
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro e heS heT
    exact Finset.disjoint_left.mp (nestExitBondSet_disjoint_internal i U V hU hV) heT (hS heS)
  have hq (η : S → Bool) : 0<freshTubeSuccessProbability p S T
      (fun _ ξ => ∃ e, ξ e=true) η := by
    rw [exit_fresh_success_probability]
    exact exit_success_probability_pos p hp V hVne
  have h := percolation_freshTube_weighted_mean p S T hd (fun _ ξ => ∃ e, ξ e=true) hq H
  have he (ω : Configuration d) : freshTubeSuccessWeight p S T
      (fun _ ξ => ∃ e, ξ e=true) (S.restrict ω) (T.restrict ω) =
      (if ∃ x∈V, ω (x,i)=true then (1-(1-(p:ℝ))^V.card)⁻¹ else 0) := by
    unfold freshTubeSuccessWeight
    rw [exit_fresh_success_probability]
    have hex : (∃ e : T, T.restrict ω e=true) ↔ ∃ x∈V, ω (x,i)=true := by
      simp [T,nestExitBondSet,Finset.restrict]
    simp only [hex]
  simp_rw [he] at h
  exact h


/-- The source large-boundary exit success estimate, uniformly over p>=p0>0.
The cardinal threshold is chosen by genuine Bernoulli geometric decay. -/
theorem percolation_exit_success_eventually {d : ℕ} (p0 : unitInterval)
    (hp0 : 0<(p0:ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ p : unitInterval, (p0:ℝ)≤(p:ℝ) →
      ∀ i : Fin d, ∀ V : Finset (Vertex d), N≤V.card →
        1-ε/4 ≤ (percolation d p).real {ω | ∃ x∈V, ω (x,i)=true} := by
  have hlim : Filter.Tendsto (fun N : ℕ => (1-(p0:ℝ))^N) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr p0.2.2) (by linarith)
  have he := hlim.eventually (gt_mem_nhds (div_pos hε (by norm_num : (0:ℝ)<4)))
  filter_upwards [he] with N hN
  intro p hp i V hV
  rw [percolation_exit_success_probability]
  have hbase : (1-(p:ℝ))^V.card ≤ (1-(p0:ℝ))^V.card :=
    pow_le_pow_left₀ (sub_nonneg.mpr p.2.2) (by linarith) _
  have hdepth : (1-(p0:ℝ))^V.card ≤ (1-(p0:ℝ))^N :=
    pow_le_pow_of_le_one (sub_nonneg.mpr p0.2.2) (by linarith [p0.2.1]) hV
  linarith [hbase.trans hdepth]

end NearCritical
