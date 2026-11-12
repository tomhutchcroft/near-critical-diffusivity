module

public import NearCritical.SplitCrossEventsMeasurable
public import NearCritical.SpanningEmbeddedPath
public import NearCritical.RestrictedSusceptibility
public import NearCritical.TranslationInvariance
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal

/-- The unrestricted cluster volume at a translated root is the same
as the volume at the origin in the translated configuration. -/
theorem restrictedClusterSize_univ_translate {d : ℕ} (ω : Configuration d) (x : Vertex d) :
    restrictedClusterSize Set.univ x ω =
      restrictedClusterSize Set.univ 0 (translateConfiguration x ω) := by
  unfold restrictedClusterSize
  rw [← (Equiv.addLeft x).tsum_eq]
  apply tsum_congr
  intro y
  have he : ω ∈ connectionToSetEvent Set.univ x {x+y} ↔
      translateConfiguration x ω ∈ connectionToSetEvent Set.univ 0 {y} := by
    rw [← restricted_reachable_iff_connection Set.univ ω x (x+y) (Set.mem_univ _),
      ← restricted_reachable_iff_connection Set.univ (translateConfiguration x ω) 0 y (Set.mem_univ _),
      restrictedGraph_univ, restrictedGraph_univ]
    have hi := SimpleGraph.Iso.reachable_iff (φ := translationGraphIso x ω)
      (u := (0 : Vertex d)) (v := y)
    change (openGraph ω).Reachable (x+0) (x+y) ↔
      (openGraph (translateConfiguration x ω)).Reachable 0 y at hi
    simpa only [add_zero] using hi
  simp only [he]

/-- The mass lower-tail condition in the cited rooted GHPf convergence. -/
def spanningMassTail {d : ℕ} (t : ℕ) (x : Vertex d) : Set (Configuration d) :=
  {ω | (t:ℝ≥0∞)^4 ≤ restrictedClusterSize Set.univ x ω}

theorem measurableSet_spanningMassTail {d : ℕ} (t : ℕ) (x : Vertex d) :
    MeasurableSet (spanningMassTail t x) :=
  measurableSet_le measurable_const (measurable_restrictedClusterSize Set.univ x)

theorem spanningMassTail_measure_eq_origin {d : ℕ} (p : unitInterval) (t : ℕ) (x : Vertex d) :
    percolation d p (spanningMassTail t x) = percolation d p (spanningMassTail t 0) := by
  have he : translateConfiguration x ⁻¹' spanningMassTail t 0 = spanningMassTail t x := by
    ext ω
    change ((t:ℝ≥0∞)^4 ≤ restrictedClusterSize Set.univ 0 (translateConfiguration x ω)) ↔
      ((t:ℝ≥0∞)^4 ≤ restrictedClusterSize Set.univ x ω)
    rw [restrictedClusterSize_univ_translate ω x]
  have hm := Measure.map_apply (μ := percolation d p) (measurable_translateConfiguration x)
    (measurableSet_spanningMassTail t (0 : Vertex d))
  rw [percolation_map_translation, he] at hm
  exact hm.symm

/-- A measure-preserving translation also transports the laws
conditioned on corresponding measurable cluster-mass events. -/
theorem map_cond_of_measure_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → Ω) (hf : Measurable f) (hmap : Measure.map f μ = μ)
    (S : Set Ω) (hS : MeasurableSet S) :
    Measure.map f (ProbabilityTheory.cond μ (f ⁻¹' S)) = ProbabilityTheory.cond μ S := by
  ext A hA
  rw [Measure.map_apply hf hA, cond_apply (hS.preimage hf), cond_apply hS,
    ← Set.preimage_inter, ← Measure.map_apply hf hS, ← Measure.map_apply hf (hS.inter hA), hmap]

theorem translate_cond_spanningMassTail {d : ℕ} (p : unitInterval) (t : ℕ) (x : Vertex d) :
    Measure.map (translateConfiguration (-x))
      (ProbabilityTheory.cond (percolation d p) (spanningMassTail t 0)) =
      ProbabilityTheory.cond (percolation d p) (spanningMassTail t x) := by
  have he : translateConfiguration (-x) ⁻¹' spanningMassTail t x = spanningMassTail t 0 := by
    ext ω
    have hinv : translateConfiguration x (translateConfiguration (-x) ω) = ω := by
      funext e
      change ω (translateBond (-x) (translateBond x e)) = ω e
      congr 1
      apply Prod.ext
      · change -x + (x + e.1) = e.1
        rw [← add_assoc, neg_add_cancel, zero_add]
      · rfl
    change ((t:ℝ≥0∞)^4 ≤ restrictedClusterSize Set.univ x (translateConfiguration (-x) ω)) ↔
      ((t:ℝ≥0∞)^4 ≤ restrictedClusterSize Set.univ 0 ω)
    rw [restrictedClusterSize_univ_translate, hinv]
  have h := map_cond_of_measure_preserving (percolation d p) (translateConfiguration (-x))
    (measurable_translateConfiguration _) (percolation_map_translation _ _)
    (spanningMassTail t x) (measurableSet_spanningMassTail t x)
  simpa only [he] using h

/-- The critical cluster mass bin used in the scaling-limit argument.
The endpoints are dyadic multiples of the fourth power of the lattice scale. -/
def spanningMassBin {d : ℕ} (x : Vertex d) (t j : ℕ) : Set (Configuration d) :=
  {ω | (2:ℝ≥0∞)^j * (t:ℝ≥0∞)^4 ≤ restrictedClusterSize Set.univ x ω ∧
    restrictedClusterSize Set.univ x ω ≤ (2:ℝ≥0∞)^(j+1) * (t:ℝ≥0∞)^4}

theorem measurableSet_spanningMassBin {d : ℕ} (x : Vertex d) (t j : ℕ) :
    MeasurableSet (spanningMassBin x t j) := by
  have hm := measurable_restrictedClusterSize Set.univ x
  exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)

/-- An event of positive probability on which a coupling eventually
succeeds gives an eventual uniform lower bound for the marginal events. -/
theorem eventually_measure_ge_of_eventually_mem {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (A : ℕ → Set Ω) {δ : ℝ≥0∞}
    (hδ : δ < μ E) (hE : ∀ ω ∈ E, ∃ n, ∀ m ≥ n, ω ∈ A m) :
    ∃ n, ∀ m ≥ n, δ ≤ μ (A m) := by
  let F (n : ℕ) : Set Ω := {ω | ω ∈ E ∧ ∀ m ≥ n, ω ∈ A m}
  have hF : Monotone F := fun n m hnm ω hω =>
    ⟨hω.1, fun k hk => hω.2 k (hnm.trans hk)⟩
  have hcover : (⋃ n, F n) = E := by
    ext ω
    constructor
    · intro hω
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
      exact hn.1
    · intro hω
      obtain ⟨n,hn⟩ := hE ω hω
      exact Set.mem_iUnion.mpr ⟨n,hω,hn⟩
  have hsup := hF.measure_iUnion (μ := μ)
  rw [hcover] at hsup
  obtain ⟨n,hn⟩ : ∃ n, δ < μ (F n) := by
    by_contra! h
    exact (not_le_of_gt hδ) (hsup.trans_le (iSup_le h))
  exact ⟨n, fun m hm => hn.le.trans (measure_mono (fun _ h => h.2 m hm))⟩

/-- A conditional crossing lower bound on a single size bin and a lower
bound on that bin's mass give the unconditional crossing estimate. -/
theorem measureReal_ge_of_cond_and_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E A : Set Ω} (hE : MeasurableSet E)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : a ≤ (ProbabilityTheory.cond μ E).real A) (hB : b ≤ μ.real E) :
    a*b ≤ μ.real A := by
  have h := congrArg ENNReal.toReal (cond_mul_eq_inter hE A μ)
  rw [ENNReal.toReal_mul] at h
  exact (mul_le_mul hA hB hb (measureReal_nonneg : 0 ≤ (ProbabilityTheory.cond μ E).real A)).trans
    (h.le.trans (measureReal_mono Set.inter_subset_right (measure_ne_top μ A)))

private theorem exists_dyadic_bin {v u : ℝ≥0∞} (J : ℕ)
    (hlo : v ≤ u) (hhi : u < (2:ℝ≥0∞)^J*v) :
    ∃ j < J, (2:ℝ≥0∞)^j*v ≤ u ∧ u < (2:ℝ≥0∞)^(j+1)*v := by
  induction J with
  | zero => exact (not_lt_of_ge hlo (by simpa using hhi)).elim
  | succ J ih =>
    by_cases h : u < (2:ℝ≥0∞)^J*v
    · obtain ⟨j,hj,h₁,h₂⟩ := ih h
      exact ⟨j, hj.trans (Nat.lt_succ_self J), h₁, h₂⟩
    · exact ⟨J, Nat.lt_succ_self J, le_of_not_gt h, hhi⟩

/-- The critical cluster volume tail at square thresholds, in the form
needed to find a dyadic bin of mass comparable to the one-arm scale. -/
def SpanningVolumeTail (d : ℕ) (c C : ℝ) : Prop :=
  ∀ (s : ℕ), 1 ≤ s → ∀ x : Vertex d,
    c / (s:ℝ) ≤ (percolation d (criticalPoint d)).real
      {ω | (s:ℝ≥0∞)^2 ≤ restrictedClusterSize Set.univ x ω} ∧
    (percolation d (criticalPoint d)).real
      {ω | (s:ℝ≥0∞)^2 ≤ restrictedClusterSize Set.univ x ω} ≤ C / (s:ℝ)

/-- The two-sided critical cluster-volume tail ensures that one of
a fixed finite number of dyadic size bins has mass at least `b / t²`. -/
theorem spanningMassBin_lower_of_volume_tail {d : ℕ} {c C : ℝ}
    (hc : 0 < c) (hvol : SpanningVolumeTail d c C) :
    ∃ (J : ℕ) (b : ℝ), 0 < b ∧ ∀ (t : ℕ), 1 ≤ t → ∀ x : Vertex d,
      ∃ j < J, b / (t:ℝ)^2 ≤ (percolation d (criticalPoint d)).real (spanningMassBin x t j) := by
  obtain ⟨K,hK⟩ := pow_unbounded_of_one_lt (max 1 (2*C/c)) (by norm_num : (1:ℝ) < 2)
  have hK₀ : 0 < K := by
    by_contra! h
    have h0 : K = 0 := by omega
    rw [h0,pow_zero] at hK
    exact (not_lt_of_ge (le_max_left _ _)) hK
  let J := K*2
  have hJ : 0 < J := by dsimp only [J]; omega
  refine ⟨J,c/(4*(J:ℝ)),div_pos hc (by positivity),?_⟩
  intro t ht x
  let μ := percolation d (criticalPoint d)
  let v := (t:ℝ≥0∞)^4
  let U := {ω : Configuration d | v ≤ restrictedClusterSize Set.univ x ω}
  let V := {ω : Configuration d | (2:ℝ≥0∞)^J*v ≤ restrictedClusterSize Set.univ x ω}
  have htpos : (0:ℝ) < t := by exact_mod_cast (Nat.zero_lt_one.trans_le ht)
  have hlo := (hvol (t^2) (one_le_pow₀ ht) x).1
  have hhi := (hvol (2^K*t^2) (by positivity) x).2
  have hU : c / (t:ℝ)^2 ≤ μ.real U := by
    simpa only [μ,U,v,Nat.cast_pow,← pow_mul] using hlo
  have hV : μ.real V ≤ C / ((2:ℝ)^K*(t:ℝ)^2) := by
    simpa only [μ,V,v,J,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow,← pow_mul] using hhi
  have hcoef : C / (2:ℝ)^K ≤ c/2 := by
    have h := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt hK)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hwindow : (c/2)/(t:ℝ)^2 ≤ μ.real (U \ V) := by
    apply le_trans _ (le_measureReal_sdiff (μ := μ) (s₁ := U) (s₂ := V))
    have hV' : μ.real V ≤ (c/2)/(t:ℝ)^2 :=
      hV.trans (by rw [← div_div]; exact div_le_div_of_nonneg_right hcoef (sq_nonneg _))
    calc
      _ = c/(t:ℝ)^2 - (c/2)/(t:ℝ)^2 := by ring
      _ ≤ _ := sub_le_sub hU hV'
  have hcover : U \ V ⊆ ⋃ j ∈ Finset.range J, spanningMassBin x t j := by
    intro ω hω
    obtain ⟨j,hj,h₁,h₂⟩ := exists_dyadic_bin J hω.1 (lt_of_not_ge hω.2)
    exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hj,h₁,h₂.le⟩⟩
  by_contra! h
  have hsum := (hwindow.trans (measureReal_mono hcover (measure_ne_top μ _))).trans
    (measureReal_biUnion_finset_le (μ := μ) (Finset.range J) (spanningMassBin x t))
  have hbnd : ∑ j ∈ Finset.range J, μ.real (spanningMassBin x t j) ≤ (c/4)/(t:ℝ)^2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range J, (c/(4*(J:ℝ)))/(t:ℝ)^2 := by
        exact Finset.sum_le_sum fun j hj => (h j (Finset.mem_range.mp hj)).le
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        field_simp [show (J:ℝ) ≠ 0 by positivity] <;> ring
  have hcontr := (div_le_div_iff_of_pos_right (sq_pos_of_pos htpos)).mp (hsum.trans hbnd)
  linarith

/-- Apply the conditional lower bound on whichever bin supplies enough
mass at the current scale. The conditional estimate is uniform over the
finitely many bins and the allowed roots. -/
theorem splitCrossInput_of_size_bins {d J : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (T₁ T₂ : ℕ)
    (hbin : ∀ t ≥ T₁, ∀ x ∈ centeredBox d ((t - 1) / 32), ∃ j < J,
      b / (t:ℝ)^2 ≤ (percolation d (criticalPoint d)).real (spanningMassBin x t j))
    (hcond : ∀ t ≥ T₂, ∀ x ∈ centeredBox d ((t - 1) / 32), ∀ j < J,
      a ≤ (ProbabilityTheory.cond (percolation d (criticalPoint d))
        (spanningMassBin x t j)).real (crossAll t t x)) :
    SplitCrossInput d (a*b) := by
  refine ⟨max T₁ T₂, ?_⟩
  intro t ht x hx
  obtain ⟨j,hj,hMass⟩ := hbin t ((le_max_left _ _).trans ht) x hx
  have h := measureReal_ge_of_cond_and_mass (percolation d (criticalPoint d))
    (measurableSet_spanningMassBin x t j) ha (div_nonneg hb (sq_nonneg _))
    (hcond t ((le_max_right _ _).trans ht) x hx j hj) hMass
  simpa only [mul_div_assoc] using h

end NearCritical.Section10
