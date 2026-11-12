module

public import NearCritical.Section9PivotalConcentration
public import NearCritical.HeartMembershipBK
public import NearCritical.Section9RevealSupport
public import Mathlib.Probability.ConditionalProbability

/-! Section9, eq.def.fC and eq.fC_shorthand: actual conditioning on the revealed
heart-cluster unions. Probability requires a nonzero conditioning atom. Pair
and union conditioning coincide for the source's disjoint cubes. This module
does not assert independence or unchanged product laws on unexplored bonds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- The actual two revealed critical cluster values, not abstract random data. -/
def section9RevealEvent {d : ℕ} (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) : Set (Configuration d) :=
  {ω | heartClusterUnion ω Q₁ H₁ = F₁ ∧ heartClusterUnion ω Q₃ H₃ = F₃}

/-- The source F13 is the union of the two actual revealed heart unions. -/
def section9RevealUnionEvent {d : ℕ} (Q₁ H₁ Q₃ H₃ F : Finset (Vertex d)) : Set (Configuration d) :=
  {ω | heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃ = F}

lemma measurableSet_section9HeartReveal {d : ℕ} (Q H F : Finset (Vertex d)) (hH : H ⊆ Q) :
    MeasurableSet {ω : Configuration d | heartClusterUnion ω Q H = F} := by
  have heq : {ω : Configuration d | heartClusterUnion ω Q H = F} =
      ⋂ x : Vertex d, {ω | x ∈ heartClusterUnion ω Q H ↔ x ∈ F} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff]
  rw [heq]
  apply MeasurableSet.iInter
  intro x
  by_cases hx : x ∈ F
  · simpa only [hx, iff_true] using measurableSet_heartClusterUnion_member Q H hH x
  · simp only [hx, iff_false]
    have hc : {ω : Configuration d | x ∉ heartClusterUnion ω Q H} =
        {ω : Configuration d | x ∈ heartClusterUnion ω Q H}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [hc]
    exact (measurableSet_heartClusterUnion_member Q H hH x).compl

lemma measurableSet_section9RevealEvent {d : ℕ} (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) : MeasurableSet (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) :=
  (measurableSet_section9HeartReveal Q₁ H₁ F₁ hH₁).inter
    (measurableSet_section9HeartReveal Q₃ H₃ F₃ hH₃)

/-- The actual conditional configuration measure, usable at p=criticalPoint d. -/
def section9RevealedLaw {d : ℕ} (p : unitInterval) (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) :
    Measure (Configuration d) :=
  ProbabilityTheory.cond (percolation d p) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃)

theorem section9RevealedLaw_isProbability {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d))
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0) :
    IsProbabilityMeasure (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃) :=
  ProbabilityTheory.cond_isProbabilityMeasure hpos

/-- Conditioning retains the literal two cluster values almost surely; this
also holds vacuously for a zero atom, which is not called a probability law. -/
theorem section9RevealedLaw_ae_values {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) :
    ∀ᵐ ω ∂section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃,
      heartClusterUnion ω Q₁ H₁ = F₁ ∧ heartClusterUnion ω Q₃ H₃ = F₃ :=
  ProbabilityTheory.ae_cond_mem (measurableSet_section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃)

private lemma separated_union_inter {d : ℕ} (Q P G H : Finset (Vertex d))
    (hG : G ⊆ Q) (hH : H ⊆ P) (hdis : Disjoint Q P) : (G ∪ H) ∩ Q = G := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hxQ⟩
    · exact hx
    · exact (Finset.disjoint_left.mp hdis hxQ (hH hx)).elim
  · intro hx
    exact ⟨Or.inl hx, hG hx⟩

/-- For disjoint source cubes the union F13 determines each revealed cluster
by intersection with its own cube, so the source conditioning is exact. -/
theorem section9RevealEvent_eq_union {d : ℕ} (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d))
    (hF₁ : F₁ ⊆ Q₁) (hF₃ : F₃ ⊆ Q₃) (hdis : Disjoint Q₁ Q₃) :
    section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ = section9RevealUnionEvent Q₁ H₁ Q₃ H₃ (F₁ ∪ F₃) := by
  ext ω
  constructor
  · rintro ⟨h₁, h₃⟩
    change heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃ = F₁ ∪ F₃
    rw [h₁, h₃]
  · intro h
    change heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃ = F₁ ∪ F₃ at h
    constructor
    · have hi := congrArg (fun S => S ∩ Q₁) h
      simpa only [separated_union_inter Q₁ Q₃ _ _
        (heartClusterUnion_subset ω Q₁ H₁) (heartClusterUnion_subset ω Q₃ H₃) hdis,
        separated_union_inter Q₁ Q₃ F₁ F₃ hF₁ hF₃ hdis] using hi
    · have hs : heartClusterUnion ω Q₃ H₃ ∪ heartClusterUnion ω Q₁ H₁ = F₃ ∪ F₁ := by
        simpa only [Finset.union_comm] using h
      have hi := congrArg (fun S => S ∩ Q₃) hs
      simpa only [separated_union_inter Q₃ Q₁ _ _
        (heartClusterUnion_subset ω Q₃ H₃) (heartClusterUnion_subset ω Q₁ H₁) hdis.symm,
        separated_union_inter Q₃ Q₁ F₃ F₁ hF₃ hF₁ hdis.symm] using hi

/-- A conditioning atom of nonzero actual probability contains a realization,
so its prescribed revealed sets inherit their cube supports. -/
theorem section9RevealEvent_supports_of_nonzero {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d))
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0) :
    F₁ ⊆ Q₁ ∧ F₃ ⊆ Q₃ := by
  have hne : section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ ≠ ∅ := by
    intro h
    apply hpos
    rw [h, measure_empty]
  obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨h₁, h₃⟩ := hω
  rw [← h₁, ← h₃]
  exact ⟨heartClusterUnion_subset ω Q₁ H₁, heartClusterUnion_subset ω Q₃ H₃⟩

theorem section9RevealedLaw_eq_union_condition {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d))
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hdis : Disjoint Q₁ Q₃) :
    section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃ =
      ProbabilityTheory.cond (percolation d p) (section9RevealUnionEvent Q₁ H₁ Q₃ H₃ (F₁ ∪ F₃)) := by
  obtain ⟨hF₁, hF₃⟩ := section9RevealEvent_supports_of_nonzero p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  unfold section9RevealedLaw
  rw [section9RevealEvent_eq_union Q₁ H₁ Q₃ H₃ F₁ F₃ hF₁ hF₃ hdis]

/-- Literal conditional first moment of the actual Section9 pivot count. -/
theorem section9ConditionalPivotalMean_eq_sum {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A B =
      ∑ e ∈ E, ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} := by
  letI := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  exact integral_section9PivotalCount (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃) E L R Q₁ F₁ Q₃ F₃ A B

/-- The source opening variance bound now holds for the ACTUAL revealed law,
not an arbitrary probability measure presumed to describe conditioning. -/
theorem section9ConditionalPivotal_variance_le {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
      section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A B)^2 ∂ν) ≤
        section9PivotalVarianceEnvelope ν E L R Q₁ F₁ Q₃ F₃ A B := by
  letI := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  exact section9PivotalCount_variance_le (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃) E L R Q₁ F₁ Q₃ F₃ A B

/-- The literal source concentration interval, for the actual revealed law;
its remaining error is the computed conditional covariance expression. -/
theorem section9ConditionalPivotal_relative_interval {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hm : 0 < section9PivotalMean (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃)
      E L R Q₁ F₁ Q₃ F₃ A B) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    let m := section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A B
    1 - section9PivotalVarianceEnvelope ν E L R Q₁ F₁ Q₃ F₃ A B / (m/2)^2 ≤
      ν.real {ω | m/2 ≤ section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∧
        section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤ 3*m/2} := by
  letI := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  exact section9PivotalCount_relative_interval (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃)
    E L R Q₁ F₁ Q₃ F₃ A B hm

/-- Under the actual revealed law, every observable of a finite block outside
both explored incident masks has its original Bernoulli expectation. This is
proved from reveal locality and the product measure, not assumed freshness. -/
theorem section9RevealedLaw_fresh_expectation {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (T : Finset (Bond d))
    (hd : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) T)
    (g : (T → Bool) → ℝ) :
    (∫ ω : Configuration d, g (T.restrict ω)
      ∂section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃) =
      ∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p := by
  let E := section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃
  have hm : MeasurableSet E :=
    measurableSet_section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃
  have hn : (percolation d p).real E ≠ 0 :=
    (measureReal_ne_zero_iff (by finiteness)).mpr hpos
  have hf := twoHeartReveal_fresh_factorization p Q₁ H₁ F₁ Q₃ H₃ F₃ hH₁ hH₃ T hd g
  change (∫ ω : Configuration d, E.indicator (fun _ => (1 : ℝ)) ω *
    g (T.restrict ω) ∂percolation d p) =
      (percolation d p).real E * (∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p) at hf
  have hi : E.indicator (fun ω => g (T.restrict ω)) =
      fun ω => E.indicator (fun _ => (1 : ℝ)) ω * g (T.restrict ω) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  unfold section9RevealedLaw ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    ← integral_indicator hm, hi, hf]
  change ((percolation d p).real E)⁻¹ *
    ((percolation d p).real E * (∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p)) = _
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end NearCritical
