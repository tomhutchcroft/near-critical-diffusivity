module

public import NearCritical.Section9PivotalSupport
public import NearCritical.Section9CandidateCount
public import NearCritical.Section9ConditionalLaw
public import NearCritical.Section9PivotOpening
public import NearCritical.Section9MiddleGeometry

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The actual opened-target count reads only the available critical tube bonds
and the enriched joining bonds. Agreement on the deleted critical bonds is unnecessary. -/
theorem section9_opened_target_count_eq_of_agree {d : ℕ} {ι : Type*}
    (I : Finset ι) (targets : ι → Finset (Vertex d))
    (M L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d))
    (ω ω' η η' : Configuration d)
    (hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = ω' b)
    (hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = ω' b)
    (hM : ∀ b ∈ internalBondSet M, η b = η' b) :
    (I.filter fun j => (sprinkledPivotalPairs ω η
      (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty) =
    (I.filter fun j => (sprinkledPivotalPairs ω' η'
      (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty) := by
  have open_eq (e : Vertex d × Vertex d) (he : e ∈ orientedLatticePairs M) :
      (openGraph η).Adj e.1 e.2 ↔ (openGraph η').Adj e.1 e.2 := by
    obtain ⟨hx, hy, _⟩ := (mem_orientedLatticePairs M e.1 e.2).mp he
    have transport (α β : Configuration d)
        (h : ∀ b ∈ internalBondSet M, α b = β b) :
        (openGraph α).Adj e.1 e.2 → (openGraph β).Adj e.1 e.2 := by
      rintro ⟨b, hb, hends⟩
      have hbM : b ∈ internalBondSet M := by
        apply (mem_internalBondSet M b).mpr
        rcases hends with ⟨hbase, htip⟩ | ⟨hbase, htip⟩
        · exact ⟨hbase ▸ hx, htip ▸ hy⟩
        · exact ⟨hbase ▸ hy, htip ▸ hx⟩
      exact ⟨b, (h b hbM).symm.trans hb, hends⟩
    exact ⟨transport η η' hM, transport η' η (fun b hb => (hM b hb).symm)⟩
  have pairs_eq (B : Finset (Vertex d)) :
      sprinkledPivotalPairs ω η (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B =
        sprinkledPivotalPairs ω' η' (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B := by
    ext e
    simp only [sprinkledPivotalPairs, sprinklingPivotalPairs, Finset.mem_filter]
    have hpivot := sprinklingPivotalPair_iff_of_available_agree
      L R Q₁ F₁ Q₃ F₃ A B ω ω' hL hR e
    constructor
    · rintro ⟨⟨he, hp⟩, ho⟩
      exact ⟨⟨he, hpivot.mp hp⟩, (open_eq e he).mp ho⟩
    · rintro ⟨⟨he, hp⟩, ho⟩
      exact ⟨⟨he, hpivot.mpr hp⟩, (open_eq e he).mpr ho⟩
  ext j
  simp only [Finset.mem_filter, pairs_eq (targets j)]

/-- The literal heart reveal leaves the joint law on any disjoint finite
critical block unchanged. This includes residual bonds inside the end cubes. -/
theorem section9_revealed_block_law {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (S : Finset (Bond d))
    (hdis : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) S) :
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).map S.restrict =
      (percolation d p).map S.restrict := by
  let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
  letI : IsProbabilityMeasure ν :=
    section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  apply Measure.ext
  intro U hU
  rw [Measure.map_apply (Finset.measurable_restrict S) hU,
    Measure.map_apply (Finset.measurable_restrict S) hU]
  have hf := section9RevealedLaw_fresh_expectation p Q₁ H₁ Q₃ H₃ F₁ F₃
    hH₁ hH₃ hpos S hdis (U.indicator (fun _ => (1 : ℝ)))
  have hi :
      (fun ω : Configuration d => U.indicator (fun _ => (1 : ℝ)) (S.restrict ω)) =
        (S.restrict ⁻¹' U).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : S.restrict ω ∈ U <;> simp [Set.indicator, hω]
  simp_rw [hi, integral_indicator_one (hU.preimage (Finset.measurable_restrict S))] at hf
  change ν.real (S.restrict ⁻¹' U) = (percolation d p).real (S.restrict ⁻¹' U) at hf
  have hmass := congrArg ENNReal.ofReal hf
  rwa [ofReal_measureReal (measure_ne_top ν _),
    ofReal_measureReal (measure_ne_top (percolation d p) _)] at hmass

/-- A fresh sprinkling field can be restricted independently of the critical
available bonds, even after the heart reveal. -/
theorem section9_revealed_two_stage_block_law {d : ℕ} (p q : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (S M : Finset (Bond d))
    (hdis : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) S) :
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).map
      (Prod.map S.restrict M.restrict) =
        ((percolation d p).map S.restrict).prod ((percolation d q).map M.restrict) := by
  letI := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  rw [← Measure.map_prod_map _ _
    (Finset.measurable_restrict S) (Finset.measurable_restrict M),
    section9_revealed_block_law p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos S hdis]

/-- The actual two-stage opened-target probability is a finite tube-block
probability after revealing the heart unions. The middle block is read in
both fields, since the joining bonds use the OR of the two bits. -/
theorem section9_opened_target_probability_eq_block {d : ℕ} {ι : Type*}
    (p q : unitInterval) (Q₁ H₁ Q₃ H₃ F₁ F₃ M L R A : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (I : Finset ι) (targets : ι → Finset (Vertex d)) (m : ℕ)
    (S : Finset (Bond d))
    (hL : sprinklingAvailableBonds L Q₁ F₁ ⊆ S)
    (hR : sprinklingAvailableBonds R Q₃ F₃ ⊆ S)
    (hM : internalBondSet M ⊆ S)
    (hdis : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) S) :
    let J := internalBondSet M
    let count := fun (ω ζ : Configuration d) =>
      (I.filter fun j => (sprinkledPivotalPairs ω (sprinkleOrConfiguration ω ζ)
        (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
      {z | (m : ℝ) < (count z.1 z.2 : ℝ)} =
    (((percolation d p).map S.restrict).prod ((percolation d q).map J.restrict)).real
      {z | (m : ℝ) < (count (extendConfiguration S (fun _ => false) z.1)
        (extendConfiguration J (fun _ => false) z.2) : ℝ)} := by
  intro J count
  let read := Prod.map S.restrict J.restrict
  let localEvent : Set ((S → Bool) × (J → Bool)) :=
    {z | (m : ℝ) < (count (extendConfiguration S (fun _ => false) z.1)
      (extendConfiguration J (fun _ => false) z.2) : ℝ)}
  have read_meas : Measurable read :=
    ((Finset.measurable_restrict S).comp measurable_fst).prodMk
      ((Finset.measurable_restrict J).comp measurable_snd)
  have event_eq : {z | (m : ℝ) < (count z.1 z.2 : ℝ)} = read ⁻¹' localEvent := by
    ext z
    let ω := extendConfiguration S (fun _ => false) (S.restrict z.1)
    let ζ := extendConfiguration J (fun _ => false) (J.restrict z.2)
    have hω (b : Bond d) (hb : b ∈ S) : z.1 b = ω b := by
      simp [ω, extendConfiguration, hb, Finset.restrict]
    have hζ (b : Bond d) (hb : b ∈ J) : z.2 b = ζ b := by
      simp [ζ, extendConfiguration, hb, Finset.restrict]
    have he := section9_opened_target_count_eq_of_agree I targets M L R Q₁ F₁ Q₃ F₃ A
      z.1 ω (sprinkleOrConfiguration z.1 z.2) (sprinkleOrConfiguration ω ζ)
      (fun b hb => hω b (hL hb)) (fun b hb => hω b (hR hb)) (by
        intro b hb
        simp only [sprinkleOrConfiguration, hω b (hM hb), hζ b hb])
    change (m : ℝ) < (count z.1 z.2 : ℝ) ↔ (m : ℝ) < (count ω ζ : ℝ)
    dsimp only [count]
    rw [he]
  change ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
    _ = (((percolation d p).map S.restrict).prod ((percolation d q).map J.restrict)).real
      localEvent
  rw [event_eq, ← map_measureReal_apply read_meas (Set.toFinite localEvent).measurableSet,
    section9_revealed_two_stage_block_law p q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos S J hdis]

/-- The actual Section 9 geometry keeps every critical coordinate used by the
opened-target event outside both incident reveal masks. -/
theorem section9_opened_target_support_disjoint {d : ℕ} (i : Fin d)
    {n : ℕ} (hn : 0 < n) (F₁ F₃ : Finset (Vertex d)) :
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2 * (n : ℝ))
    let L := section9FiniteTube i n (-(5 : ℝ) / 8) (3 / 8)
    let R := section9FiniteTube i n (-(3 : ℝ) / 8) (5 / 8)
    Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃)
      ((sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃) ∪
        internalBondSet (section9FiniteMiddle i n)) := by
  intro Q₁ Q₃ L R
  have hLQ₃ : Disjoint L Q₃ := section9FiniteLeftTube_disjoint_third i hn
  have hRQ₁ : Disjoint R Q₁ := section9FiniteRightTube_disjoint_first i hn
  have hs := sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁
  apply Finset.disjoint_left.mpr
  intro b hb hsupport
  rcases Finset.mem_union.mp hsupport with havailable | hmiddle
  · exact Finset.disjoint_left.mp hs hb havailable
  · have hends := (mem_internalBondSet _ b).mp hmiddle
    have hboth : b.1 ∈ L ∩ R := by
      change b.1 ∈ section9FiniteTube i n (-(5 : ℝ) / 8) (3 / 8) ∩
        section9FiniteTube i n (-(3 : ℝ) / 8) (5 / 8)
      rw [← section9FiniteMiddle_eq_inter]
      exact hends.1
    rcases Finset.mem_union.mp hb with h₁ | h₃
    · exact Finset.disjoint_left.mp hRQ₁ (Finset.mem_inter.mp hboth).2
        ((mem_clusterRevealBonds Q₁ F₁ b).mp h₁).1
    · exact Finset.disjoint_left.mp hLQ₃ (Finset.mem_inter.mp hboth).1
        ((mem_clusterRevealBonds Q₃ F₃ b).mp h₃).1

end NearCritical
