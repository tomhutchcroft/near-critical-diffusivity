import NearCritical.ExternalPercolation

/-!
The model-law bridge between the project's percolation law and the imported
edge-set model of `Percolation.Literature`:

  `(NearCritical.percolation d p).map edgeSetConfig = bondPercolation (zdGraph d) p`.

`NearCritical.percolation d p` is the infinite product of `Ber(true, false, p)`
over the bond index `(base, direction)`; the imported law is Mathlib's
`setBer((zdGraph d).edgeSet, p)` on sets of unordered pairs. The proof has three
steps: (1) a general reindexing of an infinite product along an injection, with
a Dirac default off its range (`infinitePi_map_extendAlong`); (2) the bond
index `(x, i) |-> s(x, x + e_i)` is injective with range the nearest-neighbour
edge set; (3) the coordinate map `Bool -> Prop` and the set-of-predicate
encoding.

This is the hypothesis `hLaw` left open in `ExternalUniqueness`; it is
unconditional.
-/

namespace NearCritical.External
open MeasureTheory ProbabilityTheory Measure
open scoped Classical unitInterval

/-! ### 1. Reindexing an infinite product along an injection -/

section Reindex
variable {α ι X : Type*} [MeasurableSpace X]

/-- Extend a family indexed by `α` to `ι` along `β`, with value `x₀` off the range. -/
noncomputable def extendAlong (β : α → ι) (x₀ : X) (ω : α → X) (z : ι) : X :=
  if h : z ∈ Set.range β then ω h.choose else x₀

lemma extendAlong_apply (β : α → ι) (hβ : Function.Injective β) (x₀ : X) (ω : α → X)
    (a : α) : extendAlong β x₀ ω (β a) = ω a := by
  have h : β a ∈ Set.range β := ⟨a, rfl⟩
  unfold extendAlong
  rw [dif_pos h]
  exact congrArg ω (hβ h.choose_spec)

lemma extendAlong_of_notMem (β : α → ι) (x₀ : X) (ω : α → X) {z : ι}
    (hz : z ∉ Set.range β) : extendAlong β x₀ ω z = x₀ := by
  unfold extendAlong
  rw [dif_neg hz]

lemma measurable_extendAlong (β : α → ι) (x₀ : X) :
    Measurable (extendAlong β x₀ : (α → X) → (ι → X)) := by
  apply measurable_pi_lambda
  intro z
  by_cases hz : z ∈ Set.range β
  · have h : (fun ω : α → X => extendAlong β x₀ ω z) = fun ω => ω hz.choose := by
      funext ω
      unfold extendAlong
      rw [dif_pos hz]
    rw [h]
    exact measurable_pi_apply _
  · have h : (fun ω : α → X => extendAlong β x₀ ω z) = fun _ => x₀ := by
      funext ω
      exact extendAlong_of_notMem β x₀ ω hz
    rw [h]
    exact measurable_const

/-- The coordinate laws of the extended family. -/
noncomputable def extendFamily (β : α → ι) (μ : Measure X) (x₀ : X) (z : ι) : Measure X :=
  if z ∈ Set.range β then μ else dirac x₀

instance extendFamily_isProbabilityMeasure (β : α → ι) (μ : Measure X)
    [IsProbabilityMeasure μ] (x₀ : X) (z : ι) :
    IsProbabilityMeasure (extendFamily β μ x₀ z) := by
  unfold extendFamily
  split_ifs <;> infer_instance

/-- Pushing an i.i.d. infinite product forward along an injective reindexing
gives the product with the same marginal on the range and a Dirac mass off it. -/
theorem infinitePi_map_extendAlong (β : α → ι) (hβ : Function.Injective β)
    (μ : Measure X) [IsProbabilityMeasure μ] (x₀ : X) :
    (infinitePi (fun _ : α => μ)).map (extendAlong β x₀) =
      infinitePi (extendFamily β μ x₀) := by
  refine eq_infinitePi _ fun s t ht => ?_
  rw [map_apply (measurable_extendAlong β x₀)
    (MeasurableSet.pi s.countable_toSet fun z _ => ht z)]
  by_cases hP : ∀ z ∈ s, z ∉ Set.range β → x₀ ∈ t z
  · have hpre : extendAlong β x₀ ⁻¹' ((s : Set ι).pi t) =
        ((s.preimage β hβ.injOn : Finset α) : Set α).pi (fun a => t (β a)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_preimage]
      constructor
      · intro h a ha
        have h' := h (β a) ha
        rwa [extendAlong_apply β hβ] at h'
      · intro h z hz
        by_cases hr : z ∈ Set.range β
        · obtain ⟨a, rfl⟩ := hr
          rw [extendAlong_apply β hβ]
          exact h a hz
        · rw [extendAlong_of_notMem β x₀ ω hr]
          exact hP z hz hr
    rw [hpre, infinitePi_pi _ (fun a _ => ht (β a))]
    have himg : (s.preimage β hβ.injOn).image β ⊆ s := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_preimage.mp ha
    have hsub : (∏ z ∈ (s.preimage β hβ.injOn).image β, extendFamily β μ x₀ z (t z)) =
        ∏ z ∈ s, extendFamily β μ x₀ z (t z) := by
      apply Finset.prod_subset himg
      intro z hz hnot
      have hr : z ∉ Set.range β := by
        rintro ⟨a, rfl⟩
        exact hnot (Finset.mem_image.mpr ⟨a, Finset.mem_preimage.mpr hz, rfl⟩)
      have hx := hP z hz hr
      simp [extendFamily, hr, dirac_apply' _ (ht z), hx]
    rw [← hsub, Finset.prod_image (fun a _ b _ h => hβ h)]
    apply Finset.prod_congr rfl
    intro a _
    have hr : β a ∈ Set.range β := ⟨a, rfl⟩
    simp only [extendFamily, if_pos hr]
  · push_neg at hP
    obtain ⟨z₀, hz₀, hr, hx⟩ := hP
    have hpre : extendAlong β x₀ ⁻¹' ((s : Set ι).pi t) = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_empty_iff_false,
        iff_false]
      intro h
      have h' := h z₀ hz₀
      rw [extendAlong_of_notMem β x₀ ω hr] at h'
      exact hx h'
    rw [hpre, measure_empty]
    symm
    apply Finset.prod_eq_zero hz₀
    simp [extendFamily, hr, dirac_apply' _ (ht z₀), hx]

end Reindex

/-! ### 2. The bond index as an unordered pair -/

/-- The unordered nearest-neighbour pair of a bond index. -/
def bondPair {d : ℕ} (e : Bond d) : Sym2 (Vertex d) := s(e.1, bondTip e)

lemma bondTip_eq_add_single {d : ℕ} (e : Bond d) :
    bondTip e = e.1 + Pi.single e.2 1 := by
  funext k
  by_cases hk : k = e.2
  · subst hk
    simp [bondTip]
  · simp [bondTip, Function.update_of_ne hk, Pi.single_eq_of_ne hk]

lemma bondPair_injective (d : ℕ) : Function.Injective (bondPair : Bond d → Sym2 (Vertex d)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  unfold bondPair at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hxy : x = y := h1
    subst hxy
    have hij : i = j := by
      by_contra hne
      have hc := congrFun h2 i
      simp only [bondTip, Function.update_self, Function.update_of_ne hne] at hc
      omega
    rw [hij]
  · exfalso
    have hx : x = bondTip (y, j) := h1
    have hy : bondTip (x, i) = y := h2
    have hxi := congrFun hx i
    have hyi := congrFun hy i
    simp only [bondTip, Function.update_self] at hyi
    by_cases hij : i = j
    · subst hij
      simp only [bondTip, Function.update_self] at hxi
      omega
    · simp only [bondTip, Function.update_of_ne hij] at hxi
      omega

lemma range_bondPair (d : ℕ) :
    Set.range (bondPair : Bond d → Sym2 (Vertex d)) =
      (Percolation.Literature.LatticeModels.zdGraph d).edgeSet := by
  ext z
  induction z using Sym2.ind with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet, Percolation.Literature.LatticeModels.zdGraph_adj_iff]
    constructor
    · rintro ⟨e, he⟩
      unfold bondPair at he
      refine ⟨e.2, ?_⟩
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [← h1, ← h2]
        exact bondTip_eq_add_single e
      · right
        rw [← h1, ← h2]
        exact bondTip_eq_add_single e
    · rintro ⟨i, h | h⟩
      · refine ⟨(x, i), ?_⟩
        unfold bondPair
        rw [bondTip_eq_add_single, h]
      · refine ⟨(y, i), ?_⟩
        unfold bondPair
        rw [bondTip_eq_add_single, h, Sym2.eq_swap]

/-- Membership in the edge-set encoding, bond by bond. -/
lemma mem_edgeSetConfig_iff {d : ℕ} (ω : Configuration d) (z : Sym2 (Vertex d)) :
    z ∈ edgeSetConfig ω ↔ extendAlong (bondPair : Bond d → Sym2 (Vertex d)) false ω z = true := by
  by_cases hz : z ∈ Set.range (bondPair : Bond d → Sym2 (Vertex d))
  · obtain ⟨e, rfl⟩ := hz
    rw [extendAlong_apply _ (bondPair_injective d)]
    unfold edgeSetConfig bondPair
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · rintro ⟨e', he', hends⟩
      have hpair : bondPair e' = bondPair e := by
        unfold bondPair
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, Sym2.eq_swap]
      rw [← bondPair_injective d hpair]
      exact he'
    · intro he
      exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · rw [extendAlong_of_notMem _ _ _ hz]
    constructor
    · intro hmem
      exfalso
      apply hz
      induction z using Sym2.ind with
      | h x y =>
        unfold edgeSetConfig at hmem
        rw [SimpleGraph.mem_edgeSet] at hmem
        obtain ⟨e, _, hends⟩ := hmem
        refine ⟨e, ?_⟩
        unfold bondPair
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, Sym2.eq_swap]
    · intro h
      exact absurd h (by simp)

/-! ### 3. The law bridge -/

/-- **Model-law bridge.** The edge-set encoding pushes the project's percolation
law forward to the imported Bernoulli bond percolation on the nearest-neighbour
graph of `Z^d`. -/
theorem percolation_map_edgeSetConfig (d : ℕ) (p : unitInterval) :
    (NearCritical.percolation d p).map edgeSetConfig =
      Percolation.Literature.bondPercolation
        (Percolation.Literature.LatticeModels.zdGraph d) p := by
  have hf : Measurable (fun b : Bool => (b = true : Prop)) := Measurable.of_discrete
  -- the encoding factors through the extension and the coordinate map
  have hfactor : (edgeSetConfig : Configuration d → Set (Sym2 (Vertex d))) =
      (fun P : Sym2 (Vertex d) → Prop => {z | P z}) ∘
        (fun (x : Sym2 (Vertex d) → Bool) z => (x z = true : Prop)) ∘
          extendAlong (bondPair : Bond d → Sym2 (Vertex d)) false := by
    funext ω
    ext z
    exact mem_edgeSetConfig_iff ω z
  have hm1 : Measurable (extendAlong (bondPair : Bond d → Sym2 (Vertex d)) false) :=
    measurable_extendAlong _ _
  have hm2 : Measurable (fun (x : Sym2 (Vertex d) → Bool) z => (x z = true : Prop)) :=
    by
      apply measurable_pi_lambda
      intro z
      exact hf.comp (measurable_pi_apply z)
  have hm3 : Measurable (fun P : Sym2 (Vertex d) → Prop => {z | P z}) :=
    MeasurableEquiv.setOfPred.measurable
  -- step 1: reindex
  have h1 : (NearCritical.percolation d p).map
      (extendAlong (bondPair : Bond d → Sym2 (Vertex d)) false) =
      infinitePi (extendFamily (bondPair : Bond d → Sym2 (Vertex d))
        (bernoulliMeasure true false p) false) := by
    unfold NearCritical.percolation
    exact infinitePi_map_extendAlong _ (bondPair_injective d) _ _
  -- step 2: coordinate map
  have hcoord : ∀ z : Sym2 (Vertex d),
      (extendFamily (bondPair : Bond d → Sym2 (Vertex d))
        (bernoulliMeasure true false p) false z).map (fun b : Bool => (b = true : Prop)) =
      bernoulliMeasure (z ∈ (Percolation.Literature.LatticeModels.zdGraph d).edgeSet)
        False p := by
    intro z
    by_cases hz : z ∈ Set.range (bondPair : Bond d → Sym2 (Vertex d))
    · have hzE : (z ∈ (Percolation.Literature.LatticeModels.zdGraph d).edgeSet) = True := by
        rw [← range_bondPair]
        exact eq_true hz
      unfold extendFamily
      rw [if_pos hz, map_bernoulliMeasure' _ _ hf, hzE]
      simp
    · have hzE : (z ∈ (Percolation.Literature.LatticeModels.zdGraph d).edgeSet) = False := by
        rw [← range_bondPair]
        exact eq_false hz
      unfold extendFamily
      rw [if_neg hz, map_dirac' hf, hzE, bernoulliMeasure_self_eq_dirac]
      simp
  have h2 : (infinitePi (extendFamily (bondPair : Bond d → Sym2 (Vertex d))
        (bernoulliMeasure true false p) false)).map
        (fun (x : Sym2 (Vertex d) → Bool) z => (x z = true : Prop)) =
      infinitePi (fun z : Sym2 (Vertex d) =>
        bernoulliMeasure (z ∈ (Percolation.Literature.LatticeModels.zdGraph d).edgeSet)
          False p) := by
    refine (infinitePi_map_pi _
      (f := fun (_ : Sym2 (Vertex d)) (b : Bool) => (b = true : Prop)) (fun _ => hf)).trans ?_
    congr 1
    funext z
    exact hcoord z
  -- assemble
  unfold Percolation.Literature.bondPercolation
  rw [setBernoulli_eq_map, hfactor, ← Measure.map_map hm3 (hm2.comp hm1),
    ← Measure.map_map hm2 hm1, h1, h2]

/-- The imported percolation probability is the project's density. -/
theorem theta_eq_density (d : ℕ) (p : unitInterval) :
    Percolation.Literature.theta (Percolation.Literature.LatticeModels.zdGraph d) 0 p =
      NearCritical.density d p := by
  unfold Percolation.Literature.theta NearCritical.density
  rw [← percolation_map_edgeSetConfig d p,
    map_measureReal_apply (measurable_edgeSetConfig d)
      (Percolation.Literature.measurableSet_percolatesAt_holds (0 : Vertex d)),
    infiniteCluster_preimage]

end NearCritical.External
