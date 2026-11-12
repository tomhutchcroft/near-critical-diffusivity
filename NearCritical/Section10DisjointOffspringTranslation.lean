module

public import NearCritical.Section10ActualOffspringHit
public import NearCritical.Section10DisjointOffspringScale

/-! Freshness and translation of the four-patch disjoint-offspring event. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory Set
open scoped Classical

theorem disjointOffspring_readsOnly {d : ℕ}
    (M L R Q₁ F₁ Q₃ F₃ X Y U V B : Finset (Vertex d)) :
    ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃)
      (fun z => z ∈ disjointOffspringEvent (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ X Y U V B) := by
  intro z z' hz
  have h (A C : Finset (Vertex d)) :
      section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A C =
        section9SprinklingCluster z'.1 z'.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A C :=
    rawBridge_readsOnly M L R Q₁ F₁ Q₃ F₃ A C z z' hz
  simp only [disjointOffspringEvent, Set.mem_setOf_eq, ← section9SprinklingCluster_nonempty_iff]
  rw [h X U, h Y V, h X B, h Y B]

theorem disjointOffspring_translate_probability {d : ℕ} (p q : unitInterval) (c : Vertex d)
    (M L R Q₁ F₁ Q₃ F₃ X Y U V B : Finset (Vertex d)) :
    let μ := (percolation d p).prod (percolation d q)
    μ.real (disjointOffspringEvent (orientedLatticePairs (translateSites c M))
      (translateSites c L) (translateSites c R) (translateSites c Q₁) (translateSites c F₁)
      (translateSites c Q₃) (translateSites c F₃) (translateSites c X) (translateSites c Y)
      (translateSites c U) (translateSites c V) (translateSites c B)) =
      μ.real (disjointOffspringEvent (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ X Y U V B) := by
  intro μ
  let f := Prod.map (translateConfiguration c) (translateConfiguration c)
  let E := disjointOffspringEvent (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ X Y U V B
  have hE : MeasurableSet E := (disjointOffspring_readsOnly M L R Q₁ F₁ Q₃ F₃ X Y U V B).measurableSet
  have heq : disjointOffspringEvent (orientedLatticePairs (translateSites c M))
      (translateSites c L) (translateSites c R) (translateSites c Q₁) (translateSites c F₁)
      (translateSites c Q₃) (translateSites c F₃) (translateSites c X) (translateSites c Y)
      (translateSites c U) (translateSites c V) (translateSites c B) = f ⁻¹' E := by
    ext z
    simp only [Set.mem_preimage, f, E, disjointOffspringEvent, Set.mem_setOf_eq, Prod.map]
    rw [sprinkledPivotalPairs_nonempty_translate, sprinkledPivotalPairs_nonempty_translate,
      section9SprinklingCluster_translate, section9SprinklingCluster_translate, translateSites_disjoint]
  have hf : Measurable f :=
    (measurable_translateConfiguration c).prodMap (measurable_translateConfiguration c)
  have hmap : μ.map f = μ := by
    dsimp only [μ, f]
    rw [← Measure.map_prod_map _ _ (measurable_translateConfiguration c)
      (measurable_translateConfiguration c), percolation_map_translation, percolation_map_translation]
  rw [heq, ← map_measureReal_apply hf hE, hmap]

/-- The H2 product bound for prescribed source and target clusters in
the actual layout, under the independent fresh product law. -/
theorem actualLayout_disjoint_offspring_probability {D : ℕ} (hd : 2 ≤ D+1)
    (asymp : TwoPointAsymptotics (D+1)) (q₀ : ℝ)
    (hp0 : 0 < (criticalPoint (D+1) : ℝ)) (hp1 : (criticalPoint (D+1) : ℝ) < 1)
    (typ : TypicalParameters) (hb : 0 ≤ typ.boundaryUpper) :
    ∃ C : ℝ, ∀ (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ),
      let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
      ∀ (z : Configuration (D+1) × Configuration (D+1)) (ℓ : RouteLabel D),
      let G := refineReveal Λ.ρ₀ Λ.S₀ z
      HasTube M ℓ → ℓ.site ∈ Λ.siteBox → ℓ.target ∈ Λ.siteBox →
      ∀ (q : unitInterval), (q:ℝ) ≤ q₀ * (t:ℝ)^(-2:ℝ) →
      ∀ (A A' B B' : Finset (Vertex (D+1))) (a b : Bool),
        A ∈ Λ.fam G ℓ.site → A' ∈ Λ.fam G ℓ.site →
        B ∈ Λ.fam G ℓ.target → B' ∈ Λ.fam G ℓ.target →
        ((percolation (D+1) (criticalPoint (D+1))).prod (percolation (D+1) q)).real
          (disjointOffspringEvent (orientedLatticePairs (Λ.Mid ℓ))
            (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site)
            (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target) (Λ.src G ℓ a A) (Λ.src G ℓ b A')
            (Λ.tgt G ℓ B) (Λ.tgt G ℓ B')
            (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ))) ≤
          C * (t:ℝ)^(12-2*((D+1:ℕ):ℝ)) := by
  let A₀ := 8 * typ.boundaryUpper
  obtain ⟨C, hC⟩ := disjoint_offspring_probability_upper_scale hd asymp q₀ A₀
  refine ⟨C, ?_⟩
  intro t ht k hk MOff Mcoal Kdiam M Λ z ℓ G hℓ hsite htgt q hq A A' B B' a b hA hA' hB hB'
  let i := dirOf ℓ
  let c := siteCenter t ℓ.site
  let L := section9FiniteTube i t (-(5:ℝ)/8) (3/8)
  let R := section9FiniteTube i t (-(3:ℝ)/8) (5/8)
  let S := section9FiniteMiddle i t
  let Q₁ := section9FiniteEndCube i t 0
  let Q₃ := section9FiniteEndCube i t (2*(t:ℝ))
  let H₁ := typicalHeart t (0 : Vertex (D + 1)) typ.heartRatio
  let H₃ := typicalHeart t (farCenter t (0 : Vertex (D + 1)) i) typ.heartRatio
  let F₁ := translateSites (-c) (Λ.Fat G.1 ℓ.site)
  let F₃ := translateSites (-c) (Λ.Fat G.1 ℓ.target)
  let X (A : Finset (Vertex (D+1))) (a : Bool) := translateSites (-c) (Λ.src G ℓ a A)
  let Y (B : Finset (Vertex (D+1))) := translateSites (-c) (Λ.tgt G ℓ B)
  let Z := translateSites (-c) (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ))
  have ht0 : 0 < t := by omega
  obtain ⟨hH₁,hH₃,hpos,hfresh⟩ :=
    actualLayout_origin_reveal_data typ t ht k hk MOff Mcoal Kdiam M hp0 hp1 z ℓ hℓ hsite htgt
  have hQ₁ : Λ.Q ℓ.site = translateSites c Q₁ := actual_Qsite_eq typ t ht k hk MOff Mcoal Kdiam M ℓ
  have hQ₃ : Λ.Q ℓ.target = translateSites c Q₃ := actual_Qtarget_eq typ t ht k hk MOff Mcoal Kdiam M hℓ
  have hX (A : Finset (Vertex (D+1))) (a : Bool) : X A a ⊆ Q₁ := by
    have hsub : Λ.src G ℓ a A ⊆ Λ.Q ℓ.site := typicalRegularPatch_subset_cube _ _ _ _ _ _ _
    rw [hQ₁] at hsub
    exact fun u hu => mem_translateSites_neg c Q₁ (translateSites_mono _ hsub hu)
  have hY (B : Finset (Vertex (D+1))) (hB : B ∈ Λ.fam G ℓ.target) : Y B ⊆ Z :=
    translateSites_mono _ (fun _ hu => Finset.mem_biUnion.mpr ⟨B,hB,hu⟩)
  have hZ : Z ⊆ Q₃ := by
    have hsub : sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ) ⊆ Λ.Q ℓ.target :=
      Finset.biUnion_subset.mpr fun B _ => Finset.union_subset
        (typicalRegularPatch_subset_cube _ _ _ _ _ _ _) (typicalRegularPatch_subset_cube _ _ _ _ _ _ _)
    rw [hQ₃] at hsub
    exact fun u hu => mem_translateSites_neg c Q₃ (translateSites_mono _ hsub hu)
  have hYc (B : Finset (Vertex (D+1))) (hB : B ∈ Λ.fam G ℓ.target) :
      ((Y B).card:ℝ) ≤ A₀ * (t:ℝ)^(2:ℝ) := by
    rw [show (Y B).card = _ from card_pullback _ _, Real.rpow_two]
    refine (Λ.tgt_card_le G ℓ hB).trans_eq ?_
    change 2 * (typ.boundaryUpper * (2*(t:ℝ))^2) = A₀ * (t:ℝ)^2
    dsimp only [A₀]
    ring
  have hXc (A : Finset (Vertex (D+1))) (a : Bool) (hA : A ∈ Λ.fam G ℓ.site) :
      ((X A a).card:ℝ) ≤ A₀ * (t:ℝ)^(2:ℝ) := by
    rw [show (X A a).card = _ from card_pullback _ _, Real.rpow_two]
    have htyp := ((mem_typicalClusterFamily _ _ _ _ A).mp hA).2
    refine (htyp.2.2.2.2.2.1 (Λ.dir ℓ,true) a).2.trans ?_
    change typ.boundaryUpper * (2*(t:ℝ))^2 ≤ A₀ * (t:ℝ)^2
    have hb' : 0 ≤ typ.boundaryUpper * (t:ℝ)^2 := by positivity
    dsimp only [A₀]
    nlinarith only [hb']
  let μ := (percolation (D+1) (criticalPoint (D+1))).prod (percolation (D+1) q)
  let E := disjointOffspringEvent (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ (X A a) (X A' b) (Y B) (Y B') Z
  have hbound : μ.real E ≤ C * (t:ℝ)^(12-2*((D+1:ℕ):ℝ)) := by
    have he := stepReadSet_revealed_probability_eq (criticalPoint (D+1)) q S L R Q₁ H₁ F₁ Q₃ H₃ F₃
      hH₁ hH₃ hpos hfresh (fun w => w ∈ E) (disjointOffspring_readsOnly S L R Q₁ F₁ Q₃ F₃ _ _ _ _ _)
    have he' : (section9RevealedLaw (criticalPoint (D+1)) Q₁ H₁ Q₃ H₃ F₁ F₃
        |>.prod (percolation (D+1) q)).real E = μ.real E := he
    rw [← he']
    exact hC i t ht0 q hq H₁ H₃ F₁ F₃ (X A a) (X A' b) (Y B) (Y B') Z hH₁ hH₃
      (hX A a) (hX A' b) (hY B hB) (hY B' hB') hZ hpos
      (hXc A a hA) (hXc A' b hA') (hYc B hB) (hYc B' hB')
  have htr := disjointOffspring_translate_probability (criticalPoint (D+1)) q c S L R Q₁ F₁ Q₃ F₃
    (X A a) (X A' b) (Y B) (Y B') Z
  dsimp only at htr
  change _ = μ.real E at htr
  rw [← actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_R_eq typ t ht k hk MOff Mcoal Kdiam M hℓ, ← hQ₁, ← hQ₃] at htr
  simp only [X,Y,Z,F₁,F₃,translateSites_add_neg_cancel] at htr
  exact htr.trans_le hbound

end NearCritical.Section10
