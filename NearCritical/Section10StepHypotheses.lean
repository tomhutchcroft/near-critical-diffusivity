module

public import NearCritical.Section10RevealPositivity
public import NearCritical.Section10ClusterTranslation
public import NearCritical.Section10StepCardinality

/-! Hypotheses of the Section 9 offspring theorem at an actual step.

* `revealEvent_translate_measure`: the two-cube reveal event is translation
  covariant, so its probability is the same for translated data.
* `NestLayout.src_pairwiseDisjoint`, `NestLayout.tgt_pairwiseDisjoint`: source
  and target patches of distinct typical clusters are disjoint.
* `NestLayout.srcBoundary_card_ge`, `NestLayout.tgtBoundary_card_ge`: lower
  bounds `|A| >= k c_b (2t)^2` and `|B| >= c (2t)^(d-6) c_b (2t)^2` for a nest
  of typical clusters and a pre-good target cube.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem revealEvent_translate_measure {d : ℕ} (p : unitInterval) (a : Vertex d)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) :
    percolation d p (section9RevealEvent (translateSites a Q₁) (translateSites a H₁)
      (translateSites a Q₃) (translateSites a H₃) (translateSites a F₁) (translateSites a F₃)) =
    percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) := by
  have hinj : Function.Injective (translateSites a) :=
    Finset.image_injective (add_right_injective a)
  have hset : section9RevealEvent (translateSites a Q₁) (translateSites a H₁)
      (translateSites a Q₃) (translateSites a H₃) (translateSites a F₁) (translateSites a F₃) =
      (translateConfiguration a) ⁻¹' section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ := by
    ext ω
    show (heartClusterUnion ω (translateSites a Q₁) (translateSites a H₁) = translateSites a F₁ ∧
        heartClusterUnion ω (translateSites a Q₃) (translateSites a H₃) = translateSites a F₃) ↔
      (heartClusterUnion (translateConfiguration a ω) Q₁ H₁ = F₁ ∧
        heartClusterUnion (translateConfiguration a ω) Q₃ H₃ = F₃)
    rw [heartClusterUnion_translate, heartClusterUnion_translate]
    exact and_congr hinj.eq_iff hinj.eq_iff
  rw [hset, ← Measure.map_apply (measurable_translateConfiguration a)
    (measurableSet_section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃), percolation_map_translation]

variable {D d : ℕ} (Λ : NestLayout D d)

lemma NestLayout.fam_disjoint (G : Λ.Φ) (s : RSite D) {C E : Finset (Vertex d)}
    (hC : C ∈ Λ.fam G s) (hE : E ∈ Λ.fam G s) (hne : C ≠ E) : Disjoint C E :=
  finiteClusterFamily_disjoint _ _ ((mem_typicalClusterFamily _ _ _ _ C).mp hC).1
    ((mem_typicalClusterFamily _ _ _ _ E).mp hE).1 hne

lemma typicalRegularPatch_subset_cluster {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (z : Vertex d) (ω : Configuration d) (C : Finset (Vertex d)) (face : Fin d × Bool)
    (plus : Bool) : typicalRegularPatch typ t z ω C face plus ⊆ C :=
  fun _ hx => (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1

theorem NestLayout.src_pairwiseDisjoint (G : Λ.Φ) (ℓ : RouteLabel D) (pl : Bool)
    (nest : Finset (Finset (Vertex d))) (hnest : nest ⊆ Λ.fam G ℓ.site) :
    Set.PairwiseDisjoint (nest : Set (Finset (Vertex d))) (Λ.src G ℓ pl) := by
  intro C hC E hE hne
  exact Finset.disjoint_of_subset_left (typicalRegularPatch_subset_cluster _ _ _ _ _ _ _)
    (Finset.disjoint_of_subset_right (typicalRegularPatch_subset_cluster _ _ _ _ _ _ _)
      (Λ.fam_disjoint G ℓ.site (hnest hC) (hnest hE) hne))

theorem NestLayout.tgt_pairwiseDisjoint (G : Λ.Φ) (ℓ : RouteLabel D) :
    Set.PairwiseDisjoint (Λ.fam G ℓ.target : Set (Finset (Vertex d))) (Λ.tgt G ℓ) := by
  intro C hC E hE hne
  have hsub : ∀ C' : Finset (Vertex d), Λ.tgt G ℓ C' ⊆ C' := by
    intro C'
    unfold NestLayout.tgt
    exact Finset.union_subset (typicalRegularPatch_subset_cluster _ _ _ _ _ _ _)
      (typicalRegularPatch_subset_cluster _ _ _ _ _ _ _)
  exact Finset.disjoint_of_subset_left (hsub C)
    (Finset.disjoint_of_subset_right (hsub E) (Λ.fam_disjoint G ℓ.target hC hE hne))

theorem NestLayout.srcBoundary_card_ge (G : Λ.Φ) (ℓ : RouteLabel D) (pl : Bool)
    (nest : Finset (Finset (Vertex d))) (hnest : nest ⊆ Λ.fam G ℓ.site) :
    (nest.card : ℝ) * (Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2) ≤
      ((sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card : ℝ) := by
  have hcard : (sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card =
      ∑ C ∈ nest, (Λ.src G ℓ pl C).card := by
    unfold sprinklingTargetBoundary
    exact Finset.card_biUnion (Λ.src_pairwiseDisjoint G ℓ pl nest hnest)
  have h2 : ∀ C ∈ nest, Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2 ≤
      ((Λ.src G ℓ pl C).card : ℝ) := by
    intro C hC
    have htyp := ((mem_typicalClusterFamily _ _ _ _ C).mp (hnest hC)).2
    exact (htyp.2.2.2.2.2.1 (Λ.dir ℓ, true) pl).1
  rw [hcard]
  push_cast
  calc (nest.card : ℝ) * (Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2)
      = ∑ _C ∈ nest, Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum h2

theorem NestLayout.tgtBoundary_card_ge (G : Λ.Φ) (ℓ : RouteLabel D)
    (hgood : Λ.goodCube G ℓ.target) (hbL : 0 ≤ Λ.typ.boundaryLower) :
    (Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6)) *
        (Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2) ≤
      ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) := by
  have hcard : (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card =
      ∑ C ∈ Λ.fam G ℓ.target, (Λ.tgt G ℓ C).card := by
    unfold sprinklingTargetBoundary
    exact Finset.card_biUnion (Λ.tgt_pairwiseDisjoint G ℓ)
  have h2 : ∀ C ∈ Λ.fam G ℓ.target, Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2 ≤
      ((Λ.tgt G ℓ C).card : ℝ) := by
    intro C hC
    have htyp := ((mem_typicalClusterFamily _ _ _ _ C).mp hC).2
    have ha := (htyp.2.2.2.2.2.1 (Λ.dir ℓ, false) true).1
    have hle : (typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.target) (Λ.revealConfig G) C
        (Λ.dir ℓ, false) true).card ≤ (Λ.tgt G ℓ C).card :=
      Finset.card_le_card Finset.subset_union_left
    have hle' := (Nat.cast_le (α := ℝ)).mpr hle
    linarith
  have hcount : Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6) ≤
      ((Λ.fam G ℓ.target).card : ℝ) := hgood.1
  have hpos : (0:ℝ) ≤ Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2 := by positivity
  rw [hcard]
  push_cast
  calc (Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6)) *
        (Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2)
      ≤ ((Λ.fam G ℓ.target).card : ℝ) * (Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hcount hpos
    _ = ∑ _C ∈ Λ.fam G ℓ.target, Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum h2

end NearCritical.Section10
