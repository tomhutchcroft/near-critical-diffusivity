module

public import NearCritical.SprinklingIntrinsic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Deterministic source eq.pigeonhole.k-nest and fixed-order representative
selection in def.nw.chain. No random exploration or uniform-choice law is claimed. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- Offspring incidence distributes over a finite union of source boundaries.
The side graphs and oriented candidate joining pairs are common to every term;
identifying these data with the source exploration remains a separate obligation. -/
theorem sprinklingOffspring_union {d : ℕ} {ι κ : Type*} [DecidableEq κ]
    (G_L G_R : SimpleGraph (Vertex d)) (nest : Finset ι)
    (sourceBoundary : ι → Finset (Vertex d)) (candidates : Finset κ)
    (targetBoundary : κ → Finset (Vertex d)) (pivots : Finset (Vertex d × Vertex d)) :
    sprinklingOffspring G_L G_R (sprinklingTargetBoundary nest sourceBoundary)
      candidates targetBoundary pivots =
    nest.biUnion (fun c => sprinklingOffspring G_L G_R (sourceBoundary c)
      candidates targetBoundary pivots) := by
  classical
  ext c
  simp only [mem_sprinklingOffspring, sprinklingTargetBoundary, Finset.mem_biUnion]
  constructor
  · rintro ⟨hc, x, ⟨a, ha, hx⟩, y, hy, e, he, hl, hr⟩
    exact ⟨a, ha, hc, x, hx, y, hy, e, he, hl, hr⟩
  · rintro ⟨a, ha, hc, x, hx, y, hy, e, he, hl, hr⟩
    exact ⟨hc, x, ⟨a, ha, hx⟩, y, hy, e, he, hl, hr⟩

/-- The finite pigeonhole step uses cardinal subadditivity and needs no
independence or disjointness between the offspring of different clusters. -/
theorem nest_exists_large_offspring {ι κ : Type*} [DecidableEq κ]
    (nest : Finset ι) (offspring : ι → Finset κ) {k m : ℕ}
    (hk : 0 < k) (hcard : nest.card = k)
    (htotal : k*m ≤ (nest.biUnion offspring).card) :
    ∃ c ∈ nest, m ≤ (offspring c).card := by
  classical
  by_contra h
  have hsmall : ∀ c ∈ nest, (offspring c).card < m := by
    intro c hc
    exact Nat.lt_of_not_ge (fun hm => h ⟨c, hc, hm⟩)
  have hne : nest.Nonempty := Finset.card_pos.mp (by omega)
  have hsum := Finset.sum_lt_sum_of_nonempty hne hsmall
  have hsum' : (∑ c ∈ nest, (offspring c).card) < k*m := by
    simpa only [Finset.sum_const, smul_eq_mul, hcard] using hsum
  have hsub : (nest.biUnion offspring).card ≤ ∑ c ∈ nest, (offspring c).card :=
    Finset.card_biUnion_le
  omega

/-- Source eq.pigeonhole.k-nest: 2k^4 offspring from k source clusters gives
one representative with at least 2k^3 offspring. -/
theorem nest_exists_good_representative {ι κ : Type*} [DecidableEq κ]
    (nest : Finset ι) (offspring : ι → Finset κ) {k : ℕ}
    (hk : 0 < k) (hcard : nest.card = k)
    (htotal : 2*k^4 ≤ (nest.biUnion offspring).card) :
    ∃ c ∈ nest, 2*k^3 ≤ (offspring c).card := by
  apply nest_exists_large_offspring nest offspring hk hcard
  convert htotal using 1
  ring

/-- Good clusters are computed by the actual offspring count threshold. -/
def goodNestRepresentatives {ι κ : Type*} (nest : Finset ι)
    (offspring : ι → Finset κ) (k : ℕ) : Finset ι := by
  classical
  exact nest.filter fun c => 2*k^3 ≤ (offspring c).card

lemma goodNestRepresentatives_nonempty {ι κ : Type*} [DecidableEq κ]
    (nest : Finset ι) (offspring : ι → Finset κ) {k : ℕ}
    (hk : 0 < k) (hcard : nest.card = k)
    (htotal : 2*k^4 ≤ (nest.biUnion offspring).card) :
    (goodNestRepresentatives nest offspring k).Nonempty := by
  classical
  obtain ⟨c, hc, hg⟩ := nest_exists_good_representative nest offspring hk hcard htotal
  exact ⟨c, Finset.mem_filter.mpr ⟨hc, hg⟩⟩

/-- The source first good cluster in a fixed deterministic order. -/
def nestRepresentative {ι κ : Type*} [LinearOrder ι] (nest : Finset ι)
    (offspring : ι → Finset κ) (k : ℕ)
    (hgood : (goodNestRepresentatives nest offspring k).Nonempty) : ι :=
  (goodNestRepresentatives nest offspring k).min' hgood

lemma nestRepresentative_spec {ι κ : Type*} [LinearOrder ι] (nest : Finset ι)
    (offspring : ι → Finset κ) (k : ℕ)
    (hgood : (goodNestRepresentatives nest offspring k).Nonempty) :
    nestRepresentative nest offspring k hgood ∈ nest ∧
      2*k^3 ≤ (offspring (nestRepresentative nest offspring k hgood)).card ∧
      ∀ c ∈ nest, 2*k^3 ≤ (offspring c).card →
        nestRepresentative nest offspring k hgood ≤ c := by
  classical
  have hm := Finset.min'_mem (goodNestRepresentatives nest offspring k) hgood
  have hm' : nestRepresentative nest offspring k hgood ∈ nest ∧
      2*k^3 ≤ (offspring (nestRepresentative nest offspring k hgood)).card :=
    Finset.mem_filter.mp hm
  refine ⟨hm'.1, hm'.2, ?_⟩
  intro c hc hg
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hc, hg⟩)

/-- A good representative has enough offspring to select the next k-nest.
This is existence of the finite subset, not its uniform probability law. -/
theorem nestRepresentative_next_nest {ι κ : Type*} [LinearOrder ι]
    (nest : Finset ι) (offspring : ι → Finset κ) {k : ℕ} (hk : 0 < k)
    (hgood : (goodNestRepresentatives nest offspring k).Nonempty) :
    ∃ next ⊆ offspring (nestRepresentative nest offspring k hgood), next.card = k := by
  have hg := (nestRepresentative_spec nest offspring k hgood).2.1
  have hsq : k ≤ k*k := by nlinarith
  have hcube : k*k ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hsq]
  exact Finset.exists_subset_card_eq (show k ≤
    (offspring (nestRepresentative nest offspring k hgood)).card by omega)

/-- Actual computed offspring incidence supplies the good representative's
existence, rather than assuming that a good cluster has already been chosen. -/
theorem sprinkling_nest_good_nonempty {d : ℕ} {ι κ : Type*} [DecidableEq κ]
    (G_L G_R : SimpleGraph (Vertex d)) (nest : Finset ι)
    (sourceBoundary : ι → Finset (Vertex d)) (candidates : Finset κ)
    (targetBoundary : κ → Finset (Vertex d)) (pivots : Finset (Vertex d × Vertex d))
    {k : ℕ} (hk : 0 < k) (hcard : nest.card = k)
    (htotal : 2*k^4 ≤ (sprinklingOffspring G_L G_R
      (sprinklingTargetBoundary nest sourceBoundary) candidates targetBoundary pivots).card) :
    (goodNestRepresentatives nest (fun c => sprinklingOffspring G_L G_R
      (sourceBoundary c) candidates targetBoundary pivots) k).Nonempty := by
  apply goodNestRepresentatives_nonempty nest _ hk hcard
  rwa [← sprinklingOffspring_union G_L G_R nest sourceBoundary candidates targetBoundary pivots]

lemma intrinsicBoundaryRadius_mono {V : Type*} (G : SimpleGraph V) (root : V)
    {A B : Finset V} (hAB : A ⊆ B) :
    intrinsicBoundaryRadius G root A ≤ intrinsicBoundaryRadius G root B := by
  classical
  unfold intrinsicBoundaryRadius
  apply Finset.sup_le
  intro x hx
  exact Finset.le_sup (f := fun z => G.dist z root) (Finset.mem_filter.mpr ⟨hAB (Finset.mem_filter.mp hx).1,
    (Finset.mem_filter.mp hx).2⟩)

lemma sprinklingIntrinsicDiameter_mono {d : ℕ} (G_L G_R : SimpleGraph (Vertex d))
    {A A' B B' : Finset (Vertex d)} {pivots pivots' : Finset (Vertex d × Vertex d)}
    (hA : A ⊆ A') (hB : B ⊆ B') (hp : pivots ⊆ pivots') :
    sprinklingIntrinsicDiameter G_L G_R A B pivots ≤
      sprinklingIntrinsicDiameter G_L G_R A' B' pivots' := by
  unfold sprinklingIntrinsicDiameter
  apply Nat.add_le_add_left
  apply Finset.sup_le
  intro e he
  exact (Nat.add_le_add (intrinsicBoundaryRadius_mono G_L e.1 hA)
    (intrinsicBoundaryRadius_mono G_R e.2 hB)).trans (Finset.le_sup (f := fun q : Vertex d × Vertex d =>
      intrinsicBoundaryRadius G_L q.1 A' + intrinsicBoundaryRadius G_R q.2 B') (hp he))

/-- The deterministic source step, with no assumed good representative or short
bridge: a typical nest's total offspring count and whole-nest rin bound produce
the first good representative, a next k-subset, and short connections into ALL
of its offspring. Stochastic typicality and exploration identification are not
proved here. -/
theorem sprinkling_nest_selected_step {d : ℕ} {ι κ : Type*}
    [LinearOrder ι] [DecidableEq κ] {ω : Configuration d}
    (D L R Q₁ F₁ Q₂ F₂ : Set (Vertex d))
    (hLD : L ⊆ D) (hRD : R ⊆ D) (hLQ : Disjoint L Q₂) (hRQ : Disjoint R Q₁)
    {G_L G_R : SimpleGraph (Vertex d)}
    (hGL : G_L ≤ microscopicPieceGraph ω L (exploredEdgeSet Q₁ F₁)ᶜ)
    (hGR : G_R ≤ microscopicPieceGraph ω R (exploredEdgeSet Q₂ F₂)ᶜ)
    (nest : Finset ι) (sourceBoundary : ι → Finset (Vertex d))
    (candidates : Finset κ) (targetBoundary : κ → Finset (Vertex d))
    (pivots : Finset (Vertex d × Vertex d)) {k : ℕ}
    (hk : 0 < k) (hcard : nest.card = k)
    (htotal : 2*k^4 ≤ (sprinklingOffspring G_L G_R
      (sprinklingTargetBoundary nest sourceBoundary) candidates targetBoundary pivots).card)
    (hAL : ∀ c ∈ nest, ∀ x ∈ sourceBoundary c, x ∈ L)
    (hpivots : ∀ e ∈ pivots, e.2 ∈ R ∧ (openGraph ω).Adj e.1 e.2)
    {K : ℝ} (hdiam : (sprinklingIntrinsicDiameter G_L G_R
      (sprinklingTargetBoundary nest sourceBoundary)
      (sprinklingTargetBoundary candidates targetBoundary) pivots : ℝ) ≤ K) :
    ∃ rep ∈ nest,
      2*k^3 ≤ (sprinklingOffspring G_L G_R (sourceBoundary rep)
        candidates targetBoundary pivots).card ∧
      (∀ c ∈ nest, 2*k^3 ≤ (sprinklingOffspring G_L G_R (sourceBoundary c)
        candidates targetBoundary pivots).card → rep ≤ c) ∧
      (∃ next ⊆ sprinklingOffspring G_L G_R (sourceBoundary rep)
        candidates targetBoundary pivots, next.card = k) ∧
      ∀ child ∈ sprinklingOffspring G_L G_R (sourceBoundary rep)
        candidates targetBoundary pivots,
        ∃ x ∈ sourceBoundary rep, ∃ y ∈ targetBoundary child, ∃ a b,
          (a,b) ∈ pivots ∧
          BoundedIntrinsicConnection (sprinklingBridgeGraph G_L G_R a b) x y K ∧
          sprinklingBridgeGraph G_L G_R a b ≤ microscopicPieceGraph ω D
            (exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₂ F₂)ᶜ := by
  classical
  let offspring := fun c => sprinklingOffspring G_L G_R (sourceBoundary c)
    candidates targetBoundary pivots
  have hg : (goodNestRepresentatives nest offspring k).Nonempty :=
    sprinkling_nest_good_nonempty G_L G_R nest sourceBoundary candidates targetBoundary pivots
      hk hcard htotal
  let rep := nestRepresentative nest offspring k hg
  have hs := nestRepresentative_spec nest offspring k hg
  refine ⟨rep, hs.1, hs.2.1, hs.2.2, nestRepresentative_next_nest nest offspring hk hg, ?_⟩
  intro child hc
  have hA : sourceBoundary rep ⊆ sprinklingTargetBoundary nest sourceBoundary := by
    intro x hx
    exact mem_sprinklingTargetBoundary nest sourceBoundary hs.1 hx
  have hm := sprinklingIntrinsicDiameter_mono G_L G_R hA
    (Finset.Subset.refl (sprinklingTargetBoundary candidates targetBoundary))
    (Finset.Subset.refl pivots)
  have hrepdiam : (sprinklingIntrinsicDiameter G_L G_R (sourceBoundary rep)
      (sprinklingTargetBoundary candidates targetBoundary) pivots : ℝ) ≤ K := by
    exact (Nat.cast_le.mpr hm).trans hdiam
  exact sprinkling_offspring_short_bridge D L R Q₁ F₁ Q₂ F₂ hLD hRD hLQ hRQ hGL hGR
    (sourceBoundary rep) candidates targetBoundary pivots (hAL rep hs.1) hpivots hc hrepdiam

end NearCritical
