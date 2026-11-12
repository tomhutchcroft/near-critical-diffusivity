module

public import NearCritical.Section10SpreadBridgeEntry
public import NearCritical.Section10OffspringTransfer

/-! Quantitative bridge entry from the H3 row on the actual tube law. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- A spread pair's distinct-cluster contribution to a bridge collision is
O(n^(6−d)). The occupation bound is charged before reading the fresh tube. -/
theorem spread_bridge_entry_integral_upper_scale {d : ℕ} {ι : Type*}
    (hd : 5 ≤ d) (asymp : TwoPointAsymptotics d)
    (q₀ : ℝ) (r : ℕ) (hr : 1 ≤ r) (δ A₀ F₀ C₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n:ℝ)^(-2:ℝ) →
      ∀ (Q₁ H₁ F₁ Q₃ H₃ F₃ B V boundary : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      (B.card:ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
      ∀ (S : Finset ι) (X Y : ι → Finset (Vertex d)),
      (S : Set ι).PairwiseDisjoint Y →
      (S.card:ℝ) ≤ C₀ * (n:ℝ)^((d:ℝ)-6) →
      S.biUnion Y ⊆ section9FiniteEndCube i n 0 →
      (∀ y ∈ S.biUnion Y, sourceRegularPoint F₁ V boundary r δ y) →
      ((S.biUnion Y).card:ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
      (∀ x ∈ S, X x ⊆ section9FiniteEndCube i n 0 ∧
        (∀ v ∈ X x, sourceRegularPoint F₁ V boundary r δ v) ∧
        ((X x).card:ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) →
      let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
      let M := section9FiniteMiddle i n
      Disjoint L Q₃ → Disjoint R Q₁ → Disjoint M Q₁ → Disjoint M Q₃ →
      ∀ (R₀ : Finset (LBond d)), Disjoint R₀ (stepReadSet M L R Q₁ F₁ Q₃ F₃) →
      ∀ (G : Configuration d × Configuration d → ℝ), IsLocal R₀ G → (∀ z, 0 ≤ G z) →
      ∀ (J J' : Configuration d × Configuration d → Finset ι), ReadsOnly R₀ J → ReadsOnly R₀ J' →
      ∀ (a : ℝ), 0 ≤ a →
      let μ := (percolation d (criticalPoint d)).prod (percolation d q)
      (∀ x ∈ S, ∀ y ∈ S.erase x,
        (∫ z, ({z | x ∈ J z ∧ y ∈ J' z} : Set (Configuration d × Configuration d)).indicator G z ∂μ) ≤
          a * (n:ℝ)^(12-2*(d:ℝ))) →
      (∫ z, ({z | ∃ x ∈ S, ∃ y ∈ S.erase x, x ∈ J z ∧ y ∈ J' z ∧
        (section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (X x) B ∩
          section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (Y y) B).Nonempty} :
          Set (Configuration d × Configuration d)).indicator G z ∂μ) ≤
        K * a * (n:ℝ)^(6-(d:ℝ)) := by
  obtain ⟨C, hC⟩ := bridge_intersection_probability_row_uniform (ι := ι) hd asymp q₀ r hr δ A₀ F₀
  refine ⟨C₀ * max 0 C, ?_⟩
  intro i n hn q hq Q₁ H₁ F₁ Q₃ H₃ F₃ B V boundary hH₁ hH₃ hpos hB hBc
    S X Y hY hSc hYbox hYreg hYc hX L R M hLQ₃ hRQ₁ hMQ₁ hMQ₃
    R₀ hdis G hG hG₀ J J' hJ hJ' a ha μ hspread
  let F (x y : ι) (z : Configuration d × Configuration d) :=
    (section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (X x) B ∩
      section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (Y y) B).Nonempty
  let ν := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
  have htransfer (x y : ι) : ν.real {z | F x y z} = μ.real {z | F x y z} :=
    revealed_prod_eq_of_readsOnly (criticalPoint d) q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos _ _
      (rawBridgeMeet_readsOnly M L R Q₁ F₁ Q₃ F₃ (X x) (Y y) B)
      (stepReadSet_fresh M L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁ hMQ₁ hMQ₃)
  have hL : L ⊆ centeredBox d (3*n) := fun _ hz => (Finset.mem_filter.mp hz).1
  have hR : R ⊆ centeredBox d (3*n) := fun _ hz => (Finset.mem_filter.mp hz).1
  have hrow (x : ι) (hx : x ∈ S) : ∑ y ∈ S.erase x, μ.real {z | F x y z} ≤ max 0 C := by
    have hsub : (S.erase x).biUnion Y ⊆ S.biUnion Y := by
      intro z hz
      obtain ⟨y, hy, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_biUnion.mpr ⟨y, Finset.erase_subset _ _ hy, hz⟩
    have hpd : ((S.erase x : Finset ι) : Set ι).PairwiseDisjoint Y := by
      intro a ha b hb hab
      exact hY (Finset.erase_subset x S ha) (Finset.erase_subset x S hb) hab
    simp_rw [← htransfer x]
    exact (hC i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ (X x) V boundary
      (S.erase x) Y hpd
      hH₁ hH₃ hLQ₃ hRQ₁ hpos hL hR hB (hX x hx).1 (hsub.trans hYbox)
      (hX x hx).2.1 (fun z hz => hYreg z (hsub hz)) (hX x hx).2.2
      ((by exact_mod_cast Finset.card_le_card hsub :
        (((S.erase x).biUnion Y).card:ℝ) ≤ ((S.biUnion Y).card:ℝ)).trans hYc) hBc).trans
      (le_max_right _ _)
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hpow : (n:ℝ)^((d:ℝ)-6) * (n:ℝ)^(12-2*(d:ℝ)) = (n:ℝ)^(6-(d:ℝ)) := by
    rw [← Real.rpow_add hn']
    congr 1
    ring
  calc
    _ ≤ (S.card:ℝ) * ((a * (n:ℝ)^(12-2*(d:ℝ))) * max 0 C) :=
      spread_bridge_entry_integral_le (criticalPoint d) q M L R Q₁ F₁ Q₃ F₃ B S X Y
        R₀ hdis G hG hG₀ J J' hJ hJ' (mul_nonneg ha (Real.rpow_nonneg hn'.le _)) hspread hrow
    _ ≤ (C₀ * (n:ℝ)^((d:ℝ)-6)) * ((a * (n:ℝ)^(12-2*(d:ℝ))) * max 0 C) :=
      mul_le_mul_of_nonneg_right hSc (mul_nonneg (mul_nonneg ha (Real.rpow_nonneg hn'.le _))
        (le_max_left _ _))
    _ = C₀ * max 0 C * a * ((n:ℝ)^((d:ℝ)-6) * (n:ℝ)^(12-2*(d:ℝ))) := by ring
    _ = _ := by rw [hpow]

end NearCritical.Section10
