module

public import NearCritical.Section10MarkedCount
public import NearCritical.Section10ArrivalTubeEntry
public import NearCritical.Section10RecordedArrivalValid
public import NearCritical.Section10MergedArrivalAppend

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- The two nests saved at their actual arrivals have a common cluster. -/
def mergedSiteMark {D d : ℕ} (Λ : NestLayout D d)
    (s : List PairMove) (a b : ℕ) (h : NestTrace (Λ.X × Λ.X) s.length) : Prop :=
  ∃ y, mergedArrivalStates? s a b h = some y ∧ (y.1.1.val ∩ y.2.1.val).Nonempty

namespace NestLayout

/-- Charge a site collision either to a previously marked shared tube
or to a common cluster among the diagonal occupations of the two nests. -/
theorem firstGood_site_collision_of_diagonal_occupations
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (x : Λ.X × Λ.X)
    (s : List PairMove) (a b : ℕ) (S : Finset (Finset (Vertex d)))
    (T : Finset (LBond d)) (P : NestTrace (Λ.X × Λ.X) s.length → Configuration d × Configuration d → Prop)
    (hP : ∀ h, ReadsOnly T (P h)) {A E : ℝ} :
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    (∀ h z, mergedTraceMass (K γ) (K γ') z s 0 0 x h ≠ 0 →
      ∀ y, mergedArrivalStates? s a b h = some y → y.1.1.val ⊆ S) →
    (∀ C ∈ S, markedPrefixMass p q (K γ) (K γ') s 0 0 x
      (fun h z => if ¬ P h z ∧
        (∃ y, mergedArrivalStates? s a b h = some y ∧ C ∈ y.1.1.val ∧ C ∈ y.2.1.val)
        then 1 else 0) / ρ ^ sharedCount s ≤ A) →
    markedPrefixMass p q (K γ) (K γ') s 0 0 x
      (fun h z => if P h z then 1 else 0) / ρ ^ sharedCount s ≤ E →
    markedPrefixMass p q (K γ) (K γ') s 0 0 x
      (fun h _ => if mergedSiteMark Λ s a b h then 1 else 0) / ρ ^ sharedCount s ≤
      E + (S.card:ℝ) * A := by
  intro K hvalid hocc hmass
  let B (δ : SourceRoute D M) j := Λ.Bl₀ G.1 (routeLab M δ.position j)
  let H := NestTrace (Λ.X × Λ.X) s.length
  let Q (C : Finset (Vertex d)) (h : H) z :=
    ¬ P h z ∧ (∃ y, mergedArrivalStates? s a b h = some y ∧ C ∈ y.1.1.val ∧ C ∈ y.2.1.val)
  let I (h : H) z := if P h z then (1:ℝ) else 0
  let J (h : H) z := ((S.filter fun C => Q C h z).card:ℝ)
  let F (h : H) (_ : Configuration d × Configuration d) :=
    if mergedSiteMark Λ s a b h then (1:ℝ) else 0
  have hk (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) : IsLocal (B δ j) (K δ j u v) :=
    stepKernel_isLocal _ _ _ _ v
  have hn (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) (z : Configuration d × Configuration d) :
      0 ≤ K δ j u v z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs δ G j u)) v z
  have hQ (C : Finset (Vertex d)) (h : H) : ReadsOnly T (Q C h) := by
    intro z z' hz
    unfold Q
    rw [hP h z z' hz]
  have hI (h : H) : IsLocal T (I h) :=
    isLocal_of_readsOnly (hP h) (fun b : Prop => if b then (1:ℝ) else 0)
  have hJ (h : H) : IsLocal T (J h) := by
    refine isLocal_of_readsOnly (P := J h) ?_ id
    intro z z' hz
    unfold J
    apply congrArg (fun S : Finset (Finset (Vertex d)) => (S.card:ℝ))
    apply Finset.filter_congr
    intro C _
    exact (hQ C h z z' hz).to_iff
  have hF (h : H) (z : Configuration d × Configuration d) : 0 ≤ F h z := by
    unfold F
    split_ifs <;> norm_num
  have hsplit (h : H) (z : Configuration d × Configuration d)
      (hnz : mergedTraceMass (K γ) (K γ') z s 0 0 x h ≠ 0) : F h z ≤ I h z + J h z := by
    by_cases hp : P h z
    · have hle : F h z ≤ 1 := by unfold F; split_ifs <;> norm_num
      rw [show I h z = 1 from if_pos hp]
      exact hle.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    · by_cases hF' : mergedSiteMark Λ s a b h
      · obtain ⟨y,hy,C,hC⟩ := hF'
        obtain ⟨hC₁,hC₂⟩ := Finset.mem_inter.mp hC
        have hmem : C ∈ S.filter (fun C => Q C h z) :=
          Finset.mem_filter.mpr ⟨hvalid h z hnz y hy hC₁,hp,y,hy,hC₁,hC₂⟩
        have hc : 0 < (S.filter fun C => Q C h z).card :=
          Finset.card_pos.mpr ⟨C,hmem⟩
        have hc' : (1:ℝ) ≤ J h z := by
          change (1:ℝ) ≤ ((S.filter fun C => Q C h z).card:ℝ)
          exact_mod_cast (show 1 ≤ _ from hc)
        rw [show I h z = 0 from if_neg hp,zero_add]
        exact le_trans (by unfold F; split_ifs <;> norm_num) hc'
      · rw [show I h z = 0 from if_neg hp,show F h z = 0 from if_neg hF',zero_add]
        exact Nat.cast_nonneg _
  have hupper := markedPrefixMass_le_add_of_nonzero p q (B γ) (B γ') (K γ) (K γ')
    (hk γ) (hk γ') (hn γ) (hn γ') s 0 0 x T F I J hI hJ hF hsplit
  have hOcc (C : Finset (Vertex d)) (hC : C ∈ S) :
      markedPrefixMass p q (K γ) (K γ') s 0 0 x
        (fun h z => @ite ℝ (Q C h z) (Classical.propDecidable _) 1 0) / ρ ^ sharedCount s ≤ A := by
    refine (le_of_eq (congrArg (fun m : ℝ => m / ρ ^ sharedCount s) ?_)).trans (hocc C hC)
    apply markedPrefixMass_congr_of_nonzero
    intro h z _
    dsimp only [Q] <;>
      (by_cases hq : ¬ P h z ∧ (∃ y, mergedArrivalStates? s a b h = some y ∧ C ∈ y.1.1.val ∧ C ∈ y.2.1.val)
       · simp only [if_pos hq]
       · simp only [if_neg hq])
  have hc := markedPrefixMass_card_filter_le p q (B γ) (B γ') (K γ) (K γ')
    (hk γ) (hk γ') s 0 0 x S (fun _ => T) Q (fun C _ h => hQ C h) ρ A hOcc
  have hJ' : markedPrefixMass p q (K γ) (K γ') s 0 0 x J / ρ ^ sharedCount s ≤ (S.card:ℝ)*A := by
    refine (le_of_eq (congrArg (fun m : ℝ => m / ρ ^ sharedCount s) ?_)).trans hc
    apply markedPrefixMass_congr_of_nonzero
    intro h z _
    unfold J
    apply congrArg (fun S : Finset (Finset (Vertex d)) => (S.card:ℝ))
    exact (Finset.filter_congr_decidable S (fun C => Q C h z)
      (fun C => Classical.propDecidable (Q C h z))).symm
  calc
    _ ≤ (markedPrefixMass p q (K γ) (K γ') s 0 0 x I +
        markedPrefixMass p q (K γ) (K γ') s 0 0 x J) / ρ ^ sharedCount s :=
      div_le_div_of_nonneg_right hupper (pow_nonneg hρ.le _)
    _ ≤ E + (S.card:ℝ)*A := by rw [add_div]; exact add_le_add hmass hJ'

end NestLayout
end NearCritical.Section10
