module

public import NearCritical.Section10ActualBridgeRow

/-! The tube part of phase entry from a spread pair of nests. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory Set
open scoped Classical

variable {D d : ℕ} (Λ : NestLayout D d)

theorem firstGoodSharedTubeMark_iff_exists_pair (G : Λ.Φ) (ℓ : RouteLabel D)
    (N N' : Finset (Finset (Vertex d))) (a b : Bool)
    (z : Configuration d × Configuration d) :
    Λ.firstGoodSharedTubeMark G ℓ N N' a b z ↔
      ∃ C ∈ N, ∃ E ∈ N', Λ.firstGoodSharedTubeMark G ℓ {C} {E} a b z := by
  let w := gluePair G.2 ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z))
  have hb (P : Finset (Finset (Vertex d))) (s : Bool) :
      Λ.firstGoodNestBridge G ℓ P s w =
        P.biUnion (fun C => Λ.firstGoodNestBridge G ℓ {C} s w) := by
    unfold firstGoodNestBridge
    simp only [sprinklingTargetBoundary, Finset.singleton_biUnion]
    exact bridge_of_nest_eq_biUnion _ _ _ _ _ _ _ _ _ _ P (Λ.src G ℓ s)
  change (Λ.firstGoodNestBridge G ℓ N a w ∩ Λ.firstGoodNestBridge G ℓ N' b w).Nonempty ↔ _
  rw [hb N a, hb N' b]
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨hl,hr⟩ := Finset.mem_inter.mp hv
    obtain ⟨C,hC,hCv⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨E,hE,hEv⟩ := Finset.mem_biUnion.mp hr
    exact ⟨C,hC,E,hE,v,Finset.mem_inter.mpr ⟨hCv,hEv⟩⟩
  · rintro ⟨C,hC,E,hE,v,hv⟩
    obtain ⟨hl,hr⟩ := Finset.mem_inter.mp hv
    exact ⟨v,Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨C,hC,hl⟩,
      Finset.mem_biUnion.mpr ⟨E,hE,hr⟩⟩⟩

/-- At a shared tube, sum the H3 row against the spread occupation masses
of the past histories. The weights can be the full weighted prefixes. -/
theorem firstGood_spread_tube_entry_le {H : Type*} [Fintype H]
    (p q : unitInterval) (G : Λ.Φ) (ℓ : RouteLabel D) (a b : Bool)
    (R : Finset (LBond d)) (hd : Disjoint R (Λ.Bl₀ G.1 ℓ))
    (N N' : H → Finset (Finset (Vertex d)))
    (hN : ∀ h, N h ⊆ Λ.fam G ℓ.site) (hN' : ∀ h, N' h ⊆ Λ.fam G ℓ.site)
    (W : H → Configuration d × Configuration d → ℝ)
    (hW : ∀ h, IsLocal R (W h)) (hW₀ : ∀ h z, 0 ≤ W h z)
    {A K : ℝ} (hA : 0 ≤ A) :
    let μ := (percolation d p).prod (percolation d q)
    let S := Λ.fam G ℓ.site
    (∀ C ∈ S, ∀ E ∈ S.erase C,
      (∑ h, if C ∈ N h ∧ E ∈ N' h then (∫ z, W h z ∂μ) else 0) ≤ A) →
    (∀ C ∈ S, (∑ E ∈ S.erase C,
      μ.real {z | Λ.firstGoodSharedTubeMark G ℓ {C} {E} a b z}) ≤ K) →
    (∑ h, ∫ z, ({z | Disjoint (N h) (N' h) ∧
      Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) a b z}).indicator (W h) z ∂μ) ≤
      (S.card:ℝ) * (A*K) := by
  intro μ S hspread hrow
  let I := S.sigma (fun C => S.erase C)
  let B (i : Σ _ : Finset (Vertex d), Finset (Vertex d)) (h : H) :=
    i.1 ∈ N h ∧ i.2 ∈ N' h
  let F (i : Σ _ : Finset (Vertex d), Finset (Vertex d)) :=
    Λ.firstGoodSharedTubeMark G ℓ {i.1} {i.2} a b
  let c (i : Σ _ : Finset (Vertex d), Finset (Vertex d)) := μ.real {z | F i z}
  let m (h : H) := ∫ z, W h z ∂μ
  have hh (h : H) :
      (∫ z, ({z | Disjoint (N h) (N' h) ∧
        Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) a b z}).indicator (W h) z ∂μ) ≤
        ∑ i ∈ I, (if B i h then m h else 0) * c i := by
    let U := {z | ∃ i ∈ I, B i h ∧ F i z}
    have hu' : ReadsOnly (Λ.Bl₀ G.1 ℓ) (fun z => z ∈ U) := by
      intro z z' hz
      unfold U
      apply propext
      constructor
      · rintro ⟨i, hi, hb, hf⟩
        exact ⟨i, hi, hb, (Λ.firstGoodSharedTubeMark_readsOnly G ℓ {i.1} {i.2} a b z z' hz).mp hf⟩
      · rintro ⟨i, hi, hb, hf⟩
        exact ⟨i, hi, hb, (Λ.firstGoodSharedTubeMark_readsOnly G ℓ {i.1} {i.2} a b z z' hz).mpr hf⟩
    have hu : MeasurableSet U := hu'.measurableSet
    have hsub : {z | Disjoint (N h) (N' h) ∧
        Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) a b z} ⊆ U := by
      rintro z ⟨hd', hm⟩
      obtain ⟨C,hC,E,hE,hCE⟩ := (Λ.firstGoodSharedTubeMark_iff_exists_pair G ℓ (N h) (N' h) a b z).mp hm
      have hne : E ≠ C := by
        intro he
        subst E
        exact Finset.disjoint_left.mp hd' hC hE
      exact ⟨⟨C,E⟩,Finset.mem_sigma.mpr ⟨hN h hC,Finset.mem_erase.mpr ⟨hne,hN' h hE⟩⟩,
        ⟨hC,hE⟩,hCE⟩
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall ?_)
      (((hW h).integrable p q).indicator hu) (Filter.Eventually.of_forall ?_)).trans ?_
    · intro z
      by_cases hm : Disjoint (N h) (N' h) ∧ Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) a b z
      <;> simp [Set.indicator_apply, hm, hW₀ h z]
    · intro z
      by_cases hm : Disjoint (N h) (N' h) ∧ Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) a b z
      · have hzu : z ∈ U := hsub hm
        simp [Set.indicator_apply, hm, hzu]
      · by_cases hzu : z ∈ U <;> simp [Set.indicator_apply, hm, hzu, hW₀ h z]
    · have hbound := weighted_fresh_union_le p q R (Λ.Bl₀ G.1 ℓ) hd I (W h) (hW h) (hW₀ h)
        (fun i _ => B i h) F (fun _ _ _ _ _ => rfl)
        (fun i _ => Λ.firstGoodSharedTubeMark_readsOnly G ℓ {i.1} {i.2} a b)
      refine hbound.trans_eq ?_
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : B i h <;> simp [hi, m, c, μ]
  calc
    _ ≤ ∑ h, ∑ i ∈ I, (if B i h then m h else 0) * c i :=
      Finset.sum_le_sum fun h _ => hh h
    _ = ∑ i ∈ I, (∑ h, if B i h then m h else 0) * c i := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ C ∈ S, A * K := by
      rw [Finset.sum_sigma]
      apply Finset.sum_le_sum
      intro C hC
      calc
        _ ≤ ∑ E ∈ S.erase C, A * c ⟨C,E⟩ :=
          Finset.sum_le_sum fun E hE =>
            mul_le_mul_of_nonneg_right (hspread C hC E hE) measureReal_nonneg
        _ ≤ A * K := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hrow C hC) hA
    _ = _ := by simp [nsmul_eq_mul]

end NearCritical.Section10.NestLayout
