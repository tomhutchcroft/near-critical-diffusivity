import NearCritical.Section10ActualIssuedFlow
import NearCritical.Section10WeightedFreshUnion

/-! The weight and overlap bound used to select the flow read finitely
many bits. Include every reveal atom, every possible route block, and
both layers of each issued bond in the observation. -/

noncomputable section
namespace NearCritical.Section10

open scoped Classical

private theorem trajWeight_congr_sample {d : ℕ} {X : Type*}
    (K : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (z z' : Configuration d × Configuration d)
    (n t : ℕ) (x : X) (f : Fin n → X)
    (h : ∀ j, t ≤ j → j < t+n → ∀ u v, K j u v z = K j u v z') :
    trajWeight K n t x f z = trajWeight K n t x f z' := by
  induction n generalizing t x with
  | zero => rfl
  | succ n ih =>
    simp only [trajWeight]
    rw [h t le_rfl (by omega), ih (t+1) (f 0) (Fin.tail f)]
    intro j hj hj' u v
    exact h j (by omega) (by omega) u v

/-- The actual trajectory weight and overlap bound are local on a finite
observation that also determines the issued network. -/
theorem firstGood_trajectory_observables_local {D d M n : ℕ} (Λ : NestLayout D d)
    (hn : 2*M ≤ n) (U : Finset (Vertex d)) (p q : unitInterval) (ρ κ A B : ℝ)
    (R : NestRule D M d p q ρ κ Λ.X Λ.Φ)
    (hReveal : ∀ z, R.ρ z = refineReveal Λ.ρ₀ Λ.S₀ z)
    (hBlock : ∀ G ℓ, R.Bl G ℓ = Λ.Bl₀ G.1 ℓ) :
    ∃ O : Finset (LBond d),
      (∀ e : IssuedBond U, ∀ b : Bool, (b,e.val) ∈ O) ∧
      IsLocal O (routeWeightSum (routeLaw D M) R.ρ R.w R.kernel (fun _ _ => n) R.x₀) ∧
      IsLocal O (fun z => Λ.trajectoryChargeSum R n z A B) := by
  let T := (Finset.univ : Finset Λ.Φ).biUnion fun G =>
    R.S G ∪ (Finset.univ : Finset (SourceRoute D M)).biUnion fun γ =>
      (Finset.range n).biUnion fun j => R.Bl G (routeLab M γ.position j)
  let E := (Finset.univ : Finset Bool).product (issuedBondSet U)
  let O := T ∪ E
  have hS (G : Λ.Φ) : R.S G ⊆ O := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨G,Finset.mem_univ _,
      Finset.mem_union_left _ he⟩)
  have hB (G : Λ.Φ) (γ : SourceRoute D M) (j : ℕ) (hj : j < n) :
      R.Bl G (routeLab M γ.position j) ⊆ O := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨G,Finset.mem_univ _,
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨γ,Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr hj,he⟩⟩)⟩)
  have hlocal (z z' : Configuration d × Configuration d)
      (hz : ∀ e ∈ O, layerVal z e = layerVal z' e)
      {S : Finset (LBond d)} {f : Configuration d × Configuration d → ℝ}
      (hf : IsLocal S f) (hsub : S ⊆ O) : f z = f z' := by
    obtain ⟨g,hg⟩ := hf
    exact (hg z).trans ((congrArg g (funext fun e => hz e.val (hsub e.property))).trans (hg z').symm)
  have hreveal (z z' : Configuration d × Configuration d)
      (hz : ∀ e ∈ O, layerVal z e = layerVal z' e) : R.ρ z' = R.ρ z := by
    have h := hlocal z z' hz (R.hρ (R.ρ z)) (hS _)
    by_contra hne
    simp only [if_pos rfl, if_neg hne] at h
    exact one_ne_zero h
  let I := SourceRoute D M × (Fin n → Λ.X)
  have hweight (z z' : Configuration d × Configuration d)
      (hz : ∀ e ∈ O, layerVal z e = layerVal z' e)
      (hG : R.ρ z' = R.ρ z) (j : I) : R.trajectoryWeight n z j = R.trajectoryWeight n z' j := by
    have ht : trajWeight (R.kernel j.1 (R.ρ z)) n 0 (R.x₀ j.1 (R.ρ z)) j.2 z =
        trajWeight (R.kernel j.1 (R.ρ z)) n 0 (R.x₀ j.1 (R.ρ z)) j.2 z' :=
      trajWeight_congr_sample _ z z' n 0 _ j.2 (fun k _ hk u v =>
        hlocal z z' hz (stepKernel_isLocal _ _ _ _ v) (hB _ j.1 k (by simpa only [Nat.zero_add] using hk)))
    unfold NestRule.trajectoryWeight
    rw [hG, ht]
  refine ⟨O,fun e b => Finset.mem_union_right _
    (Finset.mem_product.mpr ⟨Finset.mem_univ _,e.property⟩),?_,?_⟩
  · apply ReadsOnly.isLocal
    intro z z' hz
    rw [← R.sum_trajectoryWeight_eq_routeWeightSum, ← R.sum_trajectoryWeight_eq_routeWeightSum]
    exact Finset.sum_congr rfl fun j _ => hweight z z' hz (hreveal z z' hz) j
  · apply ReadsOnly.isLocal
    intro z z' hz
    have hG := hreveal z z' hz
    have hw := hweight z z' hz hG
    have hT (γ γ' : SourceRoute D M) (a b : ℕ → Λ.X) :
        Λ.trajectoryTubeMarks (M := M) γ.position γ'.position a b z =
          Λ.trajectoryTubeMarks (M := M) γ.position γ'.position a b z' := by
      ext ℓ
      simp only [NestLayout.trajectoryTubeMarks,Finset.mem_filter]
      apply and_congr_right
      intro hmem
      have hleft := (Finset.mem_inter.mp (Finset.mem_filter.mp hmem).1).1
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hleft
      have hj' : j < n := (Finset.mem_Ico.mp hj).2.trans_le hn
      have hG' : refineReveal Λ.ρ₀ Λ.S₀ z' = refineReveal Λ.ρ₀ Λ.S₀ z := by
        rw [← hReveal z', ← hReveal z, hG]
      rw [hG']
      refine Iff.of_eq (Λ.firstGoodSharedTubeMark_readsOnly _ _ _ _ _ _ z z' ?_)
      intro e he
      apply hz
      apply hB (R.ρ z) γ j hj'
      rwa [hBlock, hReveal z]
    unfold NestLayout.trajectoryChargeSum
    dsimp only
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hw j, hw l, hG, hT]

end NearCritical.Section10
