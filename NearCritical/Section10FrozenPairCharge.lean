import NearCritical.Section10ActualIssuedFlow
import NearCritical.Section10TrajectoryMarkReadout
import NearCritical.Section10SharedTubePredecessor
import NearCritical.Section10ActualPrefixMass

noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory
open scoped Classical

def mergedSiteCount {D d M : ℕ} (Λ : NestLayout D d)
    (γ γ' : SourceRoute D M) (s : List PairMove) (h : NestTrace (Λ.X × Λ.X) s.length) : ℕ :=
  ((routeSites M γ.position ∩ routeSites M γ'.position).filter
    (fun w => mergedSiteMark Λ s (routeArrivalRank γ.position w) (routeArrivalRank γ'.position w) h)).card

def mergedTubeCount {D d M : ℕ} (Λ : NestLayout D d)
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (s : List PairMove)
    (h : NestTrace (Λ.X × Λ.X) s.length) (z : Configuration d × Configuration d) : ℕ :=
  ((commonPhysicalTubes M γ.position γ'.position).filter
    (fun ℓ => Λ.mergedTubeMark G ℓ false s (ℓ.rank-1) (ℓ.rank-1) h z)).card

/-- The charge of two trajectories with their reveal fixed, summed over
the merged histories. The outer route and reveal weights are separate. -/
def frozenPairCharge {D d M : ℕ} (Λ : NestLayout D d)
    {p q : unitInterval} {ρ κ : ℝ} (R : NestRule D M d p q ρ κ Λ.X Λ.Φ)
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (s : List PairMove)
    (z : Configuration d × Configuration d) (A B : ℝ) : ℝ :=
  ∑ h : NestTrace (Λ.X × Λ.X) s.length,
    ((2*A+1) * (Λ.mergedSiteCount γ γ' s h:ℝ) +
      B * (Λ.mergedTubeCount γ γ' G s h z:ℝ)) *
      mergedTraceMass (R.kernel γ G) (R.kernel γ' G) z s 0 0 (R.x₀ γ G,R.x₀ γ' G) h

/-- Reindex the frozen charge by the original pair of finite
trajectories. The same site and tube marks appear on each side. -/
theorem frozenPairCharge_eq_trajectories {D d M : ℕ} (Λ : NestLayout D d)
    {p q : unitInterval} {ρ κ : ℝ} (R : NestRule D M d p q ρ κ Λ.X Λ.Φ)
    (hM : 1 ≤ M) (γ γ' : SourceRoute D M) (s : List PairMove)
    {n n' : ℕ} (hL : leftCount s = n) (hR : rightCount s = n')
    (hn : n = 2*M) (hn' : n' = 2*M) (z : Configuration d × Configuration d)
    (G : Λ.Φ) (hG : G = refineReveal Λ.ρ₀ Λ.S₀ z) (A B : ℝ) :
    Λ.frozenPairCharge R γ γ' G s z A B =
      ∑ f : (Fin n → Λ.X) × (Fin n' → Λ.X),
        let x := R.x₀ γ G
        let x' := R.x₀ γ' G
        let l := trajectoryState x f.1
        let r := trajectoryState x' f.2
        ((2*A+1) * ((Λ.trajectorySiteMarks (M := M) γ.position γ'.position l r).card:ℝ) +
          B * ((Λ.trajectoryTubeMarks (M := M) γ.position γ'.position l r z).card:ℝ)) *
          (trajWeight (R.kernel γ G) n 0 x f.1 z * trajWeight (R.kernel γ' G) n' 0 x' f.2 z) := by
  cases hL
  cases hR
  subst G
  let G := refineReveal Λ.ρ₀ Λ.S₀ z
  let n := leftCount s
  let n' := rightCount s
  let X := γ.position
  let Y := γ'.position
  let S := routeSites M X ∩ routeSites M Y
  let T := commonPhysicalTubes M X Y
  let H := NestTrace Λ.X n × NestTrace Λ.X n'
  let F (f : H) :=
    (2*A+1) * (((S.filter (fun w =>
      traceSiteMark Λ n n' f.1 f.2 (routeArrivalRank X w) (routeArrivalRank Y w))).card):ℝ) +
    B * (((T.filter (fun ℓ =>
      Λ.historyTubeMark G ℓ false n n' (ℓ.rank-1) (ℓ.rank-1) f.1 f.2 z)).card):ℝ)
  calc
    _ = ∑ h : NestTrace (Λ.X × Λ.X) s.length,
        F (mergedRouteTraces s h) *
          mergedTraceMass (R.kernel γ G) (R.kernel γ' G) z s 0 0 (R.x₀ γ G,R.x₀ γ' G) h := by
      unfold frozenPairCharge mergedSiteCount mergedTubeCount
      refine Finset.sum_congr rfl fun h _ => ?_
      have he : S.filter (fun w => mergedSiteMark Λ s (routeArrivalRank X w) (routeArrivalRank Y w) h) =
          S.filter (fun w =>
            traceSiteMark Λ n n' (mergedRouteTraces s h).1 (mergedRouteTraces s h).2
              (routeArrivalRank X w) (routeArrivalRank Y w)) :=
        Finset.filter_congr (fun w _ => mergedSiteMark_iff_traceSiteMark Λ s _ _ h)
      dsimp only [F]
      rw [he]
      rfl
    _ = ∑ f : (Fin n → Λ.X) × (Fin n' → Λ.X),
        F (trajectoryTraceEquiv Λ.X n f.1,trajectoryTraceEquiv Λ.X n' f.2) *
          (trajWeight (R.kernel γ G) n 0 (R.x₀ γ G) f.1 z *
            trajWeight (R.kernel γ' G) n' 0 (R.x₀ γ' G) f.2 z) :=
      mergedTraceMass_marked_sum_eq_trajProduct (R.kernel γ G) (R.kernel γ' G) z s 0 0
        (R.x₀ γ G,R.x₀ γ' G) F
    _ = _ := by
      refine Finset.sum_congr rfl fun f _ => ?_
      have hS := Λ.trajectorySiteMarks_eq_traceSiteMarks (M := M) X Y hn hn'
        (R.x₀ γ G) (R.x₀ γ' G) f.1 f.2
      have hT := Λ.trajectoryTubeMarks_eq_traceTubeMarks (M := M) hM X Y hn hn'
        (R.x₀ γ G) (R.x₀ γ' G) f.1 f.2 z
      dsimp only [F]
      rw [hS,hT]

/-- The actual trajectory charge is the sum of frozen pair charges
multiplied by the two route laws and the two revealed cube weights. -/
theorem trajectoryChargeSum_eq_frozenPairCharge {D d M : ℕ} (Λ : NestLayout D d)
    {p q : unitInterval} {ρ κ : ℝ} (R : NestRule D M d p q ρ κ Λ.X Λ.Φ)
    (hM : 1 ≤ M) (z : Configuration d × Configuration d)
    (hG : R.ρ z = refineReveal Λ.ρ₀ Λ.S₀ z) (A B : ℝ) :
    Λ.trajectoryChargeSum R (2*M) z A B =
      ∑ γ : SourceRoute D M, ∑ γ' : SourceRoute D M,
        let G := R.ρ z
        let s := jointRoutePrefix M γ.position γ'.position (2*M)
        (routeLaw D M γ * routeLaw D M γ') * ((R.w γ G * R.w γ' G) *
          Λ.frozenPairCharge R γ γ' G s z A B) := by
  let I := Fin (2*M) → Λ.X
  let H (γ : SourceRoute D M) (f : I) (γ' : SourceRoute D M) (g : I) :=
    let x := trajectoryState (R.x₀ γ (R.ρ z)) f
    let x' := trajectoryState (R.x₀ γ' (R.ρ z)) g
    R.trajectoryWeight (2*M) z (γ,f) * R.trajectoryWeight (2*M) z (γ',g) *
      ((2*A+1) * ((Λ.trajectorySiteMarks (M := M) γ.position γ'.position x x').card:ℝ) +
        B * ((Λ.trajectoryTubeMarks (M := M) γ.position γ'.position x x' z).card:ℝ))
  calc
    _ = ∑ γ : SourceRoute D M, ∑ f : I, ∑ γ' : SourceRoute D M, ∑ g : I, H γ f γ' g := by
      change (∑ j : SourceRoute D M × I, ∑ l : SourceRoute D M × I, H j.1 j.2 l.1 l.2) = _
      simp only [Fintype.sum_prod_type]
    _ = ∑ γ : SourceRoute D M, ∑ γ' : SourceRoute D M, ∑ f : I, ∑ g : I, H γ f γ' g := by
      refine Finset.sum_congr rfl fun γ _ => ?_
      exact Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun γ' _ => ?_
      let s := jointRoutePrefix M γ.position γ'.position (2*M)
      let G := R.ρ z
      change (∑ f : I, ∑ g : I, H γ f γ' g) =
        (routeLaw D M γ * routeLaw D M γ') *
          ((R.w γ G * R.w γ' G) * Λ.frozenPairCharge R γ γ' G s z A B)
      obtain ⟨hL,hR⟩ := jointRoutePrefix_clocks M γ.position γ'.position (2*M)
      rw [Λ.frozenPairCharge_eq_trajectories R hM γ γ' s hL hR rfl rfl z G hG A B]
      simp only [Fintype.sum_prod_type,Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
      unfold H NestRule.trajectoryWeight
      ring

/-- All marks of the frozen pair can be read from the blocks of the
terminal merged schedule. -/
theorem mergedTubeCount_readsOnly {D d M : ℕ} (Λ : NestLayout D d)
    (γ γ' : SourceRoute D M) (G : Λ.Φ)
    (h : NestTrace (Λ.X × Λ.X) (jointRoutePrefix M γ.position γ'.position (2*M)).length) :
    let s := jointRoutePrefix M γ.position γ'.position (2*M)
    let B (δ : SourceRoute D M) j := Λ.Bl₀ G.1 (routeLab M δ.position j)
    ReadsOnly (mergedTraceBlocks (B γ) (B γ') s 0 0) (Λ.mergedTubeCount γ γ' G s h) := by
  intro s B z z' hz
  unfold mergedTubeCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro ℓ hℓ
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ((Finset.mem_inter.mp (Finset.mem_filter.mp hℓ).1).1)
  have hcl : leftCount s = 2*M := (jointRoutePrefix_clocks M γ.position γ'.position (2*M)).1
  have hread : Λ.Bl₀ G.1 ℓ ⊆ mergedTraceBlocks (B γ) (B γ') s 0 0 := by
    rw [← he]
    simpa only [Nat.zero_add] using
      leftBlock_subset_mergedTraceBlocks (B γ) (B γ') s 0 0 j (by rw [hcl]; exact (Finset.mem_Ico.mp hj).2)
  exact ((Λ.mergedTubeMark_readsOnly G ℓ false s (ℓ.rank-1) (ℓ.rank-1) h).mono hread z z' hz).to_iff

theorem frozenPairCharge_local {D d M : ℕ} (Λ : NestLayout D d)
    {p q : unitInterval} {ρ κ : ℝ} (R : NestRule D M d p q ρ κ Λ.X Λ.Φ)
    (hB : ∀ G ℓ, R.Bl G ℓ = Λ.Bl₀ G.1 ℓ) (γ γ' : SourceRoute D M) (G : Λ.Φ) (A B : ℝ) :
    let s := jointRoutePrefix M γ.position γ'.position (2*M)
    let Bl (δ : SourceRoute D M) j := R.Bl G (routeLab M δ.position j)
    IsLocal (mergedTraceBlocks (Bl γ) (Bl γ') s 0 0) (fun z => Λ.frozenPairCharge R γ γ' G s z A B) := by
  intro s Bl
  let T := mergedTraceBlocks (Bl γ) (Bl γ') s 0 0
  have hT (h : NestTrace (Λ.X × Λ.X) s.length) : ReadsOnly T (Λ.mergedTubeCount γ γ' G s h) := by
    simpa only [T,Bl,hB] using Λ.mergedTubeCount_readsOnly γ γ' G h
  unfold frozenPairCharge
  apply isLocal_sum
  intro h
  exact (isLocal_of_readsOnly (hT h) (fun n : ℕ =>
    (2*A+1) * (Λ.mergedSiteCount γ γ' s h:ℝ) + B * (n:ℝ))).mul
    (mergedTraceMass_isLocal (Bl γ) (Bl γ') (R.kernel γ G) (R.kernel γ' G)
      (fun _ _ v => stepKernel_isLocal _ _ _ _ v) (fun _ _ v => stepKernel_isLocal _ _ _ _ v)
      s 0 0 (R.x₀ γ G,R.x₀ γ' G) h)

/-- Combine the two normalized terminal mark counts into the expected
frozen pair charge. -/
theorem frozenPairCharge_integral_le {D d M : ℕ} (Λ : NestLayout D d)
    {p q : unitInterval} {ρ κ : ℝ} (R : NestRule D M d p q ρ κ Λ.X Λ.Φ)
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (A B E F : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) :
    let s := jointRoutePrefix M γ.position γ'.position (2*M)
    let K := R.kernel γ G
    let K' := R.kernel γ' G
    let x := (R.x₀ γ G,R.x₀ γ' G)
    markedPrefixMass p q K K' s 0 0 x (fun h _ => (Λ.mergedSiteCount γ γ' s h:ℝ)) /
      ρ ^ sharedCount s ≤ E →
    markedPrefixMass p q K K' s 0 0 x (fun h z => (Λ.mergedTubeCount γ γ' G s h z:ℝ)) /
      ρ ^ sharedCount s ≤ F →
    (∫ z, Λ.frozenPairCharge R γ γ' G s z A B ∂((percolation d p).prod (percolation d q))) ≤
      ((2*A+1)*E + B*F) * ρ ^ sharedCount s := by
  intro s K K' x hS hT
  let μ := (percolation d p).prod (percolation d q)
  let H := NestTrace (Λ.X × Λ.X) s.length
  let W (h : H) z := mergedTraceMass K K' z s 0 0 x h
  let S (h : H) (_ : Configuration d × Configuration d) := (Λ.mergedSiteCount γ γ' s h:ℝ)
  let T (h : H) z := (Λ.mergedTubeCount γ γ' G s h z:ℝ)
  have hW (h : H) : IsLocal (mergedTraceBlocks (fun i => R.Bl G (routeLab M γ.position i))
      (fun i => R.Bl G (routeLab M γ'.position i)) s 0 0) (W h) :=
    mergedTraceMass_isLocal _ _ K K' (fun _ _ v => stepKernel_isLocal _ _ _ _ v)
      (fun _ _ v => stepKernel_isLocal _ _ _ _ v) s 0 0 x h
  have hI₁ : Integrable (fun z => ∑ h : H, S h z * W h z) μ :=
    integrable_finsetSum _ (fun h _ => ((isLocal_const ∅ (Λ.mergedSiteCount γ γ' s h:ℝ)).mul_union (hW h)).integrable p q)
  have hI₂ : Integrable (fun z => ∑ h : H, T h z * W h z) μ :=
    integrable_finsetSum _ (fun h _ => ((isLocal_of_readsOnly (Λ.mergedTubeCount_readsOnly γ γ' G h)
      (fun n : ℕ => (n:ℝ))).mul_union (hW h)).integrable p q)
  have he (z : Configuration d × Configuration d) :
      Λ.frozenPairCharge R γ γ' G s z A B =
        (2*A+1) * (∑ h : H, S h z * W h z) + B * (∑ h : H, T h z * W h z) := by
    unfold frozenPairCharge
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    dsimp only [S,T,W]
    ring
  change (∫ z, Λ.frozenPairCharge R γ γ' G s z A B ∂μ) ≤ _
  rw [integral_congr_ae (Filter.Eventually.of_forall he),
    integral_add (hI₁.const_mul _) (hI₂.const_mul _),integral_const_mul,integral_const_mul]
  have hS' := (div_le_iff₀ (pow_pos hρ _)).mp hS
  have hT' := (div_le_iff₀ (pow_pos hρ _)).mp hT
  change (2*A+1) * markedPrefixMass p q K K' s 0 0 x S +
    B * markedPrefixMass p q K K' s 0 0 x T ≤ _
  calc
    _ ≤ (2*A+1)*(E*ρ ^ sharedCount s) + B*(F*ρ ^ sharedCount s) :=
      add_le_add (mul_le_mul_of_nonneg_left hS' (by linarith)) (mul_le_mul_of_nonneg_left hT' hB)
    _ = _ := by ring

end NearCritical.Section10.NestLayout
