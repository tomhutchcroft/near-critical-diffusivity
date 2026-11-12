import NearCritical.Section10ActualIssuedTrajectory
import NearCritical.Section10IssuedFlowAverage

noncomputable section
namespace NearCritical.Section10

open scoped Classical

/-- Weight of a route and its trajectory, including the cube weight. -/
def NestRule.trajectoryWeight {D M d : ℕ} {p q : unitInterval} {ρ κ : ℝ}
    {X Φ : Type} [Fintype X] [Fintype Φ] (R : NestRule D M d p q ρ κ X Φ)
    (n : ℕ) (z : Configuration d × Configuration d)
    (j : SourceRoute D M × (Fin n → X)) : ℝ :=
  routeLaw D M j.1 * (R.w j.1 (R.ρ z) *
    trajWeight (R.kernel j.1 (R.ρ z)) n 0 (R.x₀ j.1 (R.ρ z)) j.2 z)

theorem NestRule.sum_trajectoryWeight_eq_routeWeightSum
    {D M d : ℕ} {p q : unitInterval} {ρ κ : ℝ} {X Φ : Type} [Fintype X] [Fintype Φ]
    (R : NestRule D M d p q ρ κ X Φ) (n : ℕ) (z : Configuration d × Configuration d) :
    (∑ j, R.trajectoryWeight n z j) =
      routeWeightSum (routeLaw D M) R.ρ R.w R.kernel (fun _ _ => n) R.x₀ z := by
  rw [Fintype.sum_prod_type]
  unfold routeWeightSum
  apply Finset.sum_congr rfl
  intro γ _
  simp only [NestRule.trajectoryWeight, ← Finset.mul_sum]
  rw [← chainValue_eq_sum_traj]

/-- The weighted count of common sites and tubes for the actual trajectories. -/
def NestLayout.trajectoryChargeSum {D M d : ℕ} (Λ : NestLayout D d)
    {p q : unitInterval} {ρ κ : ℝ} (R : NestRule D M d p q ρ κ Λ.X Λ.Φ)
    (n : ℕ) (z : Configuration d × Configuration d) (A B : ℝ) : ℝ :=
  let I := SourceRoute D M × (Fin n → Λ.X)
  let state (j : I) := trajectoryState (R.x₀ j.1 (R.ρ z)) j.2
  ∑ j : I, ∑ l : I, R.trajectoryWeight n z j * R.trajectoryWeight n z l *
    ((2*A+1) * ((Λ.trajectorySiteMarks (M := M) j.1.position l.1.position (state j) (state l)).card : ℝ) +
      B * ((Λ.trajectoryTubeMarks (M := M) j.1.position l.1.position (state j) (state l) z).card : ℝ))

/-- The weighted average of the actual issued paths is a supported unit
flow. Its energy is controlled by the two trajectory mark counts. -/
theorem actualLayout_issuedFlow_of_half_mass {D M : ℕ} [LinearOrder (Finset (Vertex (D+1)))]
    (hD : 0 < D) (hM : 1 ≤ M) (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
    (MOff Mcoal Kdiam : ℕ) (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
    (z : Configuration (D+1) × Configuration (D+1))
    (m : ℕ) (hm : m+2 = 2*M) (A : ℝ)
    (hmass : 0 ≤ sourceRouteSurvivalMass D M) (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hAbound : 2 * (typ.diameterUpper * (2 * (t : ℝ)) ^ 2) ≤ A)
    (hcount : (k : ℝ) ≤ typ.countLower * (2 * (t : ℝ)) ^ ((D+1)-6)) :
    let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
    let U := translateSites (boxCenter (D+1) t M) (centeredBox (D+1) (boxRadius t M))
    ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
        localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
          (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
            (Λ.view G.1 (routeLab M γ.position j) z))))
      (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)),
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
    let Ω := sprinkleOrConfiguration z.1 z.2
    (1/2 : ℝ) ≤ routeWeightSum (routeLaw D M) R.ρ R.w R.kernel (fun _ _ => m+1+1) R.x₀ z →
    ∃ θ : IssuedBond U → ℝ,
      (issuedNetwork U).IsBoundaryUnitFlow (negativeFace U Λ.i₀) (positiveFace U Λ.i₀) θ ∧
      Network.FlowSupported (domainWeights Ω) θ ∧
      Network.flowEnergy (domainWeights Ω) θ ≤ 4 * Λ.trajectoryChargeSum R (m+1+1) z A Kdiam := by
  intro Λ U hs hsite R Ω hWeight
  let aC := boxCenter (D+1) t M
  let r := boxRadius t M
  let i := Λ.i₀
  let I := SourceRoute D M × (Fin (m+1+1) → Λ.X)
  let x₀ (j : I) := R.x₀ j.1 (R.ρ z)
  let w : I → ℝ := R.trajectoryWeight (m+1+1) z
  let charge (j l : I) : ℝ :=
    (2*A+1) * ((Λ.trajectorySiteMarks (M := M) j.1.position l.1.position
      (trajectoryState (x₀ j) j.2) (trajectoryState (x₀ l) l.2)).card : ℝ) +
    Kdiam * ((Λ.trajectoryTubeMarks (M := M) j.1.position l.1.position
      (trajectoryState (x₀ j) j.2) (trajectoryState (x₀ l) l.2) z).card : ℝ)
  have hW : (1/2 : ℝ) ≤ ∑ j : I, w j := by
    change (1/2 : ℝ) ≤ ∑ j, R.trajectoryWeight (m+1+1) z j
    rw [R.sum_trajectoryWeight_eq_routeWeightSum]
    exact hWeight
  have hK₀ (j : I) (s : ℕ) (u v : Λ.X) (ω : Configuration (D+1) × Configuration (D+1)) :
      0 ≤ R.kernel j.1 (R.ρ z) s u v ω :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (R.hs j.1 (R.ρ z) s u)) v ω
  have htraj₀ (j : I) : 0 ≤ trajWeight (R.kernel j.1 (R.ρ z)) (m+1+1) 0 (x₀ j) j.2 z :=
    trajWeight_nonneg _ (hK₀ j) _ _ _ _ _
  have hμ (j : I) : 0 ≤ routeLaw D M j.1 := routeLaw_nonneg hmass j.1
  have hw (j : I) : 0 ≤ w j := mul_nonneg (hμ j) (mul_nonneg (R.hw0 j.1 _) (htraj₀ j))
  have hsurvive (j : I) (hj : w j ≠ 0) :
      lazyRouteSurvives j.1.1.1 j.1.2 ∧
        0 < R.w j.1 (R.ρ z) ∧
        0 < trajWeight (R.kernel j.1 (R.ρ z)) (m+1+1) 0 (x₀ j) j.2 z := by
    have hjp := lt_of_le_of_ne (hw j) hj.symm
    have hp := pos_of_mul_pos_right hjp (hμ j)
    have hμp := pos_of_mul_pos_left hjp (mul_nonneg (R.hw0 j.1 _) (htraj₀ j))
    refine ⟨?_, pos_of_mul_pos_left hp (htraj₀ j), pos_of_mul_pos_right hp (R.hw0 j.1 _)⟩
    by_contra hn
    apply ne_of_gt hμp
    rw [routeLaw, if_neg hn]
  have hpaths (j : I) (hj : w j ≠ 0) :
      ∃ F : Λ.TrajectoryFootprint j.1 z (U : Set (Vertex (D+1))) (trajectoryState (x₀ j) j.2),
      ∃ (x y : ↥(U : Set (Vertex (D+1))))
        (W : ((openGraph Ω).induce (U : Set (Vertex (D+1)))).Walk x y),
        internalIssuedVertex U x ∈ negativeFace U i ∧
        issuedExitVertex U y i ∈ positiveFace U i ∧ Ω (y.val,i) = true ∧
        External.bondPair (y.val,i) ∈ F.edges ∧
        ∀ e ∈ (W.map (SimpleGraph.Embedding.induce _).toHom).edges, e ∈ F.edges := by
    obtain ⟨hroute,hcube,htraj⟩ := hsurvive j hj
    exact actualLayout_issued_trajectory hD hM typ t ht k hk MOff Mcoal Kdiam p q ρ κ hκ
      hs hsite z j.1 hroute hcube m hm j.2 htraj hcount
  let F (j : I) (hj : w j ≠ 0) := Classical.choose (hpaths j hj)
  let E (j : I) : Finset (Sym2 (Vertex (D+1))) := if hj : w j ≠ 0 then (F j hj).edges else ∅
  have hwalk (j : I) (hj : w j ≠ 0) :
      ∃ (x y : ↥(U : Set (Vertex (D+1))))
        (W : ((openGraph Ω).induce (U : Set (Vertex (D+1)))).Walk x y),
        internalIssuedVertex U x ∈ negativeFace U i ∧
        issuedExitVertex U y i ∈ positiveFace U i ∧ Ω (y.val,i) = true ∧
        External.bondPair (y.val,i) ∈ E j ∧
        ∀ e ∈ (W.map (SimpleGraph.Embedding.induce _).toHom).edges, e ∈ E j := by
    have he : E j = (F j hj).edges := dif_pos hj
    rw [he]
    exact Classical.choose_spec (hpaths j hj)
  have hU : U.Nonempty := by
    refine ⟨aC, ?_⟩
    have hc : (0 : Vertex (D+1)) ∈ centeredBox (D+1) r := by
      apply mem_centeredBox.mpr
      intro j
      change -(r:ℤ) ≤ 0 ∧ 0 ≤ (r:ℤ)
      omega
    simpa only [add_zero] using (mem_translateSites aC _ _).mpr hc
  have hfaces : Disjoint (negativeFace U i) (positiveFace U i) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (lt_irrefl _) (face_data_lt hU hx hy)
  obtain ⟨θ,hθ,hopen,hE⟩ := issued_flow_average_of_surviving_walks U Ω i _ _ hfaces w hw hW E hwalk
  have hsum : (∑ j : I, ∑ l : I, w j * w l * ((E j ∩ E l).card : ℝ)) ≤
      ∑ j : I, ∑ l : I, w j * w l * charge j l := by
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
    by_cases hj : w j = 0
    · simp only [hj, zero_mul, le_rfl]
    by_cases hl : w l = 0
    · simp only [hl, mul_zero, zero_mul, le_rfl]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw j) (hw l))
    have hej : E j = (F j hj).edges := dif_pos hj
    have hel : E l = (F l hl).edges := dif_pos hl
    rw [hej, hel]
    exact actual_trajectory_footprint_overlap typ ht hk hM z (U : Set (Vertex (D+1))) j.1 l.1
      (hsurvive j hj).1 (hsurvive l hl).1 (trajectoryState (x₀ j) j.2) (trajectoryState (x₀ l) l.2)
      (F j hj) (F l hl) hA hAbound
  exact ⟨θ,hθ,hopen,hE.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))⟩

end NearCritical.Section10
