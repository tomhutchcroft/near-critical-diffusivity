module

public import NearCritical.SplitCrossPlacementMoment
public import NearCritical.SplitCrossDirectMasses

/-! The counted random variable is a product of terminal counts on the
crossing event. Its expectation is the sum over fixed terminal tuples. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical BigOperators

def crossingPlacementCount {d : ℕ} (t : ℕ) (x : Vertex d) (axis : Fin d)
    (θ : Configuration d) : ℝ :=
  (Section10.crossAll t t x).indicator (fun ω =>
    (∏ i : InteriorIndex d, countIn (splitEnvelope d t : Set (Vertex d))
      (nodeSites t x axis (interiorNode i)) x ω) *
    (∏ k : Fin (4 * d), countIn (splitEnvelope d t : Set (Vertex d))
      (nodeSites t x axis (face k)) x ω)) θ

/-- The two arrays of interior and far-face sites parameterize all terminals. -/
private theorem terminal_reachable_iff {d t : ℕ} (θ : Configuration d) (x : Vertex d)
    (w : InteriorIndex d → Vertex d) (f : Fin (4 * d) → Vertex d) :
    let G := restrictedGraph θ (splitEnvelope d t : Set (Vertex d))
    (∀ v : CrossingTerminal (4 * d), G.Reachable x (terminalPlacement w f v)) ↔
      (∀ i, G.Reachable x (w i)) ∧ (∀ k, G.Reachable x (f k)) := by
  intro G
  constructor
  · intro h
    constructor
    · rintro ⟨k, b⟩
      cases b
      · exact h ⟨cubeDummy k, rfl⟩
      · exact h ⟨exteriorDummy k, rfl⟩
    · intro k
      exact h ⟨face k, rfl⟩
  · rintro ⟨hw, hf⟩ ⟨v, hv⟩
    cases v with
    | cubeDummy k => exact hw (k, false)
    | exteriorDummy k => exact hw (k, true)
    | face k => exact hf k
    | root | spine _ | entry _ | exterior _ => simp [isCrossingTerminal] at hv

private theorem terminal_indicator_eq {d t : ℕ} (x : Vertex d) (hx : x ∈ splitEnvelope d t)
    (axis : Fin d) (ht : 64 ≤ t) (hx₀ : x ∈ centeredBox d ((t - 1) / 32))
    (w : InteriorIndex d → Vertex d) (hw : w ∈ interiorPlacements t x axis)
    (f : Fin (4 * d) → Vertex d) (hf : f ∈ facePlacements t x axis) (θ : Configuration d) :
    let D := (splitEnvelope d t : Set (Vertex d))
    (crossingTerminalEvent t x (terminalPlacement w f)).indicator (fun _ => (1 : ℝ)) θ =
      (Section10.crossAll t t x).indicator (fun _ => (1 : ℝ)) θ *
      (∏ i, (connectionToSetEvent D x {w i}).indicator (fun _ => (1 : ℝ)) θ) *
      (∏ k, (connectionToSetEvent D x {f k}).indicator (fun _ => (1 : ℝ)) θ) := by
  intro D
  have hwD (i : InteriorIndex d) : w i ∈ D :=
    nodeSites_subset_envelope ht hx₀ axis (interiorNode i) (Fintype.mem_piFinset.mp hw i)
  have hfD (k : Fin (4 * d)) : f k ∈ D :=
    nodeSites_subset_envelope ht hx₀ axis (face k) (Fintype.mem_piFinset.mp hf k)
  have hconn (z : Vertex d) (hz : z ∈ D) :
      θ ∈ connectionToSetEvent D x {z} ↔ (restrictedGraph θ D).Reachable x z := by
    simp [connectionToSetEvent, show x ∈ D from hx, hz]
  simp only [Set.indicator_apply, crossingTerminalEvent, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_setOf_eq, terminal_reachable_iff, hconn _ (hwD _), hconn _ (hfD _)]
  by_cases hall : θ ∈ Section10.crossAll t t x
  · by_cases hW : ∀ i, (restrictedGraph θ D).Reachable x (w i)
    · by_cases hF : ∀ k, (restrictedGraph θ D).Reachable x (f k)
      · rw [if_pos ⟨hall, hW, hF⟩, if_pos hall, one_mul]
        rw [Finset.prod_eq_one (fun i _ => if_pos (hW i)),
          Finset.prod_eq_one (fun k _ => if_pos (hF k)), one_mul]
      · obtain ⟨k, hk⟩ := not_forall.mp hF
        rw [if_neg (fun h => hk (h.2.2 k)),
          Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk), mul_zero]
    · obtain ⟨i, hi⟩ := not_forall.mp hW
      rw [if_neg (fun h => hi (h.2.1 i)),
        Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero, zero_mul]
  · rw [if_neg (fun h => hall h.1), if_neg hall, zero_mul, zero_mul]

theorem crossingPlacementCount_eq_sum {d t : ℕ} (ht : 64 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (θ : Configuration d) :
    crossingPlacementCount t x axis θ =
      ∑ w ∈ interiorPlacements t x axis, ∑ f ∈ facePlacements t x axis,
        (crossingTerminalEvent t x (terminalPlacement w f)).indicator (fun _ => (1 : ℝ)) θ := by
  have hxD : x ∈ splitEnvelope d t :=
    nodeSites_subset_envelope ht hx axis root (by simp [nodeSites])
  simp only [crossingPlacementCount, countIn, Finset.prod_univ_sum]
  rw [show (Section10.crossAll t t x).indicator _ θ =
      (Section10.crossAll t t x).indicator (fun _ => (1 : ℝ)) θ *
        ((∑ w ∈ interiorPlacements t x axis, ∏ i,
          (connectionToSetEvent (splitEnvelope d t : Set (Vertex d)) x {w i}).indicator (fun _ => (1 : ℝ)) θ) *
        (∑ f ∈ facePlacements t x axis, ∏ k,
          (connectionToSetEvent (splitEnvelope d t : Set (Vertex d)) x {f k}).indicator (fun _ => (1 : ℝ)) θ)) by
      by_cases h : θ ∈ Section10.crossAll t t x <;>
        simp [h, interiorPlacements, facePlacements]]
  rw [← mul_assoc, Finset.mul_sum (s := interiorPlacements t x axis), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun f hf => (terminal_indicator_eq x hxD axis ht hx w hw f hf θ).symm

theorem integral_crossingPlacementCount {d t : ℕ} (ht : 64 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (p : unitInterval) :
    ∫ θ, crossingPlacementCount t x axis θ ∂percolation d p =
      ∑ w ∈ interiorPlacements t x axis, ∑ f ∈ facePlacements t x axis,
        (percolation d p).real (crossingTerminalEvent t x (terminalPlacement w f)) := by
  simp_rw [crossingPlacementCount_eq_sum ht x hx axis]
  have hI (w : InteriorIndex d → Vertex d) (f : Fin (4 * d) → Vertex d) :
      Integrable ((crossingTerminalEvent t x (terminalPlacement w f)).indicator
        (fun _ => (1 : ℝ))) (percolation d p) :=
    (integrable_const _).indicator (measurableSet_crossingTerminalEvent t x _)
  rw [integral_finset_sum _ (fun w _ => integrable_finset_sum _ (fun f _ => hI w f))]
  apply Finset.sum_congr rfl
  intro w _
  rw [integral_finset_sum _ (fun f _ => hI w f)]
  exact Finset.sum_congr rfl fun f _ => integral_indicator_one (measurableSet_crossingTerminalEvent t x _)

end NearCritical.SplitCrossDirect
