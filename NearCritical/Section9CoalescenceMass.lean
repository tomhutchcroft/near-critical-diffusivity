module

public import NearCritical.Section8Convolution
public import NearCritical.ConnectionToSet
public import NearCritical.ThreePointDiagram
public import NearCritical.SprinklingPivots
public import NearCritical.RandomWalkGenerator

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- A finite family of restricted arms has quadratic Green mass at the
radius of the family, including a possible zero-length arm. -/
theorem section9_restricted_arm_mass_le {d : ℕ} (hd : 2 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (D : Set (Vertex d)) (S : Finset (Vertex d)) (u : Vertex d) (N : ℕ)
    (hS : ∀ x ∈ S, latticeDistance u x ≤ (N : ℝ)) :
    ∑ x ∈ S, (percolation d (criticalPoint d)).real (connectionToSetEvent D u {x}) ≤
      G * (1 + (2 * (d : ℝ) * 3^(d-1)) * (N+1 : ℝ)^2) := by
  calc
    _ ≤ ∑ x ∈ S, G * (max 1 (latticeDistance u x)) ^ ((2 : ℝ) - (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      have hsub : connectionToSetEvent D u {x} ⊆ connectionEvent u x := by
        rintro ω ⟨_, v, hv, _, huv⟩
        have hvx : v = x := hv
        subst v
        have hle : restrictedGraph ω D ≤ openGraph ω := fun _ _ h => h.1
        exact huv.mono hle
      exact (measureReal_mono hsub (measure_ne_top _ _)).trans (green u x)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (Section8.sum_green_ball_le hd N S u hS) hG

/-- Each head is counted at most once per lattice neighbor. -/
theorem section9_oriented_head_mass_le {d : ℕ} (S : Finset (Vertex d))
    (f : Vertex d → ℝ) (hf : ∀ y ∈ S, 0 ≤ f y) :
    ∑ e ∈ orientedLatticePairs S, f e.2 ≤ (2 * (d : ℝ)) * ∑ y ∈ S, f y := by
  classical
  rw [orientedLatticePairs, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  rw [← Finset.sum_filter]
  simp only [Prod.fst, Prod.snd]
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hf y hy)
  exact_mod_cast (Finset.card_le_card (show
    S.filter (fun x => (openGraph (fun _ => true)).Adj x y) ⊆ latticeNeighbors y by
      intro x hx
      exact (mem_latticeNeighbors_iff y x).mpr (Finset.mem_filter.mp hx).2.symm)).trans
        (card_latticeNeighbors_le y)

end NearCritical
