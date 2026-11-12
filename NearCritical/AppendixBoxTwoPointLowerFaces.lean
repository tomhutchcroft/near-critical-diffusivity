module
public import NearCritical.AppendixBoxTwoPointLowerAll
public import NearCritical.LatticeInversion

/-! lem.box_twopoint_lower (main.tex 6616) for `x` on EITHER face `{z i = ±n}` of `Λ_n`.
The positive face reduces to the negative one by the actual full lattice inversion
(`connectionToSet_probability_inversion`, LatticeInversion): `Λ_n` is inversion
invariant, `x ↦ -x` swaps the two faces, and the coordinatewise margins are preserved.
The explicit inputs are exactly those of `appendix_box_twopoint_lower_negFace`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

theorem neg_mem_centeredBox_iff {d n : ℕ} (x : Vertex d) :
    -x ∈ centeredBox d n ↔ x ∈ centeredBox d n := by
  simp only [mem_centeredBox,Pi.neg_apply]
  constructor <;> intro h i <;> have hi := h i <;> constructor <;> omega

/-- The actual restricted cube connection probability is invariant under `x ↦ -x`. -/
theorem centeredBox_connection_inversion {d : ℕ} (p : unitInterval) (n : ℕ) (x y : Vertex d) :
    (percolation d p).real (connectionToSetEvent
      ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) (-x) {-y}) =
    (percolation d p).real (connectionToSetEvent
      ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
  have hQ : Neg.neg '' ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) =
      ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (neg_mem_centeredBox_iff w).mpr hw
    · intro hz
      refine ⟨-z,(neg_mem_centeredBox_iff z).mpr hz,?_⟩
      simp
  have he := connectionToSet_probability_inversion p x
    ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) {y}
  rw [hQ,Set.image_singleton] at he
  exact congrArg ENNReal.toReal he

/-- Conditional lem.box_twopoint_lower on every face of `Λ_n`, at every scale. -/
theorem appendix_box_twopoint_lower {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hreg : ∃ creg : ℝ, 0 < creg ∧ ∀ (i : Fin d) (n : ℕ) (x : Vertex d),
      1 ≤ n → 16 ≤ α*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      creg/(n : ℝ) ≤ appendixBoxClusterMean (criticalPoint d)
        (appendixBoxQ n (Nat.floor (α*(n : ℝ)/8)) i x) x
        (fun C => ((C ∩ appendixBoxF n (Nat.floor (α*(n : ℝ)/8)) i x).card : ℝ)))
    (herr : ∃ Kerr : ℝ, 0 ≤ Kerr ∧ ∀ (i : Fin d) (n r : ℕ) (x : Vertex d),
      1 ≤ n → 1 ≤ r → 16 ≤ α*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      appendixBoxClusterMean (criticalPoint d)
          (appendixBoxQ n (Nat.floor (α*(n : ℝ)/8)) i x) x
          (fun C => appendixBoxErrCluster C (appendixBoxF n (Nat.floor (α*(n : ℝ)/8)) i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ) ∧
      appendixBoxClusterMean (criticalPoint d)
          (appendixBoxQ n (Nat.floor (α*(n : ℝ)/8)) i x) x
          (fun C => appendixBoxErrBoundary C (appendixBoxF n (Nat.floor (α*(n : ℝ)/8)) i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (n : ℕ) (x y : Vertex d), 1 ≤ n →
      (x i = -(n : ℤ) ∨ x i = (n : ℤ)) → (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      c*(n : ℝ)^((1 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
  obtain ⟨c,hc,hneg⟩ := appendix_box_twopoint_lower_negFace hd asymp lower hα0 hα1 hreg herr
  refine ⟨c,hc,?_⟩
  intro i n x y hn hface hx hy
  rcases hface with hxi | hxi
  · exact hneg i n x y hn hxi hx hy
  · have h := hneg i n (-x) (-y) hn (by simp [hxi])
      (fun j hj => by simpa using hx j hj) (fun j => by simpa using hy j)
    rwa [centeredBox_connection_inversion] at h

end NearCritical
