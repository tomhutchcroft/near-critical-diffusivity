module

public import NearCritical.AppendixSlabErrorKernels
public import NearCritical.ThreePointTreeGraphDerivation

/-! Actual tree-graph inputs for the two Appendix A error estimates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set Section8 AppendixVariance
open scoped Classical

/-- Apply the actual BK tripod with both specified end-plane legs separated
from the third leg. The final factor is the actual connection to the third
vertex, so the one-sided and end-plane variants use the same inequality. -/
theorem appendix_slab_error_tripod {d : ℕ} (hd : 1 ≤ d) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B) :
    ∃ U V : ℝ, 0 ≤ U ∧ 0 ≤ V ∧ ∀ (Q : Finset (Vertex d)) (i : Fin d) (a b : ℤ),
      (∀ u ∈ Q, a ≤ u i ∧ u i ≤ b) →
      let D := (Q : Set (Vertex d))
      let p := criticalPoint d
      let P (x y : Vertex d) := (percolation d p).real (connectionToSetEvent D x {y})
      let L (u : Vertex d) : ℝ := 1 + (appendixSlabDepth i a b u : ℝ)
      let s (x u : Vertex d) : ℝ := (linfDist x u + 1 : ℕ)
      ∀ x ∈ Q, x i = a → ∀ w ∈ Q, w i = b →
      (∀ v ∈ Q, (percolation d p).real
        (connectionToSetEvent D x {w} ∩ connectionToSetEvent D x {v}) ≤
        (U ^ 2 * V) * ∑ u ∈ Q,
          L u ^ 3 / (s x u ^ d * s w u ^ d) * (1 / s v u ^ (d - 1))) ∧
      (∀ v ∈ Q, v i = b → (percolation d p).real
        (connectionToSetEvent D x {w} ∩ connectionToSetEvent D x {v}) ≤
        U ^ 3 * ∑ u ∈ Q, L u ^ 3 / (s x u ^ d * s w u ^ d * s v u ^ d)) := by
  obtain ⟨U, V, hU, hV, hker⟩ := appendix_slab_error_kernels hd C A B hC hA hB panis arm second
  refine ⟨U, V, hU, hV, ?_⟩
  intro Q i a b hQ D p P L s x hx hxa w hw hwb
  obtain ⟨hone, htwo⟩ := hker Q i a b hQ
  have hP (y u : Vertex d) : 0 ≤ P y u := measureReal_nonneg
  have hL (u : Vertex d) : 0 ≤ L u := by dsimp only [L]; positivity
  have hs (y u : Vertex d) : 0 < s y u := by dsimp only [s]; positivity
  have hsym (y u : Vertex d) : P y u = P u y := by
    dsimp only [P]
    rw [connectionToSetEvent_singleton_symm D y u]
  have hleft (u : Vertex d) (hu : u ∈ Q) :
      P x u * P u w ≤ U ^ 2 * (L u ^ 2 / (s x u ^ d * s w u ^ d)) := by
    rw [hsym u w]
    calc
      _ ≤ (U * L u / s x u ^ d) * (U * L u / s w u ^ d) :=
        mul_le_mul (htwo x hx (Or.inl hxa) u hu) (htwo w hw (Or.inr hwb) u hu)
          (hP w u) (div_nonneg (mul_nonneg hU (hL u)) (pow_nonneg (hs x u).le _))
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  constructor
  · intro v hv
    refine (restricted_tripod_connection_probability_le p Q x w v).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    calc
      _ ≤ (U ^ 2 * (L u ^ 2 / (s x u ^ d * s w u ^ d))) * (V * L u / s v u ^ (d - 1)) :=
        mul_le_mul (hleft u hu) (hone u hu v hv) (hP v u) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  · intro v hv hvb
    refine (restricted_tripod_connection_probability_le p Q x w v).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    calc
      _ ≤ (U ^ 2 * (L u ^ 2 / (s x u ^ d * s w u ^ d))) * (U * L u / s v u ^ d) :=
        mul_le_mul (hleft u hu) (htwo v hv (Or.inr hvb) u hu) (hP v u) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end NearCritical
