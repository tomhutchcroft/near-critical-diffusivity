module
public import NearCritical.TwoPointAssumption
public import NearCritical.ThreePointDiagram
public import NearCritical.ConnectionToSet

/-! Bind the Appendix B full-space Green envelope to actual critical percolation.
This does not assert the stronger one-sided or two-sided boundary gains. -/
@[expose] public section
noncomputable section
namespace NearCritical.AppendixVariance
open MeasureTheory
open scoped Classical

/-- The natural-valued shell distance equals the actual real supremum distance,
including the zero-dimensional and coincident-endpoint cases. -/
theorem linfDist_cast_eq_latticeDistance {d : ℕ} (x y : Vertex d) :
    (linfDist x y : ℝ) = latticeDistance x y := by
  have hcoord (i : Fin d) : ((x i - y i).natAbs : ℝ) =
      dist (vertexReal x i) (vertexReal y i) := by
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, vertexReal, Real.dist_eq]
  apply le_antisymm
  · unfold linfDist
    apply Finset.sup_induction (p := fun k : ℕ => (k : ℝ) ≤ latticeDistance x y)
    · simpa using latticeDistance_nonneg x y
    · intro a ha b hb
      change ((max a b : ℕ) : ℝ) ≤ latticeDistance x y
      simpa only [Nat.cast_max] using max_le ha hb
    · intro i _
      rw [hcoord]
      exact dist_le_pi_dist (vertexReal x) (vertexReal y) i
  · apply (dist_pi_le_iff (Nat.cast_nonneg (linfDist x y))).mpr
    intro i
    rw [← hcoord]
    exact_mod_cast (Finset.le_sup (f := fun j => (x j - y j).natAbs)
      (Finset.mem_univ i))

private theorem clipped_inverse_power_le (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    (max 1 R) ^ (-(k : ℝ)) ≤ (2 : ℝ)^k / (R+1)^k := by
  have hM : 0 < max 1 R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hR1 : 0 < R+1 := by linarith
  have hbase : R+1 ≤ 2 * max 1 R := by
    have h1 := le_max_left (1 : ℝ) R
    have h2 := le_max_right (1 : ℝ) R
    linarith
  have hp := pow_le_pow_left₀ hR1.le hbase k
  rw [mul_pow] at hp
  rw [Real.rpow_neg hM.le, Real.rpow_natCast]
  apply (le_div_iff₀ (pow_pos hR1 k)).mpr
  calc
    ((max 1 R)^k)⁻¹ * (R+1)^k ≤
        ((max 1 R)^k)⁻¹ * ((2 : ℝ)^k * (max 1 R)^k) :=
      mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (pow_nonneg hM.le k))
    _ = (2 : ℝ)^k := by field_simp

/-- The actual critical Green upper bound supplies the Appendix B envelope.
The coefficient accounts explicitly for the two regularization conventions. -/
theorem twoPointBound_of_criticalSupGreenUpper {d : ℕ} (hd : 2 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    TwoPointBound (twoPoint d (criticalPoint d)) (G * (2 : ℝ)^(d-2)) := by
  intro x y
  refine ⟨twoPoint_nonneg _ _ _, (green x y).trans ?_⟩
  have he : (2 : ℝ)-(d : ℝ) = -((d-2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd]
    push_cast
    ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_left
    (clipped_inverse_power_le (latticeDistance x y) (latticeDistance_nonneg x y) (d-2)) hG
  simpa only [← linfDist_cast_eq_latticeDistance, Nat.cast_add, Nat.cast_one,
    mul_div_assoc] using hb

/-- Standing assumption (A) yields a positive Appendix B coefficient for the
actual critical two-point probabilities, rather than an abstract supplied kernel. -/
theorem twoPointBound_of_asymptotics {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ TwoPointBound (twoPoint d (criticalPoint d)) C := by
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics hd h
  exact ⟨G * (2 : ℝ)^(d-2), mul_pos hG (by positivity),
    twoPointBound_of_criticalSupGreenUpper hd hG.le green⟩

/-- The same coefficient works for every domain-restricted connection.
No boundary-distance improvement is claimed. -/
theorem restricted_twoPointBound {d : ℕ} {C : ℝ}
    (hC : TwoPointBound (twoPoint d (criticalPoint d)) C)
    (S : Set (Vertex d)) :
    TwoPointBound (fun x y => (percolation d (criticalPoint d)).real
      (connectionToSetEvent S x {y})) C := by
  intro x y
  refine ⟨measureReal_nonneg, ?_⟩
  have hsub : connectionToSetEvent S x {y} ⊆ connectionEvent x y := by
    rintro ω ⟨_, z, hz, _, hp⟩
    have hzy : z = y := Set.mem_singleton_iff.mp hz
    subst z
    have hgraph : restrictedGraph ω S ≤ openGraph ω := fun _ _ h => h.1
    exact hp.mono hgraph
  exact (measureReal_mono (μ := percolation d (criticalPoint d)) hsub
    (measure_ne_top _ _)).trans (hC x y).2

end NearCritical.AppendixVariance
