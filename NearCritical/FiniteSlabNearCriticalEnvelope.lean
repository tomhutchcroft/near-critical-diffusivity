module

public import NearCritical.SlabPioneerBoundaryBounds
public import NearCritical.SlabPlaneBounds
public import NearCritical.FiniteSlabIntegral

/-! Actual near-critical finite Russo envelope, deduced from the literal
critical weighted pioneer input. All constants precede the height, parameter,
cutoff and starting height. No desired envelope is assumed in the final result. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical ENNReal

/-- Finite rows inherit the starting-boundary factor from actual whole-plane
convolution; this intermediate transfer assumes only a visible top bound. -/
lemma finiteSlabRowMean_le_start_boundary_of_top_bound {d : ℕ} (p : unitInterval)
    (i : Fin d) (N : ℕ) (k j : ℤ)
    (hk : k ∈ Finset.Icc (0 : ℤ) (N : ℤ)) (hj : j ∈ Finset.Icc (0 : ℤ) (N : ℤ))
    (U : Finset (Vertex d)) {L : ℝ} (hL : 0 ≤ L)
    (htop : ∀ t ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∀ a : ℤ,
      slabPioneerMass p i 0 t a t ≤ ENNReal.ofReal L) :
    finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) j ≤ ((k : ℝ)+1)*L^2 := by
  have hkR : 0 ≤ (k : ℝ)+1 := by
    have h := (Finset.mem_Icc.mp hk).1
    have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    linarith
  apply finiteSlabRowMean_le_of_slabPioneerMass_le p U i 0 (N : ℤ) (Pi.single i k) j
    (mul_nonneg hkR (sq_nonneg L))
  simp only [Pi.single_eq_same]
  apply (slabPioneerMass_le_boundary_distance p i N k j hk hj hL htop).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
  exact (min_le_right _ _).trans (by
    have h := min_le_left (((k+1 : ℤ) : ℝ)) (((j+1 : ℤ) : ℝ))
    simpa only [Int.cast_add, Int.cast_one] using h)

/-- Exact actual physical edge envelope bound from one uniform top bound.
BOTH edge orientations are retained by the already-proved 2d incidence bound. -/
lemma finiteSlabRussoRowEnvelope_le_of_top_bound {d : ℕ} (p : unitInterval)
    (i : Fin d) (N : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (0 : ℤ) (N : ℤ))
    (U : Finset (Vertex d)) {L : ℝ} (hL : 0 ≤ L)
    (htop : ∀ t ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∀ a : ℤ,
      slabPioneerMass p i 0 t a t ≤ ENNReal.ofReal L) :
    finiteSlabRussoRowEnvelope (p : ℝ) U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤
      2*(d : ℝ)*L^3*(N+1 : ℝ)*((k : ℝ)+1) := by
  let f : Vertex d → ℝ := fun v ↦ (percolation d p).real
    (finiteSlabConnectionEvent U i 0 (N : ℤ) (Pi.single i k) v)
  let g : Vertex d → ℝ := fun v ↦ finiteSlabRowMean p U i 0 (N : ℤ) v (N : ℤ)
  have hf : ∀ v ∈ U, 0 ≤ f v := fun _ _ ↦ MeasureTheory.measureReal_nonneg
  have hg : ∀ v ∈ U, g v ≤ L := by
    intro v _
    exact finiteSlabRowMean_le_of_slabPioneerMass_le p U i 0 (N : ℤ) v (N : ℤ) hL
      (htop (N : ℤ) (by simp) (v i))
  have hcard : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N+1 := by
    rw [Int.card_Icc]
    omega
  have hcardR : ((Finset.Icc (0 : ℤ) (N : ℤ)).card : ℝ) = (N : ℝ)+1 := by
    exact_mod_cast hcard
  have hsum : (∑ v ∈ U, f v) ≤ (N+1 : ℝ)*(((k : ℝ)+1)*L^2) := by
    change (∑ v ∈ U, (percolation d p).real
      (finiteSlabConnectionEvent U i 0 (N : ℤ) (Pi.single i k) v)) ≤ _
    rw [finiteSlabRowMean_sum_levels]
    calc
      _ ≤ ∑ _j ∈ Finset.Icc (0 : ℤ) (N : ℤ), ((k : ℝ)+1)*L^2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact finiteSlabRowMean_le_start_boundary_of_top_bound p i N k j hk hj U hL htop
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; rw [hcardR]
  rw [finiteSlabRussoRowEnvelope_eq_actual]
  change (∑ e : internalBondSet U, (f e.val.1*g (bondTip e.val)+f (bondTip e.val)*g e.val.1)) ≤ _
  calc
    _ ≤ 2*(d : ℝ)*L*∑ v ∈ U, f v := finiteSlab_oriented_edge_sum_le U f g L hf hL hg
    _ ≤ 2*(d : ℝ)*L*((N+1 : ℝ)*(((k : ℝ)+1)*L^2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Genuine near-critical actual finite Russo envelope with constants uniform
in ALL slab heights and arbitrary finite cutoffs. The only probabilistic input
is the literal cited weighted critical pioneer estimate, not a desired bound. -/
theorem finiteSlabRussoRowEnvelope_nearCritical_bound_of_weighted {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i B b) :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (N : ℕ) (p : unitInterval), (criticalPoint d : ℝ) ≤ (p : ℝ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        ∀ (U : Finset (Vertex d)) (k : ℤ), k ∈ Finset.Icc (0 : ℤ) (N : ℤ) →
          finiteSlabRussoRowEnvelope (p : ℝ) U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤
            D*(N+1 : ℝ)*((k : ℝ)+1) := by
  obtain ⟨ε,K,hε,hK,hend,hbound⟩ :=
    slabPioneerMass_nearCritical_upper_of_weighted i hB hb hpc hpc1 decay
  refine ⟨ε,1+2*(d : ℝ)*(2*K)^3,hε,by positivity,hend,?_⟩
  intro N p hp hpwin U k hk
  have h := finiteSlabRussoRowEnvelope_le_of_top_bound p i N k hk U
    (by positivity : 0 ≤ 2*K) (hbound N p hp hpwin).1
  apply h.trans
  have hkR : 0 ≤ (k : ℝ)+1 := by
    have h := (Finset.mem_Icc.mp hk).1
    have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 2*(d : ℝ)*(2*K)^3 ≤ 1+2*(d : ℝ)*(2*K)^3)
      (by positivity : 0 ≤ (N+1 : ℝ))) hkR

end NearCritical
