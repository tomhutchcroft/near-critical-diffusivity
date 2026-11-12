module

public import NearCritical.FiniteSlabIntegral
public import NearCritical.SlabPlaneBounds
public import NearCritical.SlabGaugeFactorization
public import NearCritical.SlabPioneerExponentialBounds

/-! NEW actual exponential bound for the finite Russo edge/row envelope.
The physical neighboring-height shift is retained through the proved scalar
gauge factorization. No desired probability or derivative bound is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- Actual confined prefix probability with an exponential height gauge. -/
def finiteSlabPrefixGauge {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (N : ℕ) (k : ℤ) (r : ℝ) (v : Vertex d) : ℝ :=
  (percolation d p).real (finiteSlabConnectionEvent U i 0 (N : ℤ) (Pi.single i k) v) *
    Real.exp (r*|(v i : ℝ)-(k : ℝ)|)

/-- Actual confined top-target row with the compensating suffix gauge. -/
def finiteSlabSuffixGauge {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (N : ℕ) (r : ℝ) (v : Vertex d) : ℝ :=
  finiteSlabRowMean p U i 0 (N : ℤ) v (N : ℤ) *
    Real.exp (r*((N : ℝ)-(v i : ℝ)))

lemma finiteSlabPrefixGauge_nonneg {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (N : ℕ) (k : ℤ) (r : ℝ) (v : Vertex d) :
    0 ≤ finiteSlabPrefixGauge p U i N k r v := by
  exact mul_nonneg measureReal_nonneg (Real.exp_nonneg _)

lemma finiteSlabSuffixGauge_nonneg {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (N : ℕ) (r : ℝ) (v : Vertex d) :
    0 ≤ finiteSlabSuffixGauge p U i N r v := by
  exact mul_nonneg (finiteSlabRowMean_nonneg p U i 0 (N : ℤ) v (N : ℤ)) (Real.exp_nonneg _)

/-- Exact finite height partition of the actual prefix gauge. Outside-slab
endpoints contribute zero by the actual connection domain convention. -/
lemma finiteSlabPrefixGauge_sum_eq_levels {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (N : ℕ) (k : ℤ) (r : ℝ) :
    (∑ v ∈ U, finiteSlabPrefixGauge p U i N k r v) =
      ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ),
        finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) j *
          Real.exp (r*|(j : ℝ)-(k : ℝ)|) := by
  unfold finiteSlabPrefixGauge finiteSlabRowMean
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hvi : v i ∈ Finset.Icc (0 : ℤ) (N : ℤ)
  · simp [eq_comm, hvi]
  · have hout : v ∉ finiteHeightSlab i 0 (N : ℤ) ∩ (U : Set (Vertex d)) := by
      intro h
      exact hvi (Finset.mem_Icc.mpr h.1)
    have he := finiteSlabConnectionEvent_empty_of_end_outside U i 0 (N : ℤ) (Pi.single i k) v hout
    simp [he, eq_comm]

/-- The weighted actual prefix mass is bounded using the PROVED source-start
boundary exponential estimate and actual finite-to-infinite row domination.
No gauge mass bound is an assumption. -/
theorem finiteSlabPrefixGauge_sum_le_subcritical {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (U : Finset (Vertex d))
    (N : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (0 : ℤ) (N : ℤ)) :
    (∑ v ∈ U, finiteSlabPrefixGauge p U i N k
      ((b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))) v) ≤
        (N+1 : ℝ)*(4*B/(criticalPoint d : ℝ)^2)^2*((k : ℝ)+1) := by
  let B0 : ℝ := 4*B/(criticalPoint d : ℝ)^2
  let r : ℝ := (b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hk0 : 0 ≤ ((k+1 : ℤ) : ℝ) := by
    have h := (Finset.mem_Icc.mp hk).1
    exact_mod_cast (show (0 : ℤ) ≤ k+1 by omega)
  have hrow (j : ℤ) (hj : j ∈ Finset.Icc (0 : ℤ) (N : ℤ)) :
      finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) j *
        Real.exp (r*|(j : ℝ)-(k : ℝ)|) ≤ ((k+1 : ℤ) : ℝ)*B0^2 := by
    have hA := slabPioneerMass_subcritical_start_boundary_exponential i hB hb hpc
      pioneers p hp N k j hk hj
    have hfinite : finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) j ≤
        ((k+1 : ℤ) : ℝ)*B0^2*Real.exp (-r*|(j : ℝ)-(k : ℝ)|) := by
      apply finiteSlabRowMean_le_of_slabPioneerMass_le p U i 0 (N : ℤ) (Pi.single i k) j
        (by positivity)
      simpa only [Pi.single_eq_same] using hA
    calc
      _ ≤ (((k+1 : ℤ) : ℝ)*B0^2*Real.exp (-r*|(j : ℝ)-(k : ℝ)|)) *
          Real.exp (r*|(j : ℝ)-(k : ℝ)|) :=
        mul_le_mul_of_nonneg_right hfinite (Real.exp_nonneg _)
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        rw [show -r*|(j : ℝ)-(k : ℝ)|+r*|(j : ℝ)-(k : ℝ)| = 0 by ring]
        simp
  rw [finiteSlabPrefixGauge_sum_eq_levels]
  change (∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ),
    finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) j *
      Real.exp (r*|(j : ℝ)-(k : ℝ)|)) ≤ (N+1 : ℝ)*B0^2*((k : ℝ)+1)
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (0 : ℤ) (N : ℤ), ((k+1 : ℤ) : ℝ)*B0^2 :=
      Finset.sum_le_sum hrow
    _ = _ := by
      have hc : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N+1 := by rw [Int.card_Icc]; omega
      simp only [Finset.sum_const, nsmul_eq_mul, hc]
      push_cast
      ring

/-- The suffix gauge is uniformly bounded by the PROVED actual top-plane
exponential estimate. Off-slab sources are handled by actual empty events. -/
theorem finiteSlabSuffixGauge_le_subcritical {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (U : Finset (Vertex d))
    (N : ℕ) (v : Vertex d) :
    finiteSlabSuffixGauge p U i N ((b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))) v ≤
      4*B/(criticalPoint d : ℝ)^2 := by
  let B0 : ℝ := 4*B/(criticalPoint d : ℝ)^2
  let r : ℝ := (b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  by_cases hv : v ∈ finiteHeightSlab i 0 (N : ℤ)
  · have hvn : v i ≤ (N : ℤ) := hv.2
    have hA := slabPioneerMass_top_exponential_subcritical i hB hb hpc pioneers p hp
      0 (N : ℤ) (v i) hvn
    have hc : ((((N : ℤ)-v i).toNat : ℕ) : ℝ) = (N : ℝ)-(v i : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (sub_nonneg.mpr hvn))
    rw [hc] at hA
    have hfinite : finiteSlabRowMean p U i 0 (N : ℤ) v (N : ℤ) ≤
        B0*Real.exp (-r*((N : ℝ)-(v i : ℝ))) := by
      apply finiteSlabRowMean_le_of_slabPioneerMass_le p U i 0 (N : ℤ) v (N : ℤ)
        (by positivity)
      simpa only [B0,r,neg_mul,mul_assoc] using hA
    change finiteSlabRowMean p U i 0 (N : ℤ) v (N : ℤ) *
      Real.exp (r*((N : ℝ)-(v i : ℝ))) ≤ B0
    calc
      _ ≤ (B0*Real.exp (-r*((N : ℝ)-(v i : ℝ)))) *
          Real.exp (r*((N : ℝ)-(v i : ℝ))) :=
        mul_le_mul_of_nonneg_right hfinite (Real.exp_nonneg _)
      _ = B0 := by
        rw [mul_assoc, ← Real.exp_add,
          show -r*((N : ℝ)-(v i : ℝ))+r*((N : ℝ)-(v i : ℝ)) = 0 by ring]
        simp
  · have hout : v ∉ finiteHeightSlab i 0 (N : ℤ) ∩ (U : Set (Vertex d)) := fun h ↦ hv h.1
    have he (y : Vertex d) := finiteSlabConnectionEvent_empty_of_start_outside U i 0 (N : ℤ) v y hout
    have hrow : finiteSlabRowMean p U i 0 (N : ℤ) v (N : ℤ) = 0 := by
      simp only [finiteSlabRowMean, he, measureReal_empty, ite_self, Finset.sum_const_zero]
    simpa only [finiteSlabSuffixGauge, hrow, zero_mul] using hB0.le

/-- Actual finite two-orientation Russo envelope, with the physical neighboring
height loss exp(r) derived by the proved bond gauge. ONLY literal STANDARD
pioneer input and pc positivity remain; no desired envelope is a premise. -/
theorem finiteSlabRussoRowEnvelope_le_subcritical_exponential {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (U : Finset (Vertex d))
    (N : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (0 : ℤ) (N : ℤ)) :
    finiteSlabRussoRowEnvelope (p : ℝ) U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤
      2*(d : ℝ)*(4*B/(criticalPoint d : ℝ)^2)^3*Real.exp (b/2)*
        (N+1 : ℝ)*((k : ℝ)+1)*
          Real.exp (-((b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)))*((N : ℝ)-(k : ℝ))) := by
  let B0 : ℝ := 4*B/(criticalPoint d : ℝ)^2
  let r : ℝ := (b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))
  let f : Vertex d → ℝ := fun v ↦ (percolation d p).real
    (finiteSlabConnectionEvent U i 0 (N : ℤ) (Pi.single i k) v)
  let g : Vertex d → ℝ := fun v ↦ finiteSlabRowMean p U i 0 (N : ℤ) v (N : ℤ)
  let F := finiteSlabPrefixGauge p U i N k r
  let G := finiteSlabSuffixGauge p U i N r
  let Q := Real.exp r*Real.exp (-r*((N : ℝ)-(k : ℝ)))
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hr : 0 ≤ r := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hf : ∀ v, 0 ≤ f v := fun _ ↦ measureReal_nonneg
  have hg : ∀ v, 0 ≤ g v := fun v ↦ finiteSlabRowMean_nonneg p U i 0 (N : ℤ) v (N : ℤ)
  have hF : ∀ v ∈ U, 0 ≤ F v := fun v _ ↦ finiteSlabPrefixGauge_nonneg p U i N k r v
  have hG : ∀ v ∈ U, G v ≤ B0 := fun v _ ↦
    finiteSlabSuffixGauge_le_subcritical i hB hb hpc pioneers p hp U N v
  have hsum : (∑ v ∈ U, F v) ≤ (N+1 : ℝ)*B0^2*((k : ℝ)+1) :=
    finiteSlabPrefixGauge_sum_le_subcritical i hB hb hpc pioneers p hp U N k hk
  have hraw : finiteSlabRussoRowEnvelope (p : ℝ) U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤
      Q*(2*(d : ℝ)*B0*((N+1 : ℝ)*B0^2*((k : ℝ)+1))) := by
    rw [finiteSlabRussoRowEnvelope_eq_actual]
    change (∑ e : internalBondSet U, (f e.val.1*g (bondTip e.val)+f (bondTip e.val)*g e.val.1)) ≤ _
    calc
      _ ≤ ∑ e : internalBondSet U, Q*(F e.val.1*G (bondTip e.val)+F (bondTip e.val)*G e.val.1) := by
        apply Finset.sum_le_sum
        intro e he
        have h := bond_two_orientation_exponential_gauge e.val i (N : ℤ) k hr f g hf hg
        convert! h using 1
      _ = Q*(∑ e : internalBondSet U, (F e.val.1*G (bondTip e.val)+F (bondTip e.val)*G e.val.1)) :=
        by rw [Finset.mul_sum]
      _ ≤ Q*(2*(d : ℝ)*B0*∑ v ∈ U, F v) := mul_le_mul_of_nonneg_left
        (finiteSlab_oriented_edge_sum_le U F G B0 hF hB0.le hG) hQ
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (by positivity)) hQ
  have hgap : 0 ≤ (criticalPoint d : ℝ)-(p : ℝ) := sub_nonneg.mpr hp
  have hgap1 : (criticalPoint d : ℝ)-(p : ℝ) ≤ 1 := by
    linarith [p.2.1,(criticalPoint d).2.2]
  have hsqrt : Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) ≤ 1 := by
    nlinarith [Real.sq_sqrt hgap,Real.sqrt_nonneg ((criticalPoint d : ℝ)-(p : ℝ))]
  have hrex : Real.exp r ≤ Real.exp (b/2) := Real.exp_le_exp.mpr (by
    dsimp [r]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ b/2))
  have hkR : 0 ≤ (k : ℝ)+1 := by
    have h := (Finset.mem_Icc.mp hk).1
    have hr0 : (0 : ℝ) ≤ k := by exact_mod_cast h
    linarith
  let A : ℝ := 2*(d : ℝ)*B0^3*(N+1 : ℝ)*((k : ℝ)+1)*
    Real.exp (-r*((N : ℝ)-(k : ℝ)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ Q*(2*(d : ℝ)*B0*((N+1 : ℝ)*B0^2*((k : ℝ)+1))) := hraw
    _ = A*Real.exp r := by dsimp [A,Q]; ring
    _ ≤ A*Real.exp (b/2) := mul_le_mul_of_nonneg_left hrex hA
    _ = _ := by dsimp [A,B0,r]; ring

end NearCritical
