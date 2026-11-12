module

public import NearCritical.FiniteDomainExhaustion
public import NearCritical.PercolationMonotonicity

/-! NEW prop.onearm_half_plus Step 3: finite-domain entropic transfer and
actual exhaustion. Standard DM comparison and unresolved NEW lower-parameter
arm/interior-cluster estimates are distinct, explicit hypotheses. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set

/-- Coordinate point k*e_i in the original integer lattice. -/
def halfSpaceArmBase {d : ℕ} (i : Fin d) (k : ℕ) : Vertex d := Function.update 0 i (k : ℤ)

def halfSpaceArmDomain {d : ℕ} (i : Fin d) : Set (Vertex d) := {x | 0 ≤ x i}
def halfSpaceArmTarget {d : ℕ} (i : Fin d) (n : ℕ) : Set (Vertex d) := {x | (n : ℤ) ≤ x i}

def finiteHalfSpaceArmEvent {d : ℕ} (i : Fin d) (k n R : ℕ) : Set (Configuration d) :=
  connectionToSetEvent (halfSpaceArmDomain i ∩ (latticeSupCube d R : Set (Vertex d)))
    (halfSpaceArmBase i k) (halfSpaceArmTarget i n)

def halfSpaceArmEvent {d : ℕ} (i : Fin d) (k n : ℕ) : Set (Configuration d) :=
  connectionToSetEvent (halfSpaceArmDomain i) (halfSpaceArmBase i k) (halfSpaceArmTarget i n)

noncomputable def finiteHalfSpaceArmProbability {d : ℕ} (i : Fin d) (p : unitInterval) (k n R : ℕ) : ℝ :=
  (percolation d p).real (finiteHalfSpaceArmEvent i k n R)

/-- Finite sum of connection probabilities: expected finite-domain cluster size.
Only vertices in the finite counting cube can belong to this restricted cluster. -/
noncomputable def finiteHalfSpaceClusterSum {d : ℕ} (i : Fin d) (p : unitInterval) (k R : ℕ) : ℝ :=
  ∑ y ∈ latticeSupCube d R, (percolation d p).real
    (connectionToSetEvent (halfSpaceArmDomain i ∩ (latticeSupCube d R : Set (Vertex d)))
      (halfSpaceArmBase i k) {y})

lemma finiteHalfSpaceClusterSum_nonneg {d : ℕ} (i : Fin d) (p : unitInterval) (k R : ℕ) :
    0 ≤ finiteHalfSpaceClusterSum i p k R :=
  Finset.sum_nonneg (fun _ _ => measureReal_nonneg)

/-- Named STANDARD finite-domain DM23 Proposition 1.21 specialization.
No infinite-domain comparison or arm power bound is assumed here. -/
def FiniteHalfSpaceEntropicInput {d : ℕ} (i : Fin d) (E : ℝ) : Prop :=
  ∀ (p q : unitInterval) (k n R : ℕ), 1 ≤ n → 2 * k ≤ n → k ≤ R →
    (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) → (q : ℝ) < (p : ℝ) →
    (p : ℝ) ≤ ((criticalPoint d : ℝ) + 1) / 2 →
    finiteHalfSpaceArmProbability i p k n R - finiteHalfSpaceArmProbability i q k n R ≤
      E * ((p : ℝ) - (q : ℝ)) * Real.sqrt
        (max (finiteHalfSpaceArmProbability i p k n R) (finiteHalfSpaceArmProbability i q k n R) *
          finiteHalfSpaceClusterSum i q k R)

/-- UNRESOLVED NEW Step 1/2 prerequisites, not standard literature inputs:
the subcritical arm estimate (exponential factor discarded) and the interior
cluster bound from the minimum decomposition plus boundary susceptibility.
No supercritical arm probability occurs in this hypothesis. -/
def HalfSpaceLowerTransferPrerequisites {d : ℕ} (i : Fin d) (A S : ℝ) : Prop :=
  ∀ (q : unitInterval) (k n R : ℕ), 1 ≤ n → 2 * k ≤ n → k ≤ R →
    (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) → (q : ℝ) < (criticalPoint d : ℝ) →
    finiteHalfSpaceArmProbability i q k n R ≤ A * ((k + 1 : ℝ) / (n : ℝ) ^ 3) ∧
    finiteHalfSpaceClusterSum i q k R ≤ S * (k + 1 : ℝ) /
      Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ))

/-- The source quadratic closure, without an assumed final power bound. -/
lemma entropic_quadratic_absorption {P a t C : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (h : P ≤ a + t * Real.sqrt (P * C)) : P ≤ 2 * a + t ^ 2 * C := by
  rw [Real.sqrt_mul hP] at h
  have hp := Real.sq_sqrt hP
  have hc : (t * Real.sqrt C) ^ 2 = t ^ 2 * C := by rw [mul_pow, Real.sq_sqrt hC]
  nlinarith [sq_nonneg (Real.sqrt P - t * Real.sqrt C)]

/-- Actual finite-domain entropic transfer at admissible large scales. The
lower parameter q=pc-n^-2 is constructed inside [0,1], not postulated. -/
theorem finiteHalfSpace_entropic_transfer {d : ℕ} (i : Fin d)
    {E A S : ℝ} (hE : 0 < E) (_hA : 0 < A) (_hS : 0 < S)
    (entropic : FiniteHalfSpaceEntropicInput i E)
    (lower : HalfSpaceLowerTransferPrerequisites i A S)
    (p : unitInterval) (k n R : ℕ) (hn : 1 ≤ n) (hk : 2 * k ≤ n) (hR : k ≤ R)
    (hp : (criticalPoint d : ℝ) < (p : ℝ))
    (hwindow : (p : ℝ) ≤ (criticalPoint d : ℝ) + ((n : ℝ) ^ 2)⁻¹)
    (hscale0 : ((n : ℝ) ^ 2)⁻¹ ≤ (criticalPoint d : ℝ) / 2)
    (hscale1 : ((n : ℝ) ^ 2)⁻¹ ≤ (1 - (criticalPoint d : ℝ)) / 2) :
    finiteHalfSpaceArmProbability i p k n R ≤
      (2 * A + 4 * E ^ 2 * S) * ((k + 1 : ℝ) / (n : ℝ) ^ 3) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let δ : ℝ := ((n : ℝ) ^ 2)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (sq_pos_of_pos hnpos)
  let q : unitInterval := ⟨(criticalPoint d : ℝ) - δ, by
    constructor
    · dsimp [δ]; linarith [(criticalPoint d).property.1]
    · linarith [(criticalPoint d).property.2]⟩
  have hqlo : (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) := by dsimp [q, δ]; linarith
  have hqc : (q : ℝ) < (criticalPoint d : ℝ) := by dsimp [q]; linarith
  have hqp : (q : ℝ) < (p : ℝ) := hqc.trans hp
  have hpu : (p : ℝ) ≤ ((criticalPoint d : ℝ) + 1) / 2 := by linarith
  obtain ⟨hqa, hqcsize⟩ := lower q k n R hn hk hR hqlo hqc
  have hgap : (criticalPoint d : ℝ) - (q : ℝ) = δ := by dsimp [q]; ring
  have hroot : Real.sqrt δ = (n : ℝ)⁻¹ := by
    dsimp [δ]
    rw [Real.sqrt_inv, Real.sqrt_sq (Nat.cast_nonneg n)]
  have hcluster : finiteHalfSpaceClusterSum i q k R ≤ S * (k + 1 : ℝ) * (n : ℝ) := by
    simpa only [hgap, hroot, div_inv_eq_mul] using hqcsize
  have hmono : finiteHalfSpaceArmProbability i q k n R ≤ finiteHalfSpaceArmProbability i p k n R := by
    exact percolation_increasing_event_real_mono
      (measurableSet_connectionToSetEvent _ _ _) (connectionToSetEvent_increasing _ _ _)
      (show q ≤ p from hqp.le)
  have hent := entropic p q k n R hn hk hR hqlo hqp hpu
  rw [max_eq_left hmono] at hent
  have hP : 0 ≤ finiteHalfSpaceArmProbability i p k n R := measureReal_nonneg
  have hC := finiteHalfSpaceClusterSum_nonneg i q k R
  have hineq : finiteHalfSpaceArmProbability i p k n R ≤
      A * ((k + 1 : ℝ) / (n : ℝ) ^ 3) +
      (E * ((p : ℝ) - (q : ℝ))) * Real.sqrt
        (finiteHalfSpaceArmProbability i p k n R * finiteHalfSpaceClusterSum i q k R) := by
    linarith
  have habs := entropic_quadratic_absorption hP hC hineq
  have ht0 : 0 ≤ E * ((p : ℝ) - (q : ℝ)) := mul_nonneg hE.le (sub_nonneg.mpr hqp.le)
  have ht : E * ((p : ℝ) - (q : ℝ)) ≤ E * (2 * δ) := by
    apply mul_le_mul_of_nonneg_left _ hE.le
    dsimp [q, δ]
    linarith
  have ht2 := pow_le_pow_left₀ ht0 ht 2
  calc
    _ ≤ 2 * (A * ((k + 1 : ℝ) / (n : ℝ) ^ 3)) +
        (E * ((p : ℝ) - (q : ℝ))) ^ 2 * finiteHalfSpaceClusterSum i q k R := habs
    _ ≤ 2 * (A * ((k + 1 : ℝ) / (n : ℝ) ^ 3)) +
        (E * (2 * δ)) ^ 2 * (S * (k + 1 : ℝ) * (n : ℝ)) :=
      add_le_add le_rfl (mul_le_mul ht2 hcluster hC (sq_nonneg _))
    _ = _ := by
      dsimp [δ]
      field_simp [hnpos.ne']
      ring

/-- The finite-box argument passes to the full half-space by a proved event
exhaustion; no infinite-domain entropic inequality is assumed. -/
theorem halfSpace_entropic_transfer_large_scales {d : ℕ} (i : Fin d)
    {E A S : ℝ} (hE : 0 < E) (hA : 0 < A) (hS : 0 < S)
    (entropic : FiniteHalfSpaceEntropicInput i E)
    (lower : HalfSpaceLowerTransferPrerequisites i A S)
    (p : unitInterval) (k n : ℕ) (hn : 1 ≤ n) (hk : 2 * k ≤ n)
    (hp : (criticalPoint d : ℝ) < (p : ℝ))
    (hwindow : (p : ℝ) ≤ (criticalPoint d : ℝ) + ((n : ℝ) ^ 2)⁻¹)
    (hscale0 : ((n : ℝ) ^ 2)⁻¹ ≤ (criticalPoint d : ℝ) / 2)
    (hscale1 : ((n : ℝ) ^ 2)⁻¹ ≤ (1 - (criticalPoint d : ℝ)) / 2) :
    (percolation d p).real (halfSpaceArmEvent i k n) ≤
      (2 * A + 4 * E ^ 2 * S) * ((k + 1 : ℝ) / (n : ℝ) ^ 3) := by
  apply connectionToSet_probability_le_of_finiteDomain p
    (halfSpaceArmDomain i) (halfSpaceArmTarget i n) (halfSpaceArmBase i k)
  intro R
  have hb := finiteHalfSpace_entropic_transfer i hE hA hS entropic lower p k n (max R k)
    hn hk (le_max_right _ _) hp hwindow hscale0 hscale1
  exact (measureReal_mono (finiteDomain_connection_mono
    (halfSpaceArmDomain i) (halfSpaceArmTarget i n) (halfSpaceArmBase i k) (le_max_left R k))).trans hb

/-- The source lower-parameter choice is admissible above a finite cutoff
when the classical nontrivial critical-point input 0<pc<1 is supplied. -/
lemma exists_entropic_scale_cutoff {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ n : ℕ, L ≤ n →
      ((n : ℝ) ^ 2)⁻¹ ≤ c / 2 ∧ ((n : ℝ) ^ 2)⁻¹ ≤ (1 - c) / 2 := by
  let ρ : ℝ := min (c / 2) ((1 - c) / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by linarith)
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 ρ⁻¹)
  have hL1 : 1 ≤ L := by
    have hh : (1 : ℝ) ≤ L := (lt_of_le_of_lt (le_max_left _ _) hL).le
    exact_mod_cast hh
  refine ⟨L, hL1, ?_⟩
  intro n hLn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans hL1 hLn)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hInv : ρ⁻¹ ≤ (n : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hL).le.trans (Nat.cast_le.mpr hLn)
  have hprod : 1 ≤ ρ * (n : ℝ) := (inv_le_iff_one_le_mul₀' hρ).mp hInv
  have hsquare : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hprodSq : 1 ≤ (n : ℝ) ^ 2 * ρ := by
    nlinarith [mul_le_mul_of_nonneg_left hsquare hρ.le]
  have hδ : ((n : ℝ) ^ 2)⁻¹ ≤ ρ :=
    (inv_le_iff_one_le_mul₀' (sq_pos_of_pos hnpos)).mpr hprodSq
  exact ⟨hδ.trans (min_le_left _ _), hδ.trans (min_le_right _ _)⟩

/-- NEW Step3, all scales: admissible large scales use the proved entropic
transfer, while finitely many small scales use actual probability <=1.
The unresolved NEW subcritical/interior prerequisites remain explicit. -/
theorem halfSpace_entropic_transfer_all_scales {d : ℕ} (i : Fin d)
    {E A S : ℝ} (hE : 0 < E) (hA : 0 < A) (hS : 0 < S)
    (entropic : FiniteHalfSpaceEntropicInput i E)
    (lower : HalfSpaceLowerTransferPrerequisites i A S)
    (hpc0 : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval) (k n : ℕ), 1 ≤ n → 2 * k ≤ n →
      (criticalPoint d : ℝ) < (p : ℝ) →
      (p : ℝ) ≤ (criticalPoint d : ℝ) + ((n : ℝ) ^ 2)⁻¹ →
      (percolation d p).real (halfSpaceArmEvent i k n) ≤
        C * ((k + 1 : ℝ) / (n : ℝ) ^ 3) := by
  obtain ⟨L, hL, hcut⟩ := exists_entropic_scale_cutoff hpc0 hpc1
  let Q := 2 * A + 4 * E ^ 2 * S
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨max Q ((L : ℝ) ^ 3), hQ.trans_le (le_max_left _ _), ?_⟩
  intro p k n hn hk hp hw
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hweight : 0 ≤ (k + 1 : ℝ) / (n : ℝ) ^ 3 := by positivity
  by_cases hLn : L ≤ n
  · obtain ⟨hscale0, hscale1⟩ := hcut n hLn
    exact (halfSpace_entropic_transfer_large_scales i hE hA hS entropic lower p k n
      hn hk hp hw hscale0 hscale1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hweight)
  · have hnL : (n : ℝ) ≤ L := by exact_mod_cast (le_of_lt (lt_of_not_ge hLn))
    have hpow : (n : ℝ) ^ 3 ≤ (L : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) hnL 3
    have hfac : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ 3 * (k + 1 : ℝ) := by
      have hL3 : 0 ≤ (L : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg L) 3
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [mul_nonneg hL3 hk0]
    have hone : 1 ≤ (L : ℝ) ^ 3 * ((k + 1 : ℝ) / (n : ℝ) ^ 3) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (pow_pos hnpos 3)).mpr
      simpa only [one_mul] using hpow.trans hfac
    exact (measureReal_le_one (μ := percolation d p)).trans (hone.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hweight))

end NearCritical
