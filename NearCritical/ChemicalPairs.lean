module

public import NearCritical.ChemicalConverse
public import NearCritical.ChemicalNorm
public import NearCritical.WaterCube
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! The paper's short-pair estimate (lem.chem.pairs), with the standard uniform
Garet–Marchand lower-tail estimate explicit. Actual open source cubes, finite
pair counting, and the vanishing-probability deduction are proved here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter
open scoped Topology BigOperators

/-- The lattice l1 separation, as a real number. -/
def chemicalL1Separation {d : ℕ} (x y : Vertex d) : ℝ :=
  ∑ j, |(y j : ℝ) - (x j : ℝ)|

lemma chemical_coordinate_le_l1 {d : ℕ} (i : Fin d) (x y : Vertex d) :
    (y i : ℝ) - (x i : ℝ) ≤ chemicalL1Separation x y := by
  exact (le_abs_self _).trans (Finset.single_le_sum
    (fun j _ ↦ abs_nonneg ((y j : ℝ) - (x j : ℝ))) (Finset.mem_univ i))

/-- The source event of an unusually short connected pair, with the normalized
chemical seminorm supplied by the standard shape theorem. -/
def chemicalLowerDeviationEvent {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ))
    (μ ε : ℝ) (x y : Vertex d) : Set (Configuration d) :=
  chemicalShortEvent x y ((1 - ε) * μ * N (fun j ↦ (y j : ℝ) - (x j : ℝ)))

/-- Named standard input extracted from source eq.chem.GM07 (Garet–Marchand
2007) and stationarity. No finite-box or desired pair-event estimate is assumed. -/
def UniformChemicalLowerTail (d : ℕ) (p : unitInterval)
    (N : Seminorm ℝ (Fin d → ℝ)) (μ ε B R : ℝ) : Prop :=
  ∀ x y : Vertex d, R ≤ chemicalL1Separation x y →
    (percolation d p).real (chemicalLowerDeviationEvent N μ ε x y) ≤
      Real.exp (-B * chemicalL1Separation x y)

/-- Exactly the source open cube Lambda_(2L), for integer L, not an issued
support or an enlarged closed cube. -/
def chemicalPairBox (d L : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset (fun _ : Fin d ↦ Finset.Ioo (-(L : ℤ)) (L : ℤ))

lemma chemicalPairBox_subset (d L : ℕ) :
    chemicalPairBox d L ⊆ rectangularBox (fun _ : Fin d ↦ L) := by
  intro x hx
  have hx' : ∀ j : Fin d, -(L : ℤ) < x j ∧ x j < (L : ℤ) := by
    simpa [chemicalPairBox, Fintype.mem_piFinset] using hx
  exact mem_rectangularBox.mpr (fun j ↦ ⟨(hx' j).1.le, (hx' j).2.le⟩)

lemma card_chemicalPairBox_le (d L : ℕ) :
    (chemicalPairBox d L).card ≤ (2 * L + 1) ^ d := by
  calc
    _ ≤ (rectangularBox (fun _ : Fin d ↦ L)).card := Finset.card_le_card (chemicalPairBox_subset d L)
    _ = _ := by simp [card_rectangularBox]

/-- Bad pairs in the source cube, separated by at least L/2 in coordinate i. -/
def chemicalPairEvent {d : ℕ} (i : Fin d) (L : ℕ) (N : Seminorm ℝ (Fin d → ℝ))
    (μ ε : ℝ) : Set (Configuration d) :=
  ⋃ z : (chemicalPairBox d L) × (chemicalPairBox d L),
    {_ω : Configuration d | (L : ℝ) / 2 ≤ (z.2.val i : ℝ) - (z.1.val i : ℝ)} ∩
      chemicalLowerDeviationEvent N μ ε z.1.val z.2.val

lemma measurableSet_chemicalPairEvent {d : ℕ} (i : Fin d) (L : ℕ)
    (N : Seminorm ℝ (Fin d → ℝ)) (μ ε : ℝ) :
    MeasurableSet (chemicalPairEvent i L N μ ε) := by
  apply MeasurableSet.iUnion
  intro z
  exact (MeasurableSet.const _).inter (measurableSet_chemicalShortEvent _ _ _)

/-- The actual finite union bound, with the source directional separation
used to obtain the exponential L/2 rate. -/
theorem chemicalPair_probability_bound {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : Seminorm ℝ (Fin d → ℝ)) {μ ε B R : ℝ} (hB : 0 < B)
    (hGM : UniformChemicalLowerTail d p N μ ε B R) (L : ℕ) (hL : R ≤ (L : ℝ) / 2) :
    (percolation d p).real (chemicalPairEvent i L N μ ε) ≤
      ((2 * (L : ℝ) + 1) ^ d) ^ 2 * Real.exp (-B * (L : ℝ) / 2) := by
  let K := chemicalPairBox d L
  have hterm (z : K × K) : (percolation d p).real
      ({_ω : Configuration d | (L : ℝ) / 2 ≤ (z.2.val i : ℝ) - (z.1.val i : ℝ)} ∩
        chemicalLowerDeviationEvent N μ ε z.1.val z.2.val) ≤
      Real.exp (-B * (L : ℝ) / 2) := by
    by_cases hsep : (L : ℝ) / 2 ≤ (z.2.val i : ℝ) - (z.1.val i : ℝ)
    · have hdist : (L : ℝ) / 2 ≤ chemicalL1Separation z.1.val z.2.val :=
        hsep.trans (chemical_coordinate_le_l1 i _ _)
      calc
        _ ≤ (percolation d p).real (chemicalLowerDeviationEvent N μ ε z.1.val z.2.val) :=
          measureReal_mono inter_subset_right
        _ ≤ Real.exp (-B * chemicalL1Separation z.1.val z.2.val) := hGM _ _ (hL.trans hdist)
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
    · simp [hsep, Real.exp_nonneg]
  have hcard : (Fintype.card (K × K) : ℝ) ≤ ((2 * (L : ℝ) + 1) ^ d) ^ 2 := by
    have hc : (K.card : ℝ) ≤ (2 * (L : ℝ) + 1) ^ d := by
      exact_mod_cast card_chemicalPairBox_le d L
    simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul]
    nlinarith [sq_nonneg ((K.card : ℝ) - (2 * (L : ℝ) + 1) ^ d)]
  calc
    _ ≤ ∑ z : K × K, (percolation d p).real
        ({_ω : Configuration d | (L : ℝ) / 2 ≤ (z.2.val i : ℝ) - (z.1.val i : ℝ)} ∩
          chemicalLowerDeviationEvent N μ ε z.1.val z.2.val) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _z : K × K, Real.exp (-B * (L : ℝ) / 2) := Finset.sum_le_sum fun z _ ↦ hterm z
    _ = (Fintype.card (K × K) : ℝ) * Real.exp (-B * (L : ℝ) / 2) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)

/-- The polynomial pair-count prefactor is dominated by the strict exponential
rate. The proof keeps the exact envelope used by the finite union bound. -/
lemma chemical_pair_envelope_tendsto_zero (d : ℕ) {B : ℝ} (hB : 0 < B) :
    Tendsto (fun L : ℕ ↦ ((2 * (L : ℝ) + 1) ^ d) ^ 2 *
      Real.exp (-B * (L : ℝ) / 2)) atTop (𝓝 0) := by
  let k := B / 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hkn : Tendsto (fun n : ℕ ↦ k * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hk
  have hscaled : Tendsto (fun n : ℕ ↦ (k * (n : ℝ)) ^ (2 * d) *
      Real.exp (-(k * (n : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * d)).comp hkn
  let H := fun n : ℕ ↦ (3 / k) ^ (2 * d) *
    ((k * (n : ℝ)) ^ (2 * d) * Real.exp (-(k * (n : ℝ))))
  have hH : Tendsto H atTop (𝓝 0) := by
    simpa only [H, mul_zero] using hscaled.const_mul ((3 / k) ^ (2 * d))
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_ hH
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : ((2 * (n : ℝ) + 1) ^ d) ^ 2 ≤ (3 * (n : ℝ)) ^ (2 * d) := by
    rw [← pow_mul, Nat.mul_comm d 2]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc
    _ ≤ (3 * (n : ℝ)) ^ (2 * d) * Real.exp (-B * (n : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = H n := by
      have hbase : 3 * (n : ℝ) = (3 / k) * (k * (n : ℝ)) := by
        field_simp
      have hexp : -B * (n : ℝ) / 2 = -(k * (n : ℝ)) := by dsimp [k]; ring
      dsimp [H]
      rw [hbase, mul_pow, hexp]
      ring

/-- Source lem.chem.pairs: the pair-event probability vanishes, deduced from
standard uniform GM lower tails, actual pair counting and the L/2 geometry. -/
theorem chemicalPair_probability_tendsto_zero {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : Seminorm ℝ (Fin d → ℝ)) {μ ε B R : ℝ} (hB : 0 < B)
    (hGM : UniformChemicalLowerTail d p N μ ε B R) :
    Tendsto (fun L : ℕ ↦ (percolation d p).real (chemicalPairEvent i L N μ ε))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
    (chemical_pair_envelope_tendsto_zero d hB)
  have he : ∀ᶠ L : ℕ in atTop, 2 * R ≤ (L : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 * R))
  filter_upwards [he] with L hL
  exact chemicalPair_probability_bound p i N hB hGM L (by linarith)

/-- The cited uniform lower-tail input may provide its own constants B,R;
the pair conclusion has no dependence on their values. -/
theorem chemical_pairs {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : Seminorm ℝ (Fin d → ℝ)) (μ ε : ℝ)
    (hGM : ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail d p N μ ε B R) :
    Tendsto (fun L : ℕ ↦ (percolation d p).real (chemicalPairEvent i L N μ ε))
      atTop (𝓝 0) := by
  obtain ⟨B, hB, R, htail⟩ := hGM
  exact chemicalPair_probability_tendsto_zero p i N hB htail

end NearCritical
