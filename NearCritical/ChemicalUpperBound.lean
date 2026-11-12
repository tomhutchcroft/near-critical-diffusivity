module

public import NearCritical.ChemicalUpperReduction

/-! The new short-crossing/time-constant deduction in prop.chem.upper. The
paper's crossing construction and standard uniform GM lower tails are explicit
inputs; the resulting upper bound is proved on actual events. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter
open scoped Topology

/-- Full-lattice short connection between two points of the source cube with
coordinate separation >=L/2. A source path inside B_L implies this event after
its stated translation into Lambda_(2L); no restricted-path equality is asserted. -/
def chemicalShortCrossingEvent {d : ℕ} (i : Fin d) (L : ℕ) (T : ℝ) :
    Set (Configuration d) :=
  ⋃ z : (chemicalPairBox d L) × (chemicalPairBox d L),
    {_ω : Configuration d | (L : ℝ) / 2 ≤ (z.2.val i : ℝ) - (z.1.val i : ℝ)} ∩
      chemicalShortEvent z.1.val z.2.val (T * (L : ℝ))

/-- Exact interface bridge to the other contributor's accepted span event. -/
@[simp] lemma chemicalShortCrossingEvent_eq_span {d : ℕ} (i : Fin d) (L : ℕ) (T : ℝ) :
    chemicalShortCrossingEvent i L T = chemicalSpanEvent i L T := rfl

lemma measurableSet_chemicalShortCrossingEvent {d : ℕ} (i : Fin d) (L : ℕ) (T : ℝ) :
    MeasurableSet (chemicalShortCrossingEvent i L T) := by
  apply MeasurableSet.iUnion
  intro z
  exact (MeasurableSet.const _).inter (measurableSet_chemicalShortEvent _ _ _)

/-- If the proposed time constant is too large, every short crossing would be
one of the unusually short pairs ruled out by the pair estimate. -/
lemma chemicalShortCrossing_subset_pairs {d : ℕ} (i : Fin d) (L : ℕ)
    (N : Seminorm ℝ (Fin d → ℝ))
    (hunit : ∀ j, N (Pi.single j 1) = 1)
    (hreflect : ∀ j x, N (coordinateReflection j x) = N x)
    {μ ε T : ℝ} (hcoeff : 0 ≤ (1 - ε) * μ) (hslack : 2 * T ≤ (1 - ε) * μ) :
    chemicalShortCrossingEvent i L T ⊆ chemicalPairEvent i L N μ ε := by
  intro ω hω
  obtain ⟨z, hsep, hshort⟩ := mem_iUnion.mp hω
  apply mem_iUnion.mpr
  refine ⟨z, hsep, ?_⟩
  have hnorm : (L : ℝ) / 2 ≤ N (fun j ↦ (z.2.val j : ℝ) - (z.1.val j : ℝ)) :=
    hsep.trans ((le_abs_self _).trans
      ((chemicalNorm_comparison N hunit hreflect _).1 i))
  have hthreshold : T * (L : ℝ) ≤
      (1 - ε) * μ * N (fun j ↦ (z.2.val j : ℝ) - (z.1.val j : ℝ)) := by
    calc
      _ = (2 * T) * ((L : ℝ) / 2) := by ring
      _ ≤ ((1 - ε) * μ) * ((L : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hslack (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hcoeff
  obtain ⟨m, hm, hpath⟩ := hshort
  exact ⟨m, hm.trans hthreshold, hpath⟩

/-- Source prop.chem.upper's new deduction. Scales may be the actual source
L(M)=(M-1)*ell_0+s rather than all integers. The crossing-probability input is
recorded as a dependency, not silently discharged as a constructed path. -/
theorem chemical_timeConstant_upper_probability_reduction {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : Seminorm ℝ (Fin d → ℝ))
    (hunit : ∀ j, N (Pi.single j 1) = 1)
    (hreflect : ∀ j x, N (coordinateReflection j x) = N x)
    {μ T c : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    (scales : ℕ → ℕ) (hscales : Tendsto scales atTop atTop)
    (hcross : ∀ᶠ M : ℕ in atTop,
      c ≤ (percolation d p).real (chemicalShortCrossingEvent i (scales M) T))
    (hGM : ∀ ε : ℝ, ε ∈ Ioo 0 1 →
      ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail d p N μ ε B R) :
    μ ≤ 2 * T := by
  by_contra h
  have hgap : 2 * T < μ := lt_of_not_ge h
  have hμ : 0 < μ := lt_of_le_of_lt (by positivity : 0 ≤ 2 * T) hgap
  let ε := (μ - 2 * T) / (2 * μ)
  have hε : ε ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hgap) (by positivity)
    · apply (div_lt_one (by positivity : 0 < 2 * μ)).mpr
      linarith
  have hcoeffeq : (1 - ε) * μ = (μ + 2 * T) / 2 := by
    dsimp [ε]
    field_simp
    ring
  have hcoeff : 0 ≤ (1 - ε) * μ := by rw [hcoeffeq]; positivity
  have hslack : 2 * T ≤ (1 - ε) * μ := by rw [hcoeffeq]; linarith
  have hlim := (chemical_pairs p i N μ ε (hGM ε hε)).comp hscales
  have he := hlim.eventually (gt_mem_nhds hc)
  obtain ⟨M, hM, hsmall⟩ := (hcross.and he).exists
  have hsub := measureReal_mono (μ := percolation d p)
    (chemicalShortCrossing_subset_pairs i (scales M) N hunit hreflect hcoeff hslack)
  exact (not_le_of_gt hsmall) (hM.trans hsub)

/-- Source correlation scale in the equivalent inverse-square-root convention. -/
def chemicalCorrelationScale (d : ℕ) (p : unitInterval) : ℕ :=
  ⌊(Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)))⁻¹⌋₊

lemma chemicalCorrelationScale_le (d : ℕ) (p : unitInterval) :
    (chemicalCorrelationScale d p : ℝ) ≤
      (Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)))⁻¹ :=
  Nat.floor_le (by positivity)

/-- The quantitative near-critical consequence in prop.chem.upper, retaining
its actual short-crossing construction as an explicit paper dependency. -/
theorem chemical_timeConstant_upper_near_critical {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : Seminorm ℝ (Fin d → ℝ))
    (hunit : ∀ j, N (Pi.single j 1) = 1)
    (hreflect : ∀ j x, N (coordinateReflection j x) = N x)
    {μ C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (scales : ℕ → ℕ) (hscales : Tendsto scales atTop atTop)
    (hcross : ∀ᶠ M : ℕ in atTop,
      c ≤ (percolation d p).real
        (chemicalShortCrossingEvent i (scales M) (C * (chemicalCorrelationScale d p : ℝ))))
    (hGM : ∀ ε : ℝ, ε ∈ Ioo 0 1 →
      ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail d p N μ ε B R) :
    μ ≤ (2 * C) / Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) := by
  have hupper : μ ≤ 2 * (C * (chemicalCorrelationScale d p : ℝ)) := by
    by_cases hμ : 0 ≤ μ
    · exact chemical_timeConstant_upper_of_crossings p i N hunit hreflect hμ
        (mul_nonneg hC (Nat.cast_nonneg _)) hc scales hscales
        (by simpa only [chemicalShortCrossingEvent_eq_span] using hcross)
        (fun ε hεpos hεone ↦ hGM ε ⟨hεpos, hεone⟩)
    · exact (le_of_not_ge hμ).trans (by positivity)
  calc
    μ ≤ 2 * (C * (chemicalCorrelationScale d p : ℝ)) := hupper
    _ ≤ 2 * (C * (Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)))⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (chemicalCorrelationScale_le d p) hC) (by norm_num)
    _ = _ := by rw [div_eq_mul_inv]; ring

end NearCritical
