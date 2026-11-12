module

public import NearCritical.Section7FaceDiameter
public import NearCritical.AppendixBoxSmallScale

/-! Source `prop.lower_water`, `eq.lower_water_general`, for ALL scales.

The source statement `a(Lambda_n, p_c) >~ n^(-6)` has no restriction on `n`,
while its proof (through `lem.spanning.diam`) covers `n >= N_0`. The finitely
many small scales are handled here by positivity: with every issued bond open
(probability `p^{#bonds} > 0`) the cube is one component, so one path current
gives a positive relaxed conductivity. Reuses the accepted all-open
connectivity of `AppendixBoxSmallScale`.

 -/
@[expose] public section
noncomputable section
namespace NearCritical.Section7
open MeasureTheory
open scoped Classical

/-- The relaxed annealed conductivity of every odd cube is strictly positive
at every positive parameter. -/
theorem annealedRelaxed_pos {d : ℕ} (r : ℕ) (i : Fin d) (p : unitInterval)
    (hp : 0 < (p:ℝ)) : 0 < annealedRelaxed (centeredBox d r) i (p:ℝ) := by
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : IssuedBond (centeredBox d r) → Bool, η₁ = fun _ => true :=
    ⟨_, rfl⟩
  have hη₁e : ∀ e, η₁ e = true := by
    intro e
    rw [hη₁]
  -- the cube-restricted graph of the all-open cube assignment
  have hG : restrictedGraph (cubeConfig η₁) (centeredBox d r : Set (Vertex d)) =
      restrictedGraph (fun _ => true) (centeredBox d r : Set (Vertex d)) := by
    apply restrictedGraph_eq_of_internalBondSet_agree (centeredBox d r)
      (centeredBox d r : Set (Vertex d)) (fun x hx => hx)
    intro b hb
    obtain ⟨hb1, _⟩ := (mem_internalBondSet (centeredBox d r) b).mp hb
    have hbI : b ∈ issuedBondSet (centeredBox d r) :=
      Finset.mem_product.mpr ⟨hb1, Finset.mem_univ _⟩
    have h := cubeConfig_apply η₁ ⟨b, hbI⟩
    rw [hη₁e] at h
    exact h
  -- bottom and top points on the axis `i`
  obtain ⟨x, hxdef⟩ : ∃ x : Vertex d, x = Function.update (0 : Vertex d) i (-(r:ℤ)) := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : Vertex d, y = Function.update (0 : Vertex d) i (r:ℤ) := ⟨_, rfl⟩
  have hxi : x i = -(r:ℤ) := by
    rw [hxdef]
    exact Function.update_self i _ _
  have hyi : y i = (r:ℤ) := by
    rw [hydef]
    exact Function.update_self i _ _
  have hxU : x ∈ centeredBox d r := by
    apply mem_centeredBox.mpr
    intro j
    by_cases hj : j = i
    · subst j
      rw [hxi]
      omega
    · rw [hxdef]
      simp only [Function.update_of_ne hj, Pi.zero_apply]
      omega
  have hyU : y ∈ centeredBox d r := by
    apply mem_centeredBox.mpr
    intro j
    by_cases hj : j = i
    · subst j
      rw [hyi]
      omega
    · rw [hydef]
      simp only [Function.update_of_ne hj, Pi.zero_apply]
      omega
  have hreach : (restrictedGraph (cubeConfig η₁)
      (centeredBox d r : Set (Vertex d))).Reachable x y := by
    rw [hG]
    exact centeredBox_allOpen_reachable hxU hyU
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ((restrictedGraph (cubeConfig η₁)
      (centeredBox d r : Set (Vertex d))).dist x y : ℝ) := ⟨_, rfl⟩
  have hD : 0 ≤ D := by
    rw [hDdef]
    exact Nat.cast_nonneg _
  have hC : finiteBoxCluster (cubeConfig η₁) (centeredBox d r) x ∈
      crossingFamily (cubeConfig η₁) r i D := by
    refine (mem_crossingFamily _ r i D _).mpr
      ⟨(mem_finiteClusterFamily _ _ _).mpr ⟨x, hxU, rfl⟩, x,
        root_mem_finiteBoxCluster _ _ hxU, y,
        (mem_finiteBoxCluster _ _ x y).mpr ⟨hyU, hreach⟩, hxi, hyi, ?_⟩
    exact le_of_eq hDdef.symm
  -- its exit bond is open
  obtain ⟨e, hedef⟩ : ∃ e : IssuedBond (centeredBox d r), e =
      ⟨(exitPoint (cubeConfig η₁) r i D
          (finiteBoxCluster (cubeConfig η₁) (centeredBox d r) x), i),
        Finset.mem_product.mpr ⟨(exitPoint_spec hC).2.2, Finset.mem_univ _⟩⟩ := ⟨_, rfl⟩
  have heJ : e ∈ exitBonds r i D η₁ := by
    refine (mem_exitBonds r i D η₁ e).mpr ⟨_, hC, ?_⟩
    rw [hedef]
  have hopen : (1:ℝ) ≤ (((exitBonds r i D η₁).filter (fun e => η₁ e = true)).card : ℝ) := by
    have hpos : 0 < ((exitBonds r i D η₁).filter (fun e => η₁ e = true)).card :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heJ, hη₁e e⟩⟩
    exact_mod_cast hpos
  obtain ⟨θ, hsupp, hunit, _⟩ := exists_flow_of_open_exits r i hD η₁ one_pos hopen
  obtain ⟨hE, hb⟩ := local_relaxed_flow_lower i η₁ θ hsupp hunit
  have hcard : (0:ℝ) < ((centeredBox d r).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (centeredBox_nonempty d r))
  have hn : (0:ℝ) < (2*(r:ℝ)+1)^2 := by positivity
  have hloc : 0 < localRelaxedConductivity (centeredBox d r) i η₁ :=
    lt_of_lt_of_le (div_pos (div_pos hn hE) hcard) hb
  have hw : 0 < Section10.cubeBernoulliWeight p η₁ := by
    unfold Section10.cubeBernoulliWeight
    apply Finset.prod_pos
    intro b _
    rw [if_pos (hη₁e b)]
    exact hp
  rw [← annealedRelaxed_eq_weighted_sum]
  exact lt_of_lt_of_le (mul_pos hw hloc)
    (Finset.single_le_sum
      (f := fun η => Section10.cubeBernoulliWeight p η *
        localRelaxedConductivity (centeredBox d r) i η)
      (fun η _ => mul_nonneg (cubeBernoulliWeight_nonneg' p η)
        (localRelaxedConductivity_nonneg' _ i η)) (Finset.mem_univ η₁))

/-- Extending a large-scale `n^(-6)` bound to all scales by positivity. -/
theorem all_scales_of_large_scales {a : ℕ → ℝ} (ha : ∀ r, 0 < a r) :
    ∀ N0 : ℕ, (∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, N0 ≤ r → c / (2*(r:ℝ)+1)^6 ≤ a r) →
      ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, c / (2*(r:ℝ)+1)^6 ≤ a r := by
  intro N0
  induction N0 with
  | zero =>
    rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun r => h r (Nat.zero_le r)⟩
  | succ N ih =>
    rintro ⟨c, hc, h⟩
    apply ih
    have hN6 : (0:ℝ) < (2*(N:ℝ)+1)^6 := by positivity
    refine ⟨min c (a N * (2*(N:ℝ)+1)^6), lt_min hc (mul_pos (ha N) hN6), ?_⟩
    intro r hr
    have hr6 : (0:ℝ) < (2*(r:ℝ)+1)^6 := by positivity
    rcases Nat.eq_or_lt_of_le hr with hrN | hrN
    · subst hrN
      rw [div_le_iff₀ hN6]
      exact min_le_right _ _
    · exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hr6.le) (h r hrN)

/-- **Source `prop.lower_water`, `eq.lower_water_general`, at every scale**:
`c n^(-6) <= a(Lambda_n, p_c)` for all odd `n = 2r+1`, from `lem.spanning.diam`
and `0 < p_c`. -/
theorem lower_water_general_all {d : ℕ} (hd : 6 ≤ d) (i : Fin d)
    (hpc : 0 < (criticalPoint d : ℝ)) (hS : SpanningDiamStatement d) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
      c / (2*(r:ℝ)+1)^6 ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := by
  obtain ⟨c, hc, N0, h⟩ := lower_water_general hd i hpc hS
  exact all_scales_of_large_scales
    (a := fun r => annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ))
    (fun r => annealedRelaxed_pos r i (criticalPoint d) hpc) N0 ⟨c, hc, h⟩

/-- **Source `prop.lower_water`, `eq.lower_water`, for every `p > p_c`**: for
every odd cube of side `n = 2r+1 <= l_*(p)`, `c (p-p_c)^3 <= a(Lambda_n, p)`,
with no lower restriction on the scale. -/
theorem lower_water_all {d : ℕ} (hd : 6 ≤ d) (i : Fin d)
    (hpc : 0 < (criticalPoint d : ℝ)) (hS : SpanningDiamStatement d) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : unitInterval, criticalPoint d < p →
      ∀ r : ℕ, 2*r+1 ≤ chemicalCorrelationScale d p →
        c * ((p:ℝ) - (criticalPoint d : ℝ))^3 ≤
          annealedRelaxed (centeredBox d r) i (p:ℝ) := by
  obtain ⟨c, hc, hgen⟩ := lower_water_general_all hd i hpc hS
  refine ⟨c, hc, ?_⟩
  intro p hp r hscale
  have hNpos : (0:ℝ) < 2*(r:ℝ)+1 := by positivity
  have hle : (2*(r:ℝ)+1) ≤ (chemicalCorrelationScale d p : ℝ) := by exact_mod_cast hscale
  have h6 : (2*(r:ℝ)+1)^6 ≤ (chemicalCorrelationScale d p : ℝ)^6 :=
    pow_le_pow_left₀ hNpos.le hle 6
  have hinv := Section10.chemicalCorrelationScale_inverse_six_lower p hp
  have hinv2 : 1/(chemicalCorrelationScale d p : ℝ)^6 ≤ 1/(2*(r:ℝ)+1)^6 :=
    one_div_le_one_div_of_le (pow_pos hNpos 6) h6
  calc c * ((p:ℝ) - (criticalPoint d : ℝ))^3
      ≤ c * (1/(2*(r:ℝ)+1)^6) := mul_le_mul_of_nonneg_left (hinv.trans hinv2) hc.le
    _ = c / (2*(r:ℝ)+1)^6 := mul_one_div _ _
    _ ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := hgen r
    _ ≤ annealedRelaxed (centeredBox d r) i (p:ℝ) :=
        annealedRelaxed_parameter_mono _ i hp.le

/-- **Source `prop.lower_water`, `eq.lower_water_general`, at every scale**, from
assumption (A), `d >= 9`, the literal `eq.arm.2dspanning`, the small-volume
input and the face-reach tail. -/
theorem lower_water_general_all_of_literal_inputs {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) (harm : Arm2dSpanningStatement d)
    (hvol : SpanningSmallVolumeInput d) (htail : FaceReachTail d) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
      c / (2*(r:ℝ)+1)^6 ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := by
  have hpc := criticalPoint_pos_of_twoPointAsymptotics i hA
  obtain ⟨c, hc, N0, h⟩ := lower_water_general_of_literal_inputs hd i hA harm hvol htail
  exact all_scales_of_large_scales
    (a := fun r => annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ))
    (fun r => annealedRelaxed_pos r i (criticalPoint d) hpc) N0 ⟨c, hc, h⟩

end NearCritical.Section7
