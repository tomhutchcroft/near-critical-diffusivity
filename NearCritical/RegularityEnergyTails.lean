module

public import NearCritical.PreGoodRegularBoundary

/-! The Chebyshev step of NEW prop.choice_c, on actual finite-heart energies.
The diagram estimates for their conditional means/variances remain NEW inputs. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

/-- Every real observable of the FULL finite heart-cluster union is integrable. -/
lemma integrable_heartUnion_observable {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (f : Finset (Vertex d) → ℝ) :
    Integrable (fun ω : Configuration d => f (heartClusterUnion ω Q heart)) (percolation d p) := by
  have h := percolation_cylinder_integrable d p (internalBondSet Q)
    (fun η => f (heartClusterUnion (reconstructInterior Q η) Q heart))
  apply h.congr
  filter_upwards [] with ω
  exact (congrArg f (heartClusterUnion_eq_of_internal_agree Q Q heart (fun _ hx => hx)
    ω _ (reconstructInterior_restrict_agree Q ω))).symm

/-- Computed mean conditioned on the actual point belonging to fC. The value
on a null membership event is defined by real division; no positivity is assumed. -/
def heartConditionalMean {d : ℕ} (p : unitInterval) (Q heart : Finset (Vertex d))
    (f : Finset (Vertex d) → ℝ) (x : Vertex d) : ℝ :=
  (∫ ω : Configuration d, if x ∈ heartClusterUnion ω Q heart
    then f (heartClusterUnion ω Q heart) else 0 ∂percolation d p) /
      (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart}

/-- Actual UNNORMALIZED conditional centered second moment. For positive
membership mass it is that mass times the conditional variance. -/
def heartCenteredMoment {d : ℕ} (p : unitInterval) (Q heart : Finset (Vertex d))
    (f : Finset (Vertex d) → ℝ) (x : Vertex d) : ℝ :=
  ∫ ω : Configuration d, if x ∈ heartClusterUnion ω Q heart
    then (f (heartClusterUnion ω Q heart) - heartConditionalMean p Q heart f x)^2 else 0
    ∂percolation d p

/-- Weighted Chebyshev at delta/2, derived without dividing by membership
probability. This remains valid for null membership fibers. -/
theorem heart_energy_upper_tail {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (f : Finset (Vertex d) → ℝ) (x : Vertex d)
    {δ : ℝ} (hδ : 0 < δ) (hm : heartConditionalMean p Q heart f x ≤ δ/2) :
    (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart ∧
      δ < f (heartClusterUnion ω Q heart)} ≤ 4*heartCenteredMoment p Q heart f x/δ^2 := by
  let m := heartConditionalMean p Q heart f x
  let g := fun ω : Configuration d => if x ∈ heartClusterUnion ω Q heart
    then (f (heartClusterUnion ω Q heart)-m)^2 else (0:ℝ)
  have hi : Integrable g (percolation d p) :=
    integrable_heartUnion_observable p Q heart (fun F => if x ∈ F then (f F-m)^2 else 0)
  have hn : 0 ≤ᵐ[percolation d p] g := by
    apply Filter.Eventually.of_forall
    intro ω
    dsimp [g]
    split_ifs <;> positivity
  have hs : {ω : Configuration d | x ∈ heartClusterUnion ω Q heart ∧
      δ < f (heartClusterUnion ω Q heart)} ⊆ {ω | (δ/2)^2 ≤ g ω} := by
    intro ω hω
    dsimp [g]
    rw [ite_eq_left hω.1]
    have hd : δ/2 < f (heartClusterUnion ω Q heart)-m := by dsimp [m]; linarith [hω.2]
    have hprod := mul_nonneg
      (show 0 ≤ f (heartClusterUnion ω Q heart)-m-δ/2 by linarith)
      (show 0 ≤ f (heartClusterUnion ω Q heart)-m+δ/2 by linarith)
    nlinarith
  have ht : 0 < (δ/2)^2 := by positivity
  have hmark := mul_meas_ge_le_integral_of_nonneg hn hi ((δ/2)^2)
  have hbound : (percolation d p).real {ω | (δ/2)^2 ≤ g ω} ≤
      heartCenteredMoment p Q heart f x/((δ/2)^2) := by
    apply (le_div_iff₀ ht).mpr
    simpa only [heartCenteredMoment,g,m,mul_comm] using hmark
  calc
    _ ≤ heartCenteredMoment p Q heart f x/((δ/2)^2) := (measureReal_mono hs).trans hbound
    _ = _ := by field_simp [ne_of_gt hδ]; ring

/-- Literal irregular-point probability from the TWO actual ERE moments.
Full cubeBoundary controls ERE2; markBoundary only controls the counted points.
The half-delta mean hypotheses are NEW analytic estimates, not tail premises. -/
theorem irregularBoundary_probability_le_moments {d : ℕ} (p : unitInterval)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d))
    (hmark : markBoundary ⊆ cubeBoundary) (r : ℕ) (x : Vertex d) {δ : ℝ} (hδ : 0 < δ)
    (hm1 : heartConditionalMean p Q heart (fun F => regularityEnergyOne F excluded r x) x ≤ δ/2)
    (hm2 : heartConditionalMean p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤ δ/2) :
    (percolation d p).real {ω | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ} ≤
      4*(heartCenteredMoment p Q heart (fun F => regularityEnergyOne F excluded r x) x +
        heartCenteredMoment p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x)/δ^2 := by
  have hs : {ω : Configuration d | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ} ⊆
      {ω | x ∈ heartClusterUnion ω Q heart ∧ δ < regularityEnergyOne (heartClusterUnion ω Q heart) excluded r x} ∪
      {ω | x ∈ heartClusterUnion ω Q heart ∧ δ < regularityEnergyTwo (heartClusterUnion ω Q heart) cubeBoundary r x} := by
    intro ω hω
    obtain ⟨hx,hbad⟩ := Finset.mem_filter.mp hω
    obtain ⟨hxF,hxm⟩ := Finset.mem_inter.mp hx
    by_cases h1 : regularityEnergyOne (heartClusterUnion ω Q heart) excluded r x ≤ δ
    · right
      refine ⟨hxF,lt_of_not_ge ?_⟩
      intro h2
      exact hbad ⟨Finset.mem_inter.mpr ⟨hxF,hmark hxm⟩,h1,h2⟩
    · exact Or.inl ⟨hxF,lt_of_not_ge h1⟩
  have h1 := heart_energy_upper_tail p Q heart (fun F => regularityEnergyOne F excluded r x) x hδ hm1
  have h2 := heart_energy_upper_tail p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x hδ hm2
  have h := (measureReal_mono (μ := percolation d p) hs).trans (measureReal_union_le _ _)
  calc
    _ ≤ 4*heartCenteredMoment p Q heart (fun F => regularityEnergyOne F excluded r x) x/δ^2 +
        4*heartCenteredMoment p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x/δ^2 :=
      h.trans (add_le_add h1 h2)
    _ = _ := by ring

/-- Exact expectation of the LITERAL irregular-point count, with membership
measurability already derived from actual internal-coordinate support. -/
theorem integral_irregularBoundary_count {d : ℕ} (p : unitInterval)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ) :
    (∫ ω : Configuration d,
      ((irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ).card:ℝ)
      ∂percolation d p) =
      ∑ x ∈ Q, (percolation d p).real
        {ω | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ} := by
  let B := fun ω => irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ
  have hBU := fun ω => irregularBoundaryVertices_subset ω Q heart excluded cubeBoundary markBoundary r δ
  have hm := fun x (_hx : x ∈ Q) =>
    measurableSet_irregularBoundary_member Q heart excluded cubeBoundary markBoundary r δ x
  calc
    _ = ∫ ω, markedVertexCount Q B ω ∂percolation d p := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (markedVertexCount_eq_card Q B hBU ω).symm
    _ = _ := integral_markedVertexCount p Q B hm

/-- The source marked first moment is DERIVED by summing the actual TWO-ERE
tail bounds. Mean assumptions are needed only on the truncated counting set. -/
theorem irregularBoundary_first_moment_le_moments {d : ℕ} (p : unitInterval)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d))
    (hmarkQ : markBoundary ⊆ Q) (hmark : markBoundary ⊆ cubeBoundary)
    (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hm1 : ∀ x ∈ markBoundary,
      heartConditionalMean p Q heart (fun F => regularityEnergyOne F excluded r x) x ≤ δ/2)
    (hm2 : ∀ x ∈ markBoundary,
      heartConditionalMean p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤ δ/2) :
    (∫ ω : Configuration d,
      ((irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ).card:ℝ)
      ∂percolation d p) ≤
      (4/δ^2)*∑ x ∈ markBoundary,
        (heartCenteredMoment p Q heart (fun F => regularityEnergyOne F excluded r x) x +
         heartCenteredMoment p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x) := by
  have hzero (x : Vertex d) (hx : x ∉ markBoundary) :
      (percolation d p).real
        {ω | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ} = 0 := by
    simp [irregularBoundaryVertices,hx]
  have he : (∑ x ∈ markBoundary, (percolation d p).real
        {ω | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ}) =
      ∑ x ∈ Q, (percolation d p).real
        {ω | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ} := by
    exact Finset.sum_subset hmarkQ (fun x _hx hxm => hzero x hxm)
  rw [integral_irregularBoundary_count,← he]
  calc
    _ ≤ ∑ x ∈ markBoundary,
        4*(heartCenteredMoment p Q heart (fun F => regularityEnergyOne F excluded r x) x +
           heartCenteredMoment p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x)/δ^2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact irregularBoundary_probability_le_moments p Q heart excluded cubeBoundary markBoundary
        hmark r x hδ (hm1 x hx) (hm2 x hx)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring

/-- Computed conditional variance and membership estimates imply the source
finite first-moment bound. No marked-count/tail bound is an input.
The moment inequalities below are still NEW diagram obligations. -/
theorem irregularBoundary_first_moment_le_variance_membership {d : ℕ} (p : unitInterval)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d))
    (hmarkQ : markBoundary ⊆ Q) (hmark : markBoundary ⊆ cubeBoundary)
    (r : ℕ) {δ V C : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V)
    (hm1 : ∀ x ∈ markBoundary,
      heartConditionalMean p Q heart (fun F => regularityEnergyOne F excluded r x) x ≤ δ/2)
    (hm2 : ∀ x ∈ markBoundary,
      heartConditionalMean p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤ δ/2)
    (hvar : ∀ x ∈ markBoundary,
      heartCenteredMoment p Q heart (fun F => regularityEnergyOne F excluded r x) x +
        heartCenteredMoment p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤
      V*(percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart})
    (hhit : ∀ x ∈ markBoundary,
      (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} ≤ C) :
    (∫ ω : Configuration d,
      ((irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ).card:ℝ)
      ∂percolation d p) ≤ (4/δ^2)*V*C*(markBoundary.card:ℝ) := by
  have hsum : (∑ x ∈ markBoundary,
      (heartCenteredMoment p Q heart (fun F => regularityEnergyOne F excluded r x) x +
       heartCenteredMoment p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x)) ≤
      (V*C)*(markBoundary.card:ℝ) := by
    calc
      _ ≤ ∑ _x ∈ markBoundary, V*C := Finset.sum_le_sum
        (fun x hx => (hvar x hx).trans (mul_le_mul_of_nonneg_left (hhit x hx) hV))
      _ = _ := by simp [mul_comm]
  have hfactor : 0 ≤ 4/δ^2 := by positivity
  have h := (irregularBoundary_first_moment_le_moments p Q heart excluded cubeBoundary
    markBoundary hmarkQ hmark r hδ hm1 hm2).trans (mul_le_mul_of_nonneg_left hsum hfactor)
  convert h using 1; ring

/-- Source prop.choice_c scaling: variance decay r^{6-d}, membership n^{-3}
and truncated-face cardinality n^{d-1} give the actual n^{d-4} first moment.
All moment/membership bounds remain NEW analytic inputs at this scale. -/
theorem irregularBoundary_first_moment_source_scale {d : ℕ} (p : unitInterval)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d))
    (hmarkQ : markBoundary ⊆ Q) (hmark : markBoundary ⊆ cubeBoundary)
    (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) (hd : 7 ≤ d)
    {δ Cv Cp Cb : ℝ} (hδ : 0 < δ) (hCv : 0 ≤ Cv) (hCp : 0 ≤ Cp)
    (hm1 : ∀ x ∈ markBoundary,
      heartConditionalMean p Q heart (fun F => regularityEnergyOne F excluded r x) x ≤ δ/2)
    (hm2 : ∀ x ∈ markBoundary,
      heartConditionalMean p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤ δ/2)
    (hvar : ∀ x ∈ markBoundary,
      heartCenteredMoment p Q heart (fun F => regularityEnergyOne F excluded r x) x +
        heartCenteredMoment p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤
      (Cv/(r:ℝ)^(d-6))*(percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart})
    (hhit : ∀ x ∈ markBoundary,
      (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} ≤ Cp/(n:ℝ)^3)
    (hcard : (markBoundary.card:ℝ) ≤ Cb*(n:ℝ)^(d-1)) :
    (∫ ω : Configuration d,
      ((irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ).card:ℝ)
      ∂percolation d p) ≤ (4*Cv*Cp*Cb/δ^2)/(r:ℝ)^(d-6)*(n:ℝ)^(d-4) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hV : 0 ≤ Cv/(r:ℝ)^(d-6) := by positivity
  have hcoef : 0 ≤ (4/δ^2)*(Cv/(r:ℝ)^(d-6))*(Cp/(n:ℝ)^3) := by positivity
  have h := irregularBoundary_first_moment_le_variance_membership p Q heart excluded
    cubeBoundary markBoundary hmarkQ hmark r hδ hV hm1 hm2 hvar hhit
  have hp : (n:ℝ)^(d-1) = (n:ℝ)^(d-4)*(n:ℝ)^3 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ (4/δ^2)*(Cv/(r:ℝ)^(d-6))*(Cp/(n:ℝ)^3)*(Cb*(n:ℝ)^(d-1)) :=
      h.trans (mul_le_mul_of_nonneg_left hcard hcoef)
    _ = _ := by
      rw [hp]
      field_simp [ne_of_gt hnR,ne_of_gt hrR,ne_of_gt hδ] <;> ring

end NearCritical
