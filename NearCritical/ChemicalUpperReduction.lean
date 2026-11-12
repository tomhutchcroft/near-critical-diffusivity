module

public import NearCritical.ChemicalPairs

/-! The new crossing/bad-pair deduction in source prop.chem.upper.
The paper's crossing construction remains an explicit unresolved dependency. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter
open scoped Topology

/-- A short connection between two points of the actual source open cube with
coordinate separation at least L/2. A source box crossing implies this event
once its endpoints and length have been embedded; no embedding is presumed. -/
def chemicalSpanEvent {d : ℕ} (i : Fin d) (L : ℕ) (K : ℝ) : Set (Configuration d) :=
  ⋃ z : (chemicalPairBox d L) × (chemicalPairBox d L),
    {_ω : Configuration d | (L:ℝ)/2 ≤ (z.2.val i:ℝ)-(z.1.val i:ℝ)} ∩
      chemicalShortEvent z.1.val z.2.val (K*(L:ℝ))

lemma measurableSet_chemicalSpanEvent {d : ℕ} (i : Fin d) (L : ℕ) (K : ℝ) :
    MeasurableSet (chemicalSpanEvent i L K) := by
  apply MeasurableSet.iUnion
  intro z
  exact (MeasurableSet.const _).inter (measurableSet_chemicalShortEvent _ _ _)

/-- An actual open walk supplies the span event once its endpoints, separation,
and length have been checked. Domain confinement may be stronger than needed. -/
lemma chemicalSpanEvent_of_walk {d : ℕ} {ω : Configuration d} (i : Fin d) (L : ℕ)
    {K : ℝ} {x y : Vertex d} (hx : x ∈ chemicalPairBox d L)
    (hy : y ∈ chemicalPairBox d L) (hsep : (L:ℝ)/2 ≤ (y i:ℝ)-(x i:ℝ))
    (w : (openGraph ω).Walk x y) (hlen : (w.length:ℝ) ≤ K*(L:ℝ)) :
    ω ∈ chemicalSpanEvent i L K := by
  apply Set.mem_iUnion.mpr
  refine ⟨(⟨x,hx⟩,⟨y,hy⟩),hsep,w.length,hlen,w.length,le_rfl,?_⟩
  exact (graphNStep_iff_exists_walk (openGraph ω) w.length x y).2 ⟨w,rfl⟩

/-- If the time constant were too large, every short spanning connection would
be an unusually short pair. The actual normalized seminorm supplies geometry. -/
lemma chemicalSpan_subset_pair {d : ℕ} (i : Fin d) (L : ℕ) (K : ℝ)
    (N : Seminorm ℝ (Fin d → ℝ))
    (hunit : ∀ j, N (Pi.single j 1)=1)
    (hreflect : ∀ j x, N (coordinateReflection j x)=N x)
    {μ ε : ℝ} (hμ : 0≤μ) (hε : ε≤1) (hlarge : 2*K ≤ (1-ε)*μ) :
    chemicalSpanEvent i L K ⊆ chemicalPairEvent i L N μ ε := by
  intro ω hω
  obtain ⟨z,hsep,hshort⟩ := Set.mem_iUnion.mp hω
  apply Set.mem_iUnion.mpr
  refine ⟨z,hsep,?_⟩
  have hnorm := (chemicalNorm_comparison N hunit hreflect
    (fun j => (z.2.val j:ℝ)-(z.1.val j:ℝ))).1 i
  have hdist : (L:ℝ)/2 ≤ N (fun j => (z.2.val j:ℝ)-(z.1.val j:ℝ)) :=
    hsep.trans ((le_abs_self _).trans hnorm)
  have hcoef : 0≤(1-ε)*μ := mul_nonneg (sub_nonneg.mpr hε) hμ
  have h1 := mul_le_mul_of_nonneg_left hdist hcoef
  have h2 := mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg L : (0:ℝ)≤L)
  have hthreshold : K*(L:ℝ) ≤ (1-ε)*μ*N (fun j => (z.2.val j:ℝ)-(z.1.val j:ℝ)) := by
    nlinarith
  obtain ⟨m,hm,hconn⟩ := hshort
  exact ⟨m,hm.trans hthreshold,hconn⟩

/-- At any epsilon, positive crossing probability and the proved bad-pair limit
force the source numerical bound. Arbitrary cofinal scales retain the paper's
restriction L=L(M), rather than assuming crossings at every integer size. -/
theorem chemical_upper_at_epsilon {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : Seminorm ℝ (Fin d → ℝ))
    (hunit : ∀ j, N (Pi.single j 1)=1)
    (hreflect : ∀ j x, N (coordinateReflection j x)=N x)
    {μ ε K cA : ℝ} (hμ : 0≤μ) (hε : ε≤1) (hcA : 0<cA)
    (scales : ℕ → ℕ) (hscales : Tendsto scales atTop atTop)
    (hcross : ∀ᶠ M : ℕ in atTop, cA ≤ (percolation d p).real (chemicalSpanEvent i (scales M) K))
    (hGM : ∃ B : ℝ, 0<B ∧ ∃ R : ℝ, UniformChemicalLowerTail d p N μ ε B R) :
    (1-ε)*μ < 2*K := by
  by_contra h
  have hlarge : 2*K ≤ (1-ε)*μ := le_of_not_gt h
  have hlim := (chemical_pairs p i N μ ε hGM).comp hscales
  have he := hlim.eventually (gt_mem_nhds hcA)
  obtain ⟨M,hM⟩ := (hcross.and he).exists
  have hsub := measureReal_mono (μ := percolation d p)
    (chemicalSpan_subset_pair i (scales M) K N hunit hreflect hμ hε hlarge)
  exact (not_lt_of_ge (hM.1.trans hsub)) hM.2

/-- Source prop.chem.upper reduction, with epsilon removed. The actual short
crossing probability is the unresolved paper-specific dependency lem.chem.crossing;
the GM lower tail is a named standard literature input. -/
theorem chemical_timeConstant_upper_of_crossings {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : Seminorm ℝ (Fin d → ℝ))
    (hunit : ∀ j, N (Pi.single j 1)=1)
    (hreflect : ∀ j x, N (coordinateReflection j x)=N x)
    {μ K cA : ℝ} (hμ : 0≤μ) (hK : 0≤K) (hcA : 0<cA)
    (scales : ℕ → ℕ) (hscales : Tendsto scales atTop atTop)
    (hcross : ∀ᶠ M : ℕ in atTop, cA ≤ (percolation d p).real (chemicalSpanEvent i (scales M) K))
    (hGM : ∀ ε : ℝ, 0<ε → ε<1 → ∃ B : ℝ, 0<B ∧ ∃ R : ℝ,
      UniformChemicalLowerTail d p N μ ε B R) : μ ≤ 2*K := by
  by_contra h
  have hgap : 2*K<μ := lt_of_not_ge h
  have hpos : 0<μ := lt_of_le_of_lt (by positivity) hgap
  let ε := (μ-2*K)/(2*μ)
  have hepos : 0<ε := div_pos (sub_pos.mpr hgap) (by positivity)
  have heone : ε<1 := (div_lt_one (by positivity : 0<2*μ)).2 (by linarith)
  have he := chemical_upper_at_epsilon p i N hunit hreflect hμ heone.le hcA
    scales hscales hcross (hGM ε hepos heone)
  have hid : ε*(2*μ)=μ-2*K := div_mul_cancel₀ _ (ne_of_gt (by positivity : 0<2*μ))
  nlinarith

end NearCritical
