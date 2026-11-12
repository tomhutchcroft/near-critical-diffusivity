module

public import NearCritical.SlabPioneerConvolution
public import NearCritical.BulkDomain
public import NearCritical.Russo
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Actual finite-cutoff slab row means. The cylinder law, polynomial and
Russo identities are derived from actual restricted connection events. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- Actual restricted slab connection, with BOTH endpoints checked in the
slab/vertex cutoff. No auxiliary finite graph replaces the source event. -/
def finiteSlabConnectionEvent {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (m n : ℤ) (x y : Vertex d) : Set (Configuration d) :=
  connectionToSetEvent (finiteHeightSlab i m n ∩ (U : Set (Vertex d))) x {y}

/-- Restricted paths within U use only bonds whose TWO endpoints belong to U. -/
theorem restrictedGraph_eq_of_internalBondSet_agree {d : ℕ} (U : Finset (Vertex d))
    (S : Set (Vertex d)) (hSU : S ⊆ (U : Set (Vertex d))) (ω θ : Configuration d)
    (hagree : ∀ e ∈ internalBondSet U, ω e = θ e) :
    restrictedGraph ω S = restrictedGraph θ S := by
  have hle : ∀ (α β : Configuration d), (∀ e ∈ internalBondSet U, α e = β e) →
      restrictedGraph α S ≤ restrictedGraph β S := by
    intro α β hαβ x y hxy
    obtain ⟨⟨e, he, hends⟩, hxS, hyS⟩ := hxy
    have hxU := hSU hxS
    have hyU := hSU hyS
    have heU : e ∈ internalBondSet U := by
      apply (mem_internalBondSet U e).mpr
      rcases hends with ⟨hxb, hyt⟩ | ⟨hyb, hxt⟩
      · exact ⟨hxb ▸ hxU, hyt ▸ hyU⟩
      · exact ⟨hyb ▸ hyU, hxt ▸ hxU⟩
    exact ⟨⟨e, (hαβ e heU).symm.trans he, hends⟩, hxS, hyS⟩
  exact le_antisymm (hle ω θ hagree) (hle θ ω (fun e he ↦ (hagree e he).symm))

/-- Universal outside-assignment invariance of actual finite-domain events. -/
theorem connectionToSetEvent_iff_of_internalBondSet_agree {d : ℕ}
    (U : Finset (Vertex d)) (S : Set (Vertex d)) (hSU : S ⊆ (U : Set (Vertex d)))
    (ω θ : Configuration d) (hagree : ∀ e ∈ internalBondSet U, ω e = θ e)
    (x : Vertex d) (B : Set (Vertex d)) :
    ω ∈ connectionToSetEvent S x B ↔ θ ∈ connectionToSetEvent S x B := by
  change (x ∈ S ∧ ∃ y, y ∈ B ∧ y ∈ S ∧ (restrictedGraph ω S).Reachable x y) ↔
    (x ∈ S ∧ ∃ y, y ∈ B ∧ y ∈ S ∧ (restrictedGraph θ S).Reachable x y)
  rw [restrictedGraph_eq_of_internalBondSet_agree U S hSU ω θ hagree]

/-- The local event is obtained by extending the internal bits with closed
outside bits. The following exact cylinder theorem proves this choice harmless. -/
def finiteSlabLocalConnectionEvent {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (m n : ℤ) (x y : Vertex d) : Set ((e : internalBondSet U) → Bool) :=
  {η | extendConfiguration (internalBondSet U) (fun _ ↦ false) η ∈
    finiteSlabConnectionEvent U i m n x y}

theorem finiteSlabConnectionEvent_eq_preimage {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    finiteSlabConnectionEvent U i m n x y = (internalBondSet U).restrict ⁻¹'
      finiteSlabLocalConnectionEvent U i m n x y := by
  ext ω
  change ω ∈ finiteSlabConnectionEvent U i m n x y ↔
    extendConfiguration (internalBondSet U) (fun _ ↦ false) ((internalBondSet U).restrict ω) ∈
      finiteSlabConnectionEvent U i m n x y
  apply connectionToSetEvent_iff_of_internalBondSet_agree U _ (fun _ hz ↦ hz.2) ω _ _ x {y}
  intro e he
  simp [extendConfiguration, he]

lemma finiteSlabConnectionEvent_empty_of_start_outside {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d)
    (hx : x ∉ finiteHeightSlab i m n ∩ (U : Set (Vertex d))) :
    finiteSlabConnectionEvent U i m n x y = ∅ := by
  ext ω
  simp [finiteSlabConnectionEvent, connectionToSetEvent, hx]

lemma finiteSlabConnectionEvent_empty_of_end_outside {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d)
    (hy : y ∉ finiteHeightSlab i m n ∩ (U : Set (Vertex d))) :
    finiteSlabConnectionEvent U i m n x y = ∅ := by
  ext ω
  constructor
  · rintro ⟨_, z, hz, hzS, _⟩
    have hzy : z = y := hz
    subst z
    exact hy hzS
  · simp

/-- A nil path is present exactly when its endpoint belongs to the actual domain. -/
lemma finiteSlabConnectionEvent_self {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) :
    finiteSlabConnectionEvent U i m n x x =
      {_ω : Configuration d | x ∈ finiteHeightSlab i m n ∩ (U : Set (Vertex d))} := by
  ext ω
  constructor
  · exact fun h ↦ h.1
  · intro hx
    exact ⟨hx, x, rfl, hx, SimpleGraph.Reachable.refl x⟩

/-- Actual finite row mass, with arbitrary starting vertex (both boundary
orientations are allowed), and endpoints in the cutoff at level j. -/
def finiteSlabRowMean {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) : ℝ :=
  ∑ y ∈ U, if y i = j then (percolation d p).real (finiteSlabConnectionEvent U i m n x y) else 0

def finiteSlabRowCount {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) (ω : Configuration d) : ℝ :=
  ∑ y ∈ U, if y i = j then (if ω ∈ finiteSlabConnectionEvent U i m n x y then 1 else 0) else 0

def finiteSlabRowObservable {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    (η : (e : internalBondSet U) → Bool) : ℝ :=
  ∑ y ∈ U, if y i = j then (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0) else 0

lemma finiteSlabRowCount_eq_observable {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) (ω : Configuration d) :
    finiteSlabRowCount U i m n x j ω =
      finiteSlabRowObservable U i m n x j ((internalBondSet U).restrict ω) := by
  apply Finset.sum_congr rfl
  intro y _
  rw [finiteSlabConnectionEvent_eq_preimage]
  rfl

lemma finiteSlabRowMean_nonneg {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) : 0 ≤ finiteSlabRowMean p U i m n x j := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

private lemma finiteExpectation_finset_sum {E Y : Type*} [Fintype E]
    (q : ℝ) (s : Finset Y) (g : Y → (E → Bool) → ℝ) :
    finiteExpectation q (fun η ↦ ∑ y ∈ s, g y η) = ∑ y ∈ s, finiteExpectation q (g y) := by
  simp only [finiteExpectation, Finset.sum_mul]
  exact Finset.sum_comm

/-- The actual infinite-law event probability equals its finite Bernoulli sum. -/
lemma finiteSlabConnectionEvent_probability {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    (percolation d p).real (finiteSlabConnectionEvent U i m n x y) =
      finiteExpectation (p : ℝ) (fun η ↦ if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0) := by
  rw [finiteSlabConnectionEvent_eq_preimage]
  exact (eventProbability_cylinder d p (internalBondSet U) _).symm

/-- Literal row mean, not an assumed finite-event probability, is a finite expectation. -/
theorem finiteSlabRowMean_eq_finiteExpectation {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteSlabRowMean p U i m n x j =
      finiteExpectation (p : ℝ) (finiteSlabRowObservable U i m n x j) := by
  unfold finiteSlabRowMean finiteSlabRowObservable
  rw [finiteExpectation_finset_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y i = j
  · simp only [ite_eq_left hy]
    exact finiteSlabConnectionEvent_probability p U i m n x y
  · simp only [ite_eq_right hy, finiteExpectation, zero_mul, Finset.sum_const_zero]

/-- Actual percolation expectation of the actual finite row count. -/
theorem integral_finiteSlabRowCount {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    (∫ ω, finiteSlabRowCount U i m n x j ω ∂percolation d p) =
      finiteExpectation (p : ℝ) (finiteSlabRowObservable U i m n x j) := by
  simpa only [finiteSlabRowCount_eq_observable] using percolation_cylinder_expectation d p
    (internalBondSet U) (finiteSlabRowObservable U i m n x j)

def finiteSlabRowExpectation {d : ℕ} (q : ℝ) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) : ℝ :=
  finiteExpectation q (finiteSlabRowObservable U i m n x j)

def finiteSlabRowPolynomial {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) : Polynomial ℝ :=
  annealedPolynomial (finiteSlabRowObservable U i m n x j)

theorem finiteSlabRowPolynomial_eval {d : ℕ} (q : ℝ) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    (finiteSlabRowPolynomial U i m n x j).eval q = finiteSlabRowExpectation q U i m n x j :=
  eval_annealedPolynomial q _

theorem finiteSlabRowExpectation_hasDerivAt {d : ℕ} (q : ℝ) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    HasDerivAt (fun r ↦ finiteSlabRowExpectation r U i m n x j)
      ((finiteSlabRowPolynomial U i m n x j).derivative.eval q) q :=
  finiteExpectation_hasDerivAt q _

/-- The actual finite row's real extension has the existing finite Russo derivative. -/
theorem finiteSlabRowExpectation_russo {d : ℕ} (q : ℝ) (hq : q ≠ 1) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    HasDerivAt (fun r ↦ finiteSlabRowExpectation r U i m n x j)
      ((1 - q)⁻¹ * ∑ e : internalBondSet U, finiteExpectation q (fun η ↦
        finiteSlabRowObservable U i m n x j (BernoulliCalculus.forceOpen e η) -
          finiteSlabRowObservable U i m n x j η)) q :=
  BernoulliCalculus.finiteExpectation_russo q hq _

lemma finiteSlabConnectionEvent_measurable {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    MeasurableSet (finiteSlabConnectionEvent U i m n x y) :=
  measurableSet_connectionToSetEvent _ _ _

lemma finiteSlabConnectionEvent_increasing {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    BK.Increasing (finiteSlabConnectionEvent U i m n x y) :=
  connectionToSetEvent_increasing _ _ _

lemma finiteSlabLocalConnectionEvent_increasing {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    BK.Increasing (finiteSlabLocalConnectionEvent U i m n x y) := by
  intro η θ hηθ hη
  apply finiteSlabConnectionEvent_increasing U i m n x y ?_ hη
  intro e he
  by_cases hs : e ∈ internalBondSet U
  · simp only [extendConfiguration, dite_eq_left hs] at he ⊢
    exact hηθ ⟨e, hs⟩ he
  · simp [extendConfiguration, hs] at he

lemma finiteSlabRowMean_eq_expectation {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteSlabRowMean p U i m n x j = finiteSlabRowExpectation (p : ℝ) U i m n x j :=
  finiteSlabRowMean_eq_finiteExpectation p U i m n x j

lemma finiteSlabRowMean_eq_integral {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteSlabRowMean p U i m n x j = ∫ ω, finiteSlabRowCount U i m n x j ω ∂percolation d p :=
  (finiteSlabRowMean_eq_finiteExpectation p U i m n x j).trans
    (integral_finiteSlabRowCount p U i m n x j).symm

lemma finiteSlabRowMean_eq_polynomial_eval {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteSlabRowMean p U i m n x j = (finiteSlabRowPolynomial U i m n x j).eval (p : ℝ) :=
  (finiteSlabRowMean_eq_expectation p U i m n x j).trans
    (finiteSlabRowPolynomial_eval (p : ℝ) U i m n x j).symm

/-- All polynomial regularity is exhibited for the actual real extension. -/
theorem finiteSlabRowExpectation_contDiff {d : ℕ} (r : WithTop ℕ∞) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    ContDiff ℝ r (fun q ↦ finiteSlabRowExpectation q U i m n x j) := by
  simpa only [Polynomial.coe_aeval_eq_eval, finiteSlabRowPolynomial_eval] using
    (finiteSlabRowPolynomial U i m n x j).contDiff_aeval (𝕜 := ℝ) r

lemma finiteSlabRowExpectation_nonneg {d : ℕ} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    0 ≤ finiteSlabRowExpectation q U i m n x j := by
  let p : unitInterval := ⟨q, hq, hq1⟩
  exact (finiteSlabRowMean_eq_expectation p U i m n x j) ▸
    finiteSlabRowMean_nonneg p U i m n x j

/-- Endpoint reversal is exact for the same cutoff and domain. -/
lemma finiteSlabConnectionEvent_symm {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    finiteSlabConnectionEvent U i m n x y = finiteSlabConnectionEvent U i m n y x :=
  connectionToSetEvent_singleton_symm _ x y

/-- Actual column mass, for the boundary-END family needed along with rows. -/
def finiteSlabColumnMean {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n k : ℤ) (y : Vertex d) : ℝ :=
  ∑ x ∈ U, if x i = k then (percolation d p).real (finiteSlabConnectionEvent U i m n x y) else 0

lemma finiteSlabColumnMean_eq_rowMean {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n k : ℤ) (y : Vertex d) :
    finiteSlabColumnMean p U i m n k y = finiteSlabRowMean p U i m n y k := by
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteSlabConnectionEvent_symm U i m n x y]

def finiteSlabColumnExpectation {d : ℕ} (q : ℝ) (U : Finset (Vertex d))
    (i : Fin d) (m n k : ℤ) (y : Vertex d) : ℝ :=
  finiteSlabRowExpectation q U i m n y k

lemma finiteSlabColumnMean_eq_expectation {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n k : ℤ) (y : Vertex d) :
    finiteSlabColumnMean p U i m n k y = finiteSlabColumnExpectation (p : ℝ) U i m n k y :=
  (finiteSlabColumnMean_eq_rowMean p U i m n k y).trans
    (finiteSlabRowMean_eq_expectation p U i m n y k)

lemma finiteSlabColumnMean_nonneg {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n k : ℤ) (y : Vertex d) : 0 ≤ finiteSlabColumnMean p U i m n k y := by
  rw [finiteSlabColumnMean_eq_rowMean]
  exact finiteSlabRowMean_nonneg p U i m n y k

theorem finiteSlabColumnExpectation_hasDerivAt {d : ℕ} (q : ℝ) (U : Finset (Vertex d))
    (i : Fin d) (m n k : ℤ) (y : Vertex d) :
    HasDerivAt (fun r ↦ finiteSlabColumnExpectation r U i m n k y)
      ((finiteSlabRowPolynomial U i m n y k).derivative.eval q) q :=
  finiteSlabRowExpectation_hasDerivAt q U i m n y k

theorem finiteSlabColumnExpectation_contDiff {d : ℕ} (r : WithTop ℕ∞) (U : Finset (Vertex d))
    (i : Fin d) (m n k : ℤ) (y : Vertex d) :
    ContDiff ℝ r (fun q ↦ finiteSlabColumnExpectation q U i m n k y) :=
  finiteSlabRowExpectation_contDiff r U i m n y k

end NearCritical
