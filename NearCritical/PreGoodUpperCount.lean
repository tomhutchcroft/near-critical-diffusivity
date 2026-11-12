module

public import NearCritical.FiniteClusterFamily
public import NearCritical.WaterCubeOrdinaryArms
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! NEW source prop.proba.pregood Step3: actual distinct component count is
controlled by a measurable rooted spanning count and the standard ordinary arm
input. No cluster-count probability/expectation conclusion is an input. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Actual root's finite component meets every labelled face. -/
def finiteRootSpanningEvent {d : ℕ} {φ : Type*} (U : Finset (Vertex d))
    (faces : φ → Finset (Vertex d)) (root : Vertex d) : Set (Configuration d) :=
  {ω | ∀ i, (finiteBoxCluster ω U root ∩ faces i).Nonempty}

lemma measurableSet_finiteRootSpanningEvent {d : ℕ} {φ : Type*} [Fintype φ]
    (U : Finset (Vertex d)) (faces : φ → Finset (Vertex d)) (root : Vertex d) :
    MeasurableSet (finiteRootSpanningEvent U faces root) := by
  classical
  have he : finiteRootSpanningEvent U faces root =
      ⋂ i, ⋃ y : Vertex d, ({ω : Configuration d | y ∈ U ∧ y ∈ faces i} ∩
        {ω | (restrictedGraph ω (U : Set (Vertex d))).Reachable root y}) := by
    ext ω
    simp only [finiteRootSpanningEvent, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_iUnion, Set.mem_inter_iff, Finset.Nonempty, Finset.mem_inter,
      mem_finiteBoxCluster]
    constructor
    · intro h i
      obtain ⟨y, ⟨hy, hr⟩, hf⟩ := h i
      exact ⟨y, ⟨hy, hf⟩, hr⟩
    · intro h i
      obtain ⟨y, ⟨hy, hf⟩, hr⟩ := h i
      exact ⟨y, ⟨hy, hr⟩, hf⟩
  rw [he]
  exact MeasurableSet.iInter fun i => MeasurableSet.iUnion fun y =>
    (MeasurableSet.const _).inter (measurableSet_graphReachable
      (fun ω => restrictedGraph ω (U : Set (Vertex d))) (measurableSet_restricted_adj _) root y)

/-- Count of rooted spanning vertices, as an actual measurable finite sum. -/
def rootSpanningCount {d : ℕ} {φ : Type*} (U : Finset (Vertex d))
    (faces : φ → Finset (Vertex d)) (ω : Configuration d) : ℝ :=
  ∑ x ∈ U, (finiteRootSpanningEvent U faces x).indicator (fun _ => (1:ℝ)) ω

lemma rootSpanningCount_eq_card {d : ℕ} {φ : Type*}
    (U : Finset (Vertex d)) (faces : φ → Finset (Vertex d)) (ω : Configuration d) :
    rootSpanningCount U faces ω =
      (filteredClusterVertices ω U (fun C => ∀ i, (C ∩ faces i).Nonempty)).card := by
  classical
  simp [rootSpanningCount, filteredClusterVertices, finiteRootSpanningEvent,
    Set.indicator_apply, Finset.sum_boole]

lemma rootSpanningCount_nonneg {d : ℕ} {φ : Type*}
    (U : Finset (Vertex d)) (faces : φ → Finset (Vertex d)) (ω : Configuration d) :
    0 ≤ rootSpanningCount U faces ω := by
  rw [rootSpanningCount_eq_card]
  positivity

lemma integrable_rootSpanningCount {d : ℕ} {φ : Type*} [Fintype φ]
    (p : unitInterval) (U : Finset (Vertex d)) (faces : φ → Finset (Vertex d)) :
    Integrable (rootSpanningCount U faces) (percolation d p) := by
  apply integrable_finsetSum
  intro x hx
  exact (integrable_const (1:ℝ)).indicator (measurableSet_finiteRootSpanningEvent U faces x)

lemma integral_rootSpanningCount {d : ℕ} {φ : Type*} [Fintype φ]
    (p : unitInterval) (U : Finset (Vertex d)) (faces : φ → Finset (Vertex d)) :
    ∫ ω, rootSpanningCount U faces ω ∂percolation d p =
      ∑ x ∈ U, (percolation d p).real (finiteRootSpanningEvent U faces x) := by
  unfold rootSpanningCount
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x hx
    exact integral_indicator_one (measurableSet_finiteRootSpanningEvent U faces x)
  · intro x hx
    exact (integrable_const (1:ℝ)).indicator (measurableSet_finiteRootSpanningEvent U faces x)

/-- The actual full face-spanning event yields an ordinary arm. One of the two
faces in a fixed coordinate is distance at least r from ANY root. -/
theorem finiteRootSpanning_subset_ordinary {d r : ℕ} (i : Fin d) (hr : 1≤r)
    (x : Vertex d) :
    finiteRootSpanningEvent (centeredBox d r) (signedCubeFace d r) x ⊆
      extrinsicRadiusArmEvent x ((r:ℝ)/2) := by
  intro ω hω
  by_cases hx : x i ≤ 0
  · obtain ⟨y, hy⟩ := (hω (i,true))
    obtain ⟨hyC, hyface⟩ := Finset.mem_inter.mp hy
    have hycoord : y i = (r:ℤ) := by
      exact (Finset.mem_filter.mp hyface).2
    have hdist := dist_le_pi_dist x y i
    have hxr : (x i : ℝ) ≤ 0 := by exact_mod_cast hx
    rw [Int.dist_eq, hycoord, Int.cast_natCast, abs_of_nonpos (by linarith [show (0:ℝ)≤r by positivity] :
      (x i : ℝ) - (r:ℝ) ≤ 0)] at hdist
    refine ⟨y, ?_, ?_⟩
    · have hrr : (1:ℝ)≤r := by exact_mod_cast hr
      linarith
    · have hle : restrictedGraph ω (centeredBox d r : Set (Vertex d)) ≤ openGraph ω :=
        fun _ _ h => h.1
      exact SimpleGraph.Reachable.mono hle
        ((mem_finiteBoxCluster ω (centeredBox d r) x y).mp hyC).2
  · obtain ⟨y, hy⟩ := (hω (i,false))
    obtain ⟨hyC, hyface⟩ := Finset.mem_inter.mp hy
    have hycoord : y i = -(r:ℤ) := by
      exact (Finset.mem_filter.mp hyface).2
    have hdist := dist_le_pi_dist x y i
    have hxr : (0:ℝ) < x i := by exact_mod_cast (lt_of_not_ge hx)
    rw [Int.dist_eq, hycoord, Int.cast_neg, Int.cast_natCast, sub_neg_eq_add,
      abs_of_nonneg (by positivity : 0 ≤ (x i : ℝ)+(r:ℝ))] at hdist
    refine ⟨y, ?_, ?_⟩
    · have hrr : (1:ℝ)≤r := by exact_mod_cast hr
      linarith
    · have hle : restrictedGraph ω (centeredBox d r : Set (Vertex d)) ≤ openGraph ω :=
        fun _ _ h => h.1
      exact SimpleGraph.Reachable.mono hle
        ((mem_finiteBoxCluster ω (centeredBox d r) x y).mp hyC).2

/-- No spanning probability estimate is assumed: it is deduced from the named
STANDARD ordinary-arm input under the actual critical law. -/
theorem finiteRootSpanning_probability_le {d r : ℕ} (i : Fin d) (hr : 1≤r)
    {C : ℝ} (ordinary : OrdinaryArmWindowInput d C) (x : Vertex d) :
    (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d r) (signedCubeFace d r) x) ≤ C/(r:ℝ)^2 := by
  apply (measureReal_mono (finiteRootSpanning_subset_ordinary i hr x)).trans
  apply ordinary (criticalPoint d) x r hr
  exact le_add_of_nonneg_right (inv_nonneg.mpr (sq_nonneg _))

/-- Source Step3 upper tail for ACTUAL distinct filtered components. Only size,
spanning implication and the standard ordinary-arm bound are inputs. P need not
be measurable here: this is a valid outer-probability bound. No assertion of
full typical-count measurability is made. -/
theorem preGood_cluster_count_upper_tail {d r : ℕ} (i : Fin d) (hr : 1≤r)
    {C v T : ℝ} (ordinary : OrdinaryArmWindowInput d C) (hv : 0<v) (hT : 0<T)
    (P : Configuration d → Finset (Vertex d) → Prop)
    (hsize : ∀ ω A, A ∈ filteredClusterFamily ω (centeredBox d r) (P ω) → v ≤ (A.card:ℝ))
    (hspan : ∀ ω A, P ω A → ∀ j, (A ∩ signedCubeFace d r j).Nonempty) :
    (percolation d (criticalPoint d)).real
      {ω | T ≤ ((filteredClusterFamily ω (centeredBox d r) (P ω)).card:ℝ)} ≤
      ((centeredBox d r).card:ℝ)*(C/(r:ℝ)^2)/(v*T) := by
  let μ := percolation d (criticalPoint d)
  let Z := rootSpanningCount (centeredBox d r) (signedCubeFace d r)
  have hdom (ω : Configuration d) :
      v*((filteredClusterFamily ω (centeredBox d r) (P ω)).card:ℝ) ≤ Z ω := by
    change v*((filteredClusterFamily ω (centeredBox d r) (P ω)).card:ℝ) ≤
      rootSpanningCount (centeredBox d r) (signedCubeFace d r) ω
    rw [rootSpanningCount_eq_card]
    exact filteredClusterFamily_volume_count_of_implies ω (centeredBox d r) (P ω) _
      (hsize ω) (hspan ω)
  have hsub : {ω | T ≤ ((filteredClusterFamily ω (centeredBox d r) (P ω)).card:ℝ)} ⊆
      {ω | v*T ≤ Z ω} := by
    intro ω hω
    exact (mul_le_mul_of_nonneg_left hω hv.le).trans (hdom ω)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (rootSpanningCount_nonneg (centeredBox d r) (signedCubeFace d r)))
    (integrable_rootSpanningCount (criticalPoint d) (centeredBox d r) (signedCubeFace d r)) (v*T)
  have hmean : (∫ ω, Z ω ∂μ) ≤ ((centeredBox d r).card:ℝ)*(C/(r:ℝ)^2) := by
    change (∫ ω, rootSpanningCount (centeredBox d r) (signedCubeFace d r) ω
      ∂percolation d (criticalPoint d)) ≤ _
    rw [integral_rootSpanningCount]
    calc
      _ ≤ ∑ x ∈ centeredBox d r, C/(r:ℝ)^2 := Finset.sum_le_sum
        (fun x hx => finiteRootSpanning_probability_le i hr ordinary x)
      _ = _ := by simp
  have hbound : μ.real {ω | v*T ≤ Z ω} ≤
      ((centeredBox d r).card:ℝ)*(C/(r:ℝ)^2)/(v*T) := by
    apply (le_div_iff₀ (mul_pos hv hT)).mpr
    nlinarith [hmark]
  exact (measureReal_mono hsub).trans hbound

lemma card_centeredBox_exact (d r : ℕ) : (centeredBox d r).card = (2*r+1)^d := by
  change (rectangularBox (fun _ : Fin d => r)).card = (2*r+1)^d
  simp [card_rectangularBox]

/-- Literal n^(d-6) source scale, n=2r+1. The factor9 comes from n<=3r;
no volume/count exponent conversion is an input. -/
theorem preGood_cluster_count_scale_tail {d r : ℕ} (i : Fin d) (hr : 1≤r) (hd : 6≤d)
    {C cv A : ℝ} (hC : 0≤C) (ordinary : OrdinaryArmWindowInput d C)
    (hcv : 0<cv) (hA : 0<A) (P : Configuration d → Finset (Vertex d) → Prop)
    (hsize : ∀ ω E, E ∈ filteredClusterFamily ω (centeredBox d r) (P ω) →
      cv*((2*r+1:ℕ):ℝ)^4 ≤ (E.card:ℝ))
    (hspan : ∀ ω E, P ω E → ∀ j, (E ∩ signedCubeFace d r j).Nonempty) :
    (percolation d (criticalPoint d)).real
      {ω | A*((2*r+1:ℕ):ℝ)^(d-6) ≤
        ((filteredClusterFamily ω (centeredBox d r) (P ω)).card:ℝ)} ≤ 9*C/(cv*A) := by
  let L : ℝ := ((2*r+1:ℕ):ℝ)
  have hL : 0<L := by dsimp [L]; positivity
  have hrpos : (0:ℝ)<r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hcard : ((centeredBox d r).card:ℝ) = L^d := by
    dsimp [L]
    exact_mod_cast card_centeredBox_exact d r
  have ht := preGood_cluster_count_upper_tail i hr ordinary
    (mul_pos hcv (pow_pos hL 4)) (mul_pos hA (pow_pos hL (d-6))) P hsize hspan
  rw [hcard] at ht
  have hp : L^d = L^(d-6)*L^6 := by
    rw [← pow_add]
    congr 1
    omega
  have heq : L^d*(C/(r:ℝ)^2)/(cv*L^4*(A*L^(d-6))) = C*L^2/(cv*A*(r:ℝ)^2) := by
    rw [hp]
    field_simp [ne_of_gt hL, ne_of_gt hrpos, ne_of_gt hcv, ne_of_gt hA]
  have hgap : L^2 ≤ 9*(r:ℝ)^2 := by
    have hr1 : (1:ℝ)≤r := by exact_mod_cast hr
    have hLeq : L=2*(r:ℝ)+1 := by simp [L]
    rw [hLeq]
    nlinarith [sq_nonneg ((r:ℝ)-1)]
  apply ht.trans
  rw [heq]
  apply (div_le_div_iff₀ (mul_pos (mul_pos hcv hA) (sq_pos_of_pos hrpos)) (mul_pos hcv hA)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hgap (mul_nonneg hC (mul_pos hcv hA).le)]

/-- Explicit upper pre-good constant, independent of r. Failure probability is
at most epsilon/3, exactly the allocation of source Step3. Lower count and
regularity-loss events are not claimed here. -/
theorem preGood_cluster_count_upper_failure {d r : ℕ} (i : Fin d) (hr : 1≤r) (hd : 6≤d)
    {C cv ε : ℝ} (hC : 0<C) (ordinary : OrdinaryArmWindowInput d C)
    (hcv : 0<cv) (hε : 0<ε) (P : Configuration d → Finset (Vertex d) → Prop)
    (hsize : ∀ ω E, E ∈ filteredClusterFamily ω (centeredBox d r) (P ω) →
      cv*((2*r+1:ℕ):ℝ)^4 ≤ (E.card:ℝ))
    (hspan : ∀ ω E, P ω E → ∀ j, (E ∩ signedCubeFace d r j).Nonempty) :
    (percolation d (criticalPoint d)).real
      {ω | (27*C/(cv*ε))*((2*r+1:ℕ):ℝ)^(d-6) ≤
        ((filteredClusterFamily ω (centeredBox d r) (P ω)).card:ℝ)} ≤ ε/3 := by
  have hA : 0 < 27*C/(cv*ε) := by positivity
  have h := preGood_cluster_count_scale_tail i hr hd hC.le ordinary hcv hA P hsize hspan
  have heq : 9*C/(cv*(27*C/(cv*ε))) = ε/3 := by
    field_simp [ne_of_gt hC, ne_of_gt hcv, ne_of_gt hε]; ring
  rwa [heq] at h

end NearCritical
