module

public import NearCritical.PreGoodUpperCount

/-! NEW pre-good Step2: boundary regularity deficit gives many distinct marked
points, then a Markov bound on cluster loss. The source irregular first-moment
estimate (prop.choice_c) remains an explicit UNRESOLVED NEW input. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Marked subsets of distinct actual components are disjoint. -/
theorem component_mark_count_bound {d : ℕ} (ω : Configuration d) (U B : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) {b : ℝ}
    (hmark : ∀ C ∈ filteredClusterFamily ω U P, b ≤ ((C ∩ B).card:ℝ)) :
    b*(filteredClusterFamily ω U P).card ≤ B.card := by
  classical
  let F := filteredClusterFamily ω U P
  have hd : (F : Set (Finset (Vertex d))).PairwiseDisjoint (fun C => C ∩ B) := by
    intro C hC E hE hne
    exact (finiteClusterFamily_disjoint ω U (Finset.mem_filter.mp hC).1
      (Finset.mem_filter.mp hE).1 hne).mono Finset.inter_subset_left Finset.inter_subset_left
  have hu : F.biUnion (fun C => C ∩ B) ⊆ B := by
    intro x hx
    obtain ⟨C, _, hC⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hC).2
  have hc := (Finset.card_biUnion hd).symm.trans_le (Finset.card_le_card hu)
  calc
    _ = ∑ C ∈ F, b := by simp [F, mul_comm]
    _ ≤ ∑ C ∈ F, ((C ∩ B).card:ℝ) := Finset.sum_le_sum hmark
    _ ≤ B.card := by exact_mod_cast hc

/-- Source bad clusters: a candidate fails the lower regular-point bound on
at least one patch. The candidate predicate and regularity relation are explicit. -/
def regularityBadCluster {d : ℕ} {φ : Type*}
    (P : Finset (Vertex d) → Prop) (patch : φ → Finset (Vertex d))
    (regular : Vertex d → Prop) (b : ℝ) (C : Finset (Vertex d)) : Prop :=
  P C ∧ ∃ i, (((C ∩ patch i).filter regular).card:ℝ) < b

/-- At least2b boundary points and fewer thanb regular points force at leastb
marked irregular points. This conclusion is derived, not a per-bad-cluster premise. -/
theorem regularity_deficit_mark_bound {d : ℕ} {φ : Type*}
    (ω : Configuration d) (U B : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) (patch : φ → Finset (Vertex d))
    (regular : Vertex d → Prop) {b : ℝ}
    (hpatch : ∀ C ∈ filteredClusterFamily ω U P, ∀ i, 2*b ≤ ((C ∩ patch i).card:ℝ))
    (hcover : ∀ C ∈ filteredClusterFamily ω U P, ∀ i,
      (C ∩ patch i).filter (fun x => ¬regular x) ⊆ B) :
    b*(filteredClusterFamily ω U (regularityBadCluster P patch regular b)).card ≤ B.card := by
  classical
  apply component_mark_count_bound ω U B
  intro C hC
  obtain ⟨hactual, hP, i, hbad⟩ := Finset.mem_filter.mp hC
  have hCP : C ∈ filteredClusterFamily ω U P := Finset.mem_filter.mpr ⟨hactual, hP⟩
  have hc := Finset.card_filter_add_card_filter_not (s := C ∩ patch i) regular
  have hhalf : b ≤ (((C ∩ patch i).filter (fun x => ¬regular x)).card:ℝ) := by
    have hcR : (((C ∩ patch i).filter regular).card:ℝ) +
        (((C ∩ patch i).filter (fun x => ¬regular x)).card:ℝ) = ((C ∩ patch i).card:ℝ) := by
      exact_mod_cast hc
    linarith [hpatch C hCP i]
  have hsub : (C ∩ patch i).filter (fun x => ¬regular x) ⊆ C ∩ B := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1,
      hcover C hCP i hx⟩
  exact hhalf.trans (by exact_mod_cast Finset.card_le_card hsub)

/-- Actual finite marked-point count, expressed as measurable membership indicators. -/
def markedVertexCount {d : ℕ} (U : Finset (Vertex d)) (B : Configuration d → Finset (Vertex d))
    (ω : Configuration d) : ℝ := ∑ x ∈ U, ({η | x ∈ B η} : Set (Configuration d)).indicator (fun _ => (1:ℝ)) ω

lemma markedVertexCount_eq_card {d : ℕ} (U : Finset (Vertex d))
    (B : Configuration d → Finset (Vertex d)) (hBU : ∀ ω, B ω ⊆ U) (ω : Configuration d) :
    markedVertexCount U B ω = (B ω).card := by
  classical
  have he : U.filter (fun x => x ∈ B ω) = B ω := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hBU ω h, h⟩⟩
  simp only [markedVertexCount, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_boole]
  exact_mod_cast congrArg Finset.card he

lemma integrable_markedVertexCount {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (B : Configuration d → Finset (Vertex d))
    (hm : ∀ x ∈ U, MeasurableSet {ω | x ∈ B ω}) :
    Integrable (markedVertexCount U B) (percolation d p) := by
  apply integrable_finsetSum
  intro x hx
  exact (integrable_const (1:ℝ)).indicator (hm x hx)

lemma integral_markedVertexCount {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (B : Configuration d → Finset (Vertex d))
    (hm : ∀ x ∈ U, MeasurableSet {ω | x ∈ B ω}) :
    ∫ ω, markedVertexCount U B ω ∂percolation d p =
      ∑ x ∈ U, (percolation d p).real {ω | x ∈ B ω} := by
  unfold markedVertexCount
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun x hx => integral_indicator_one (hm x hx))
  · exact fun x hx => (integrable_const (1:ℝ)).indicator (hm x hx)

/-- Actual cluster-loss outer probability from a supplied irregular-point
first moment. This moment is the unresolved NEW prop.choice_c obligation, not
an assumed cluster-loss conclusion and not a standard literature placeholder. -/
theorem regularity_loss_markov {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (B : Configuration d → Finset (Vertex d)) (hBU : ∀ ω, B ω ⊆ U)
    (hm : ∀ x ∈ U, MeasurableSet {ω | x ∈ B ω})
    (P : Configuration d → Finset (Vertex d) → Prop) {b T E : ℝ} (hb : 0<b) (hT : 0<T)
    (hmarks : ∀ ω, b*(filteredClusterFamily ω U (P ω)).card ≤ (B ω).card)
    (hmoment : (∑ x ∈ U, (percolation d p).real {ω | x ∈ B ω}) ≤ E) :
    (percolation d p).real {ω | T ≤ ((filteredClusterFamily ω U (P ω)).card:ℝ)} ≤ E/(b*T) := by
  let Z := markedVertexCount U B
  have hsub : {ω | T ≤ ((filteredClusterFamily ω U (P ω)).card:ℝ)} ⊆ {ω | b*T ≤ Z ω} := by
    intro ω hω
    have hdom := hmarks ω
    rw [← markedVertexCount_eq_card U B hBU ω] at hdom
    exact (mul_le_mul_of_nonneg_left hω hb.le).trans hdom
  have hn : 0 ≤ᵐ[percolation d p] Z := Filter.Eventually.of_forall (fun ω => by
    change 0 ≤ markedVertexCount U B ω
    rw [markedVertexCount_eq_card U B hBU]
    positivity)
  have hmark := mul_meas_ge_le_integral_of_nonneg hn (integrable_markedVertexCount p U B hm) (b*T)
  have hmean : (∫ ω, Z ω ∂percolation d p) ≤ E := by
    change (∫ ω, markedVertexCount U B ω ∂percolation d p) ≤ E
    rwa [integral_markedVertexCount p U B hm]
  have ht : (percolation d p).real {ω | b*T ≤ Z ω} ≤ E/(b*T) := by
    apply (le_div_iff₀ (mul_pos hb hT)).mpr
    nlinarith [hmark]
  exact (measureReal_mono hsub).trans ht

/-- Source Step2's explicit loss rate. The irregular first moment below is the
UNRESOLVED NEW prop.choice_c input; the cluster-loss conclusion is derived. -/
theorem regularity_loss_source_bound {d : ℕ} {φ : Type*} (p : unitInterval)
    (U : Finset (Vertex d)) (B : Configuration d → Finset (Vertex d))
    (hBU : ∀ ω, B ω ⊆ U) (hm : ∀ x ∈ U, MeasurableSet {ω | x ∈ B ω})
    (P : Configuration d → Finset (Vertex d) → Prop) (patch : φ → Finset (Vertex d))
    (regular : Configuration d → Vertex d → Prop) (n : ℕ) (hn : 1≤n) (hd : 6≤d)
    {c c1 δ : ℝ} (hc : 0<c) (hc1 : 0<c1)
    (hpatch : ∀ ω C, C ∈ filteredClusterFamily ω U (P ω) → ∀ i,
      c*(n:ℝ)^2 ≤ ((C ∩ patch i).card:ℝ))
    (hcover : ∀ ω C, C ∈ filteredClusterFamily ω U (P ω) → ∀ i,
      (C ∩ patch i).filter (fun x => ¬regular ω x) ⊆ B ω)
    (hmoment : (∑ x ∈ U, (percolation d p).real {ω | x ∈ B ω}) ≤
      2*(d:ℝ)*δ*(n:ℝ)^(d-4)) :
    (percolation d p).real {ω | (c1/2)*(n:ℝ)^(d-6) ≤
      ((filteredClusterFamily ω U
        (regularityBadCluster (P ω) patch (regular ω) ((c/2)*(n:ℝ)^2))).card:ℝ)} ≤
      8*(d:ℝ)*δ/(c*c1) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hb : 0<(c/2)*(n:ℝ)^2 := by positivity
  have hT : 0<(c1/2)*(n:ℝ)^(d-6) := by positivity
  have hmarks (ω : Configuration d) : (c/2)*(n:ℝ)^2 *
      (filteredClusterFamily ω U
        (regularityBadCluster (P ω) patch (regular ω) ((c/2)*(n:ℝ)^2))).card ≤ (B ω).card := by
    apply regularity_deficit_mark_bound ω U (B ω) (P ω) patch (regular ω)
    · intro C hC i
      nlinarith [hpatch ω C hC i]
    · exact hcover ω
  have h := regularity_loss_markov p U B hBU hm
    (fun ω => regularityBadCluster (P ω) patch (regular ω) ((c/2)*(n:ℝ)^2))
    hb hT hmarks hmoment
  have hp : (n:ℝ)^(d-4) = (n:ℝ)^(d-6)*(n:ℝ)^2 := by
    rw [← pow_add]
    congr 1
    omega
  have heq : (2*(d:ℝ)*δ*(n:ℝ)^(d-4))/
      ((c/2)*(n:ℝ)^2*((c1/2)*(n:ℝ)^(d-6))) = 8*(d:ℝ)*δ/(c*c1) := by
    rw [hp]
    field_simp [ne_of_gt hnR, ne_of_gt hc, ne_of_gt hc1] ; ring
  rwa [heq] at h

/-- Explicit epsilon-prime choice gives exactly the epsilon/3 failure budget.
Existence of a regularity radius achieving this point first moment is NOT
asserted: that remains the new source prop.choice_c obligation. -/
theorem regularity_loss_failure {d : ℕ} {φ : Type*} (p : unitInterval)
    (U : Finset (Vertex d)) (B : Configuration d → Finset (Vertex d))
    (hBU : ∀ ω, B ω ⊆ U) (hm : ∀ x ∈ U, MeasurableSet {ω | x ∈ B ω})
    (P : Configuration d → Finset (Vertex d) → Prop) (patch : φ → Finset (Vertex d))
    (regular : Configuration d → Vertex d → Prop) (n : ℕ) (hn : 1≤n) (hd : 6≤d)
    {c c1 ε : ℝ} (hc : 0<c) (hc1 : 0<c1) (hε : 0<ε)
    (hpatch : ∀ ω C, C ∈ filteredClusterFamily ω U (P ω) → ∀ i,
      c*(n:ℝ)^2 ≤ ((C ∩ patch i).card:ℝ))
    (hcover : ∀ ω C, C ∈ filteredClusterFamily ω U (P ω) → ∀ i,
      (C ∩ patch i).filter (fun x => ¬regular ω x) ⊆ B ω)
    (hmoment : (∑ x ∈ U, (percolation d p).real {ω | x ∈ B ω}) ≤
      2*(d:ℝ)*(ε*c*c1/(24*(d:ℝ)))*(n:ℝ)^(d-4)) :
    (percolation d p).real {ω | (c1/2)*(n:ℝ)^(d-6) ≤
      ((filteredClusterFamily ω U
        (regularityBadCluster (P ω) patch (regular ω) ((c/2)*(n:ℝ)^2))).card:ℝ)} ≤ ε/3 := by
  have hdR : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have h := regularity_loss_source_bound p U B hBU hm P patch regular n hn hd
    hc hc1 hpatch hcover hmoment
  have heq : 8*(d:ℝ)*(ε*c*c1/(24*(d:ℝ)))/(c*c1) = ε/3 := by
    field_simp [ne_of_gt hdR, ne_of_gt hc, ne_of_gt hc1] ; ring
  rwa [heq] at h

/-- Candidates that fail no lower regular-boundary test. -/
def regularityGoodCluster {d : ℕ} {φ : Type*} (P : Finset (Vertex d) → Prop)
    (patch : φ → Finset (Vertex d)) (regular : Vertex d → Prop) (b : ℝ)
    (C : Finset (Vertex d)) : Prop :=
  P C ∧ ¬∃ i, (((C ∩ patch i).filter regular).card:ℝ) < b

lemma regularityGoodCluster_iff {d : ℕ} {φ : Type*} (P : Finset (Vertex d) → Prop)
    (patch : φ → Finset (Vertex d)) (regular : Vertex d → Prop) (b : ℝ)
    (C : Finset (Vertex d)) : regularityGoodCluster P patch regular b C ↔
      P C ∧ ∀ i, b ≤ (((C ∩ patch i).filter regular).card:ℝ) := by
  simp [regularityGoodCluster, not_lt]

lemma regularity_good_bad_partition {d : ℕ} {φ : Type*}
    (ω : Configuration d) (U : Finset (Vertex d)) (P : Finset (Vertex d) → Prop)
    (patch : φ → Finset (Vertex d)) (regular : Vertex d → Prop) (b : ℝ) :
    (filteredClusterFamily ω U (regularityGoodCluster P patch regular b)).card +
      (filteredClusterFamily ω U (regularityBadCluster P patch regular b)).card =
      (filteredClusterFamily ω U P).card := by
  let F := filteredClusterFamily ω U P
  let bad := fun C => ∃ i, (((C ∩ patch i).filter regular).card:ℝ) < b
  have hb : F.filter bad = filteredClusterFamily ω U (regularityBadCluster P patch regular b) := by
    ext C
    simp [F, bad, filteredClusterFamily, regularityBadCluster, and_assoc]
  have hg : F.filter (fun C => ¬bad C) =
      filteredClusterFamily ω U (regularityGoodCluster P patch regular b) := by
    ext C
    simp [F, bad, filteredClusterFamily, regularityGoodCluster, and_assoc]
  have h := Finset.card_filter_add_card_filter_not (s := F) bad
  rw [hb, hg] at h
  simpa only [F, Nat.add_comm] using h

/-- Source surviving-candidate count on the complement of the loss event. -/
theorem regularity_good_count_lower {d : ℕ} {φ : Type*}
    (ω : Configuration d) (U : Finset (Vertex d)) (P : Finset (Vertex d) → Prop)
    (patch : φ → Finset (Vertex d)) (regular : Vertex d → Prop) (b L : ℝ)
    (hstart : L ≤ ((filteredClusterFamily ω U P).card:ℝ))
    (hloss : ((filteredClusterFamily ω U (regularityBadCluster P patch regular b)).card:ℝ) < L/2) :
    L/2 ≤ ((filteredClusterFamily ω U (regularityGoodCluster P patch regular b)).card:ℝ) := by
  have h : ((filteredClusterFamily ω U (regularityGoodCluster P patch regular b)).card:ℝ) +
      ((filteredClusterFamily ω U (regularityBadCluster P patch regular b)).card:ℝ) =
      ((filteredClusterFamily ω U P).card:ℝ) := by
    exact_mod_cast regularity_good_bad_partition ω U P patch regular b
  linarith

end NearCritical
