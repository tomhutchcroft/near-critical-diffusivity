module

public import NearCritical.NestRegularBoundary
public import NearCritical.HalfSpaceLastVisit

/-! Actual heart-membership BK reduction for source NEW PxinfC upper bound.
Quantitative box/half-space estimates and boundary counting remain separate. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

/-- Inner-domain vertices adjacent to an outside vertex of the outer domain.
The full-open graph supplies purely geometric nearest-neighbor adjacency. -/
def innerEntryBoundary {d : ℕ} (Q C : Finset (Vertex d)) : Finset (Vertex d) :=
  C.filter fun v => ∃ u ∈ Q, u ∉ C ∧ (openGraph (fun _ => true)).Adj u v

/-- Actual fC membership is precisely connection inside Q to its heart. -/
theorem heartClusterUnion_mem_connection {d : ℕ} (ω : Configuration d)
    (Q heart : Finset (Vertex d)) (hheart : heart ⊆ Q) (x : Vertex d) :
    x ∈ heartClusterUnion ω Q heart ↔
      ω ∈ connectionToSetEvent (Q : Set (Vertex d)) x (heart : Set (Vertex d)) := by
  constructor
  · intro hx
    obtain ⟨y,hy,hxy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxQ,hyx⟩ := (mem_finiteBoxCluster ω Q y x).mp hxy
    exact ⟨hxQ,y,hy,hheart hy,hyx.symm⟩
  · rintro ⟨hxQ,y,hy,_hyQ,hxy⟩
    exact Finset.mem_biUnion.mpr ⟨y,hy,(mem_finiteBoxCluster ω Q y x).mpr ⟨hxQ,hxy.symm⟩⟩

/-- Actual point membership is measurable without a source density premise. -/
theorem measurableSet_heartClusterUnion_member {d : ℕ}
    (Q heart : Finset (Vertex d)) (hheart : heart ⊆ Q) (x : Vertex d) :
    MeasurableSet {ω | x ∈ heartClusterUnion ω Q heart} := by
  have he : {ω : Configuration d | x ∈ heartClusterUnion ω Q heart} =
      connectionToSetEvent (Q : Set (Vertex d)) x (heart : Set (Vertex d)) := by
    ext ω
    exact heartClusterUnion_mem_connection ω Q heart hheart x
  rw [he]
  exact measurableSet_connectionToSetEvent _ _ _

/-- The LAST outside vertex gives a first inside vertex on the inner entry
boundary. Prefix and suffix are disjoint finite open certificates; the suffix
is genuinely confined to C. Nil suffixes are allowed. -/
theorem heartClusterUnion_last_entry_split {d : ℕ} {ω : Configuration d}
    (Q C heart : Finset (Vertex d)) (hCQ : C ⊆ Q) (hheart : heart ⊆ C)
    (x : Vertex d) (hxC : x ∉ C) (hx : x ∈ heartClusterUnion ω Q heart) :
    ∃ v ∈ innerEntryBoundary Q C, DisjointOccurrence
      (connectionToSetEvent (Q : Set (Vertex d)) x {v})
      (connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d))) ω := by
  obtain ⟨hxQ,y,hyH,_hyQ,⟨w⟩⟩ :=
    (heartClusterUnion_mem_connection ω Q heart (hheart.trans hCQ) x).mp hx
  have hle : restrictedGraph ω (Q : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
  let r : (openGraph ω).Walk x y := (w.toPath : (restrictedGraph ω (Q : Set (Vertex d))).Walk x y).mapLe hle
  have hr : r.IsPath := w.toPath.property.mapLe _
  have hrQ : ∀ z ∈ r.support, z ∈ Q := by
    intro z hz
    exact restrictedWalk_support
      (w.toPath : (restrictedGraph ω (Q : Set (Vertex d))).Walk x y) hxQ z
      (by simpa only [r, SimpleGraph.Walk.support_mapLe_eq_support] using hz)
  obtain ⟨u,p,q,hpq,huC,hlast⟩ := walk_last_visit r (fun z => z ∉ C)
    ⟨x,r.start_mem_support,hxC⟩
  have hpQ : ∀ z ∈ p.support, z ∈ Q := by
    intro z hz
    apply hrQ z
    rw [← hpq]
    exact p.support_subset_support_append_left q hz
  cases q with
  | nil => exact (huC (hheart hyH)).elim
  | @cons u v y huv q =>
    have hqC : ∀ z ∈ q.support, z ∈ C := by simpa using hlast
    have hvC : v ∈ C := hqC v q.start_mem_support
    have huQ : u ∈ Q := hpQ u p.end_mem_support
    have hfull : (openGraph (fun _ : Bond d => true)).Adj u v := by
      obtain ⟨e,_he,hends⟩ := huv
      exact ⟨e,rfl,hends⟩
    have hv : v ∈ innerEntryBoundary Q C :=
      Finset.mem_filter.mpr ⟨hvC,u,huQ,huC,hfull⟩
    have happ : (p.concat huv).append q = r := by
      simpa only [SimpleGraph.Walk.concat_append] using hpq
    have hdis : (p.concat huv).edges.Disjoint q.edges :=
      ((SimpleGraph.Walk.isTrail_append (p.concat huv) q).mp (happ.symm ▸ hr.isTrail)).2.2
    have haQ : ∀ z ∈ (p.concat huv).support, z ∈ Q := by
      intro z hz
      apply hrQ z
      rw [← happ]
      exact (p.concat huv).support_subset_support_append_left q hz
    exact ⟨v,hv,disjointOpenWalks_occurrence (p.concat huv) q hdis
      (Q : Set (Vertex d)) (C : Set (Vertex d)) {v} (heart : Set (Vertex d))
      haQ hqC rfl hyH⟩

/-- Actual source heart-membership probability bounded by a finite sum of
outer-prefix times inner-suffix probabilities. No rate or independence premise. -/
theorem heartClusterUnion_probability_le_boundary_products {d : ℕ} (p : unitInterval)
    (Q C heart : Finset (Vertex d)) (hCQ : C ⊆ Q) (hheart : heart ⊆ C)
    (x : Vertex d) (hxC : x ∉ C) :
    (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} ≤
      ∑ v ∈ innerEntryBoundary Q C,
        (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {v}) *
        (percolation d p).real (connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d))) := by
  let E := fun v : Vertex d => {ω : Configuration d | DisjointOccurrence
    (connectionToSetEvent (Q : Set (Vertex d)) x {v})
    (connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d))) ω}
  have hs : {ω : Configuration d | x ∈ heartClusterUnion ω Q heart} ⊆
      ⋃ v ∈ innerEntryBoundary Q C, E v := by
    intro ω hω
    obtain ⟨v,hv,hdis⟩ := heartClusterUnion_last_entry_split Q C heart hCQ hheart x hxC hω
    exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hv,hdis⟩⟩
  calc
    _ ≤ (percolation d p).real (⋃ v ∈ innerEntryBoundary Q C, E v) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ ∑ v ∈ innerEntryBoundary Q C, (percolation d p).real (E v) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _hv
      exact connectionToSet_bk p (Q : Set (Vertex d)) (C : Set (Vertex d)) x v {v} (heart : Set (Vertex d))

/-- Uniform outer and inner connection bounds turn the actual BK sum into a
boundary-cardinality bound. These are connection inputs, not a membership rate. -/
theorem heartClusterUnion_probability_le_entry_card {d : ℕ} (p : unitInterval)
    (Q C heart : Finset (Vertex d)) (hCQ : C ⊆ Q) (hheart : heart ⊆ C)
    (x : Vertex d) (hxC : x ∉ C) {A B : ℝ} (hA : 0 ≤ A)
    (hprefix : ∀ v ∈ innerEntryBoundary Q C,
      (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {v}) ≤ A)
    (hsuffix : ∀ v ∈ innerEntryBoundary Q C,
      (percolation d p).real (connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d))) ≤ B) :
    (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} ≤
      (A*B)*((innerEntryBoundary Q C).card:ℝ) := by
  calc
    _ ≤ ∑ v ∈ innerEntryBoundary Q C,
        (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {v}) *
        (percolation d p).real (connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d))) :=
      heartClusterUnion_probability_le_boundary_products p Q C heart hCQ hheart x hxC
    _ ≤ ∑ _v ∈ innerEntryBoundary Q C, A*B := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul (hprefix v hv) (hsuffix v hv) measureReal_nonneg hA
    _ = _ := by simp [mul_comm]

/-- Source PxinfC upper scaling from the actual BK decomposition: outer
one-sided box n^{1-d}, inner half-space arm (rho*n)^{-3}, and cut-boundary
cardinality (rho*n)^{d-1} give rho^{d-4}n^{-3}. None of those quantitative
connection/geometry estimates is silently asserted here. -/
theorem heartClusterUnion_probability_source_scale {d : ℕ} (p : unitInterval)
    (Q C heart : Finset (Vertex d)) (hCQ : C ⊆ Q) (hheart : heart ⊆ C)
    (x : Vertex d) (hxC : x ∉ C) (n : ℕ) (hn : 1 ≤ n) (hd : 4 ≤ d)
    {ρ Ca Ch Cb : ℝ} (hρ : 0 < ρ) (hCa : 0 ≤ Ca) (hCh : 0 ≤ Ch)
    (hprefix : ∀ v ∈ innerEntryBoundary Q C,
      (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {v}) ≤ Ca/(n:ℝ)^(d-1))
    (hsuffix : ∀ v ∈ innerEntryBoundary Q C,
      (percolation d p).real (connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d))) ≤
        Ch/(ρ*(n:ℝ))^3)
    (hcard : ((innerEntryBoundary Q C).card:ℝ) ≤ Cb*(ρ*(n:ℝ))^(d-1)) :
    (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} ≤
      Ca*Ch*Cb*ρ^(d-4)/(n:ℝ)^3 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 ≤ Ca/(n:ℝ)^(d-1) := by positivity
  have hcoef : 0 ≤ (Ca/(n:ℝ)^(d-1))*(Ch/(ρ*(n:ℝ))^3) := by positivity
  have h := heartClusterUnion_probability_le_entry_card p Q C heart hCQ hheart x hxC hA hprefix hsuffix
  have hpn : (n:ℝ)^(d-1) = (n:ℝ)^(d-4)*(n:ℝ)^3 := by
    rw [← pow_add]
    congr 1
    omega
  have hpr : ρ^(d-1) = ρ^(d-4)*ρ^3 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ ((Ca/(n:ℝ)^(d-1))*(Ch/(ρ*(n:ℝ))^3))*(Cb*(ρ*(n:ℝ))^(d-1)) :=
      h.trans (mul_le_mul_of_nonneg_left hcard hcoef)
    _ = _ := by
      simp only [mul_pow]
      simp_rw [hpn,hpr]
      field_simp [ne_of_gt hnR,ne_of_gt hρ]

end NearCritical
