module
public import NearCritical.Section9PivotalSupport
public import NearCritical.Section9PivotalCount
public import NearCritical.FiniteClusterMetric
public import NearCritical.ConnectionToSet
public import NearCritical.Section9AvoidanceCertificate

/-! Step 1 of the proof of lem.box_twopoint_lower (main.tex 6667-6675,
eq.lower_step1), for the ACTUAL cluster `C` of `x` in a finite box `Q ⊆ T`.

For a face set `F'`, the source events
`A(w) = {w ↔ y in T off EDGE(C)} \ ⋃_{w' ∈ (C ∩ F') \ {w}} {w ↔ w' off EDGE(C)}`
are `section9AvoidanceEvent T T Q C {y} ((C ∩ F') \ {w}) w`. EDGE(C) is
`exploredEdgeSet Q C`, and the matching bond mask is `clusterRevealBonds Q C`. We prove:
* each `A(w)` depends only on `sprinklingAvailableBonds T Q C`, which is disjoint from
  the reveal mask, so `P[cluster = C ∩ A] = P[cluster = C] P[A]` (exact product-law
  independence; no conditional-law object is introduced);
* the `A(w)`, `w ∈ C ∩ F'`, are pairwise disjoint;
* `{cluster = C} ∩ A(w) ⊆ {x ↔_T y}`.
Summing over the finitely many `C ⊆ Q` gives
`Σ_C P[cluster = C] Σ_{w ∈ C ∩ F'} P[A_C(w)] ≤ P[x ↔_T y]`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Exact independence of the actual finite-box cluster event from any measurable
event determined by bonds outside its reveal mask. -/
theorem appendix_clusterReveal_fresh_event {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (T : Finset (Bond d)) (hd : Disjoint (clusterRevealBonds U C) T)
    (A : Set (Configuration d)) (hA : MeasurableSet A)
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ T, ω b = θ b) → (ω ∈ A ↔ θ ∈ A)) :
    (percolation d p).real ({ω | finiteBoxCluster ω U root = C} ∩ A) =
      (percolation d p).real {ω | finiteBoxCluster ω U root = C} *
        (percolation d p).real A := by
  have hE : MeasurableSet {ω : Configuration d | finiteBoxCluster ω U root = C} :=
    measurableSet_clusterReveal_event U C root hroot
  let g : (T → Bool) → ℝ := fun ξ =>
    A.indicator (fun _ => (1 : ℝ)) (extendConfiguration T (fun _ => false) ξ)
  have hg (ω : Configuration d) :
      g (T.restrict ω) = A.indicator (fun _ => (1 : ℝ)) ω := by
    have hEq := hlocal ω (extendConfiguration T (fun _ => false) (T.restrict ω)) (by
      intro b hb
      simp [extendConfiguration, hb, Finset.restrict])
    simp only [g, Set.indicator_apply, ← hEq]
  have h := clusterReveal_fresh_factorization p U C root hroot T hd (fun _ => (1 : ℝ)) g
  have hi (S : Set (Configuration d)) (hS : MeasurableSet S) :
      (∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂percolation d p) = (percolation d p).real S :=
    integral_indicator_one hS
  calc (percolation d p).real ({ω | finiteBoxCluster ω U root = C} ∩ A)
      = ∫ ω, ({ω : Configuration d | finiteBoxCluster ω U root = C} ∩ A).indicator
          (fun _ => (1 : ℝ)) ω ∂percolation d p := (hi _ (hE.inter hA)).symm
    _ = ∫ ω, ({η : Configuration d | finiteBoxCluster η U root = C}).indicator
          (fun _ => (1 : ℝ)) ω * g (T.restrict ω) ∂percolation d p := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [hg ω]
        by_cases h1 : finiteBoxCluster ω U root = C <;> by_cases h2 : ω ∈ A <;>
          simp [Set.indicator_apply, h1, h2]
    _ = (∫ ω, ({η : Configuration d | finiteBoxCluster η U root = C}).indicator
          (fun _ => (1 : ℝ)) ω ∂percolation d p) *
          (∫ ω, g (T.restrict ω) ∂percolation d p) := h
    _ = _ := by
        rw [hi _ hE]
        congr 1
        simp_rw [hg]
        exact hi _ hA

/-- Source A(w) of main.tex 6667: `w` reaches `y` in `T` off EDGE(C), and does not
reach any OTHER point of the face part `W` of the cluster off EDGE(C). -/
def appendixBoxAvoidEvent {d : ℕ} (T Q C W : Finset (Vertex d)) (y w : Vertex d) :
    Set (Configuration d) :=
  section9AvoidanceEvent T T Q C {y} (W \ {w}) w

theorem measurableSet_appendixBoxAvoidEvent {d : ℕ} (T Q C W : Finset (Vertex d))
    (y w : Vertex d) : MeasurableSet (appendixBoxAvoidEvent T Q C W y w) :=
  (measurableSet_sprinklingUnexploredCluster_hits T Q C {y} w).inter
    (measurableSet_sprinklingUnexploredCluster_hits T Q C (W \ {w}) w).compl

/-- A(w) is determined by the bonds of `T` outside the reveal mask of `C`. -/
theorem appendixBoxAvoidEvent_local {d : ℕ} (T Q C W : Finset (Vertex d)) (y w : Vertex d)
    (ω θ : Configuration d) (hagree : ∀ b ∈ sprinklingAvailableBonds T Q C, ω b = θ b) :
    ω ∈ appendixBoxAvoidEvent T Q C W y w ↔ θ ∈ appendixBoxAvoidEvent T Q C W y w := by
  unfold appendixBoxAvoidEvent section9AvoidanceEvent
  simp only [Set.mem_setOf_eq]
  rw [sprinklingUnexploredCluster_eq_of_available_agree T Q C ω θ hagree w]

/-- Distinct face points give disjoint source events (main.tex 6670). -/
theorem appendixBoxAvoidEvent_disjoint {d : ℕ} (T Q C W : Finset (Vertex d)) (y : Vertex d)
    (hWT : W ⊆ T) {w w' : Vertex d} (hw' : w' ∈ W) (hne : w ≠ w') :
    Disjoint (appendixBoxAvoidEvent T Q C W y w) (appendixBoxAvoidEvent T Q C W y w') := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  simp only [appendixBoxAvoidEvent, section9AvoidanceEvent, Set.mem_setOf_eq] at h1 h2
  obtain ⟨⟨u,hu⟩,hno⟩ := h1
  obtain ⟨⟨u',hu'⟩,_⟩ := h2
  obtain ⟨huC,huy⟩ := Finset.mem_inter.mp hu
  obtain ⟨hu'C,hu'y⟩ := Finset.mem_inter.mp hu'
  have hu1 : u = y := Finset.mem_singleton.mp huy
  have hu2 : u' = y := Finset.mem_singleton.mp hu'y
  rw [hu1] at huC
  rw [hu2] at hu'C
  obtain ⟨_,hwy⟩ := (mem_sprinklingUnexploredCluster ω T Q C w y).mp huC
  obtain ⟨_,hw'y⟩ := (mem_sprinklingUnexploredCluster ω T Q C w' y).mp hu'C
  apply hno
  refine ⟨w',Finset.mem_inter.mpr ⟨(mem_sprinklingUnexploredCluster ω T Q C w w').mpr
    ⟨hWT hw',hwy.trans hw'y.symm⟩,?_⟩⟩
  exact Finset.mem_sdiff.mpr ⟨hw',fun h => hne (Finset.mem_singleton.mp h).symm⟩

/-- eq.lower_step1 for one cluster value `C ⊆ Q`, in unconditioned product form. -/
theorem appendix_box_cluster_avoid_lower {d : ℕ} (p : unitInterval)
    (T Q F' C : Finset (Vertex d)) (x y : Vertex d) (hQT : Q ⊆ T) (hx : x ∈ Q)
    (hCQ : C ⊆ Q) :
    (percolation d p).real {ω | finiteBoxCluster ω Q x = C} *
      ∑ w ∈ C ∩ F', (percolation d p).real (appendixBoxAvoidEvent T Q C (C ∩ F') y w) ≤
    (percolation d p).real ({ω | finiteBoxCluster ω Q x = C} ∩
      connectionToSetEvent (T : Set (Vertex d)) x {y}) := by
  have hWT : C ∩ F' ⊆ T := fun v hv => hQT (hCQ (Finset.mem_inter.mp hv).1)
  let A : Set (Configuration d) := ⋃ w ∈ C ∩ F', appendixBoxAvoidEvent T Q C (C ∩ F') y w
  have hAm : MeasurableSet A :=
    Finset.measurableSet_biUnion _ (fun w _ => measurableSet_appendixBoxAvoidEvent _ _ _ _ _ _)
  have hlocA : ∀ ω θ : Configuration d,
      (∀ b ∈ sprinklingAvailableBonds T Q C, ω b = θ b) → (ω ∈ A ↔ θ ∈ A) := by
    intro ω θ h
    simp only [A, Set.mem_iUnion]
    exact exists_congr fun w => exists_congr fun _ =>
      appendixBoxAvoidEvent_local T Q C (C ∩ F') y w ω θ h
  have hdis : Disjoint (clusterRevealBonds Q C) (sprinklingAvailableBonds T Q C) :=
    Finset.disjoint_right.mpr (fun b hb => (Finset.mem_sdiff.mp hb).2)
  have hfac := appendix_clusterReveal_fresh_event p Q C x hx _ hdis A hAm hlocA
  have hpd : Set.PairwiseDisjoint (↑(C ∩ F') : Set (Vertex d))
      (fun w => appendixBoxAvoidEvent T Q C (C ∩ F') y w) := by
    intro w _ w' hw' hne
    exact appendixBoxAvoidEvent_disjoint T Q C (C ∩ F') y hWT hw' hne
  have hmeas : ∀ w ∈ C ∩ F', MeasurableSet (appendixBoxAvoidEvent T Q C (C ∩ F') y w) :=
    fun w _ => measurableSet_appendixBoxAvoidEvent _ _ _ _ _ _
  have hsum : (percolation d p).real A =
      ∑ w ∈ C ∩ F', (percolation d p).real (appendixBoxAvoidEvent T Q C (C ∩ F') y w) :=
    measureReal_biUnion_finset hpd hmeas (fun _ _ => measure_ne_top _ _)
  have hsub : {ω | finiteBoxCluster ω Q x = C} ∩ A ⊆
      {ω | finiteBoxCluster ω Q x = C} ∩ connectionToSetEvent (T : Set (Vertex d)) x {y} := by
    rintro ω ⟨hcl,hA⟩
    refine ⟨hcl,?_⟩
    have hcl' : finiteBoxCluster ω Q x = C := hcl
    simp only [A, Set.mem_iUnion] at hA
    obtain ⟨w,hwW,hAw⟩ := hA
    simp only [appendixBoxAvoidEvent, section9AvoidanceEvent, Set.mem_setOf_eq] at hAw
    obtain ⟨⟨u,hu⟩,_⟩ := hAw
    obtain ⟨huC,huy⟩ := Finset.mem_inter.mp hu
    rw [Finset.mem_singleton.mp huy] at huC
    obtain ⟨hyT,hwy⟩ := (mem_sprinklingUnexploredCluster ω T Q C w y).mp huC
    have hwC : w ∈ finiteBoxCluster ω Q x := by rw [hcl']; exact (Finset.mem_inter.mp hwW).1
    obtain ⟨_,hxw⟩ := (mem_finiteBoxCluster ω Q x w).mp hwC
    have hQT' : (Q : Set (Vertex d)) ⊆ (T : Set (Vertex d)) := Finset.coe_subset.mpr hQT
    have hle' : sprinklingUnexploredGraph ω T Q C ≤ restrictedGraph ω (T : Set (Vertex d)) :=
      fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩
    exact ⟨hQT hx,y,Set.mem_singleton y,hyT,
      (hxw.mono (restrictedGraph_mono ω hQT')).trans (hwy.mono hle')⟩
  calc (percolation d p).real {ω | finiteBoxCluster ω Q x = C} *
        ∑ w ∈ C ∩ F', (percolation d p).real (appendixBoxAvoidEvent T Q C (C ∩ F') y w)
      = (percolation d p).real {ω | finiteBoxCluster ω Q x = C} *
          (percolation d p).real A := by rw [hsum]
    _ = (percolation d p).real ({ω | finiteBoxCluster ω Q x = C} ∩ A) := hfac.symm
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

/-- eq.lower_step1 summed over every possible cluster: the actual restricted
connection probability dominates the cluster-weighted source sum. -/
theorem appendix_box_cluster_sum_lower {d : ℕ} (p : unitInterval)
    (T Q F' : Finset (Vertex d)) (x y : Vertex d) (hQT : Q ⊆ T) (hx : x ∈ Q) :
    ∑ C ∈ Q.powerset, (percolation d p).real {ω | finiteBoxCluster ω Q x = C} *
      ∑ w ∈ C ∩ F', (percolation d p).real (appendixBoxAvoidEvent T Q C (C ∩ F') y w) ≤
    (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) x {y}) := by
  calc _ ≤ ∑ C ∈ Q.powerset, (percolation d p).real ({ω | finiteBoxCluster ω Q x = C} ∩
          connectionToSetEvent (T : Set (Vertex d)) x {y}) :=
        Finset.sum_le_sum fun C hC =>
          appendix_box_cluster_avoid_lower p T Q F' C x y hQT hx (Finset.mem_powerset.mp hC)
    _ = (percolation d p).real (⋃ C ∈ Q.powerset, ({ω | finiteBoxCluster ω Q x = C} ∩
          connectionToSetEvent (T : Set (Vertex d)) x {y})) := by
        have hpd : Set.PairwiseDisjoint (↑Q.powerset : Set (Finset (Vertex d)))
            (fun C => {ω : Configuration d | finiteBoxCluster ω Q x = C} ∩
              connectionToSetEvent (T : Set (Vertex d)) x {y}) := by
          intro C _ C' _ hne
          refine Set.disjoint_left.mpr fun ω h1 h2 => hne ?_
          have e1 : finiteBoxCluster ω Q x = C := h1.1
          have e2 : finiteBoxCluster ω Q x = C' := h2.1
          exact e1.symm.trans e2
        have hmeas : ∀ C ∈ Q.powerset, MeasurableSet
            ({ω : Configuration d | finiteBoxCluster ω Q x = C} ∩
              connectionToSetEvent (T : Set (Vertex d)) x {y}) :=
          fun C _ => (measurableSet_clusterReveal_event Q C x hx).inter
            (measurableSet_connectionToSetEvent _ _ _)
        exact (measureReal_biUnion_finset hpd hmeas (fun _ _ => measure_ne_top _ _)).symm
    _ ≤ _ := measureReal_mono (Set.iUnion₂_subset fun C _ => Set.inter_subset_right)
        (measure_ne_top _ _)

end NearCritical
