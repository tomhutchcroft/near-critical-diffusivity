module

public import NearCritical.FiniteClusterFamily

/-! Source nest labels are actual distinct component vertex sets. Canonical
root recovery instantiates the existing actual-component trace; no duplicate
root indexing is used to count or choose clusters. -/
@[expose] public section
noncomputable section
namespace NearCritical

structure ComponentLabelNestData (d : ℕ) (φ : Type*) [Fintype φ] [DecidableEq φ]
    (ω : Configuration d) (D : Set (Vertex d)) (K B : ℝ) (n : ℕ) where
  critical : Configuration d
  critical_le : ∀ e, critical e = true → ω e = true
  cube : ℕ → Finset (Vertex d)
  cube_subset : ∀ t, t ≤ n → (cube t : Set (Vertex d)) ⊆ D
  faces : ℕ → φ → Finset (Vertex d)
  nest : ℕ → Finset (Finset (Vertex d))
  initial_nest_actual : nest 0 ⊆ finiteClusterFamily critical (cube 0)
  representative : ℕ → Finset (Vertex d)
  representative_mem : ∀ t, t ≤ n → representative t ∈ nest t
  spanning : ∀ t, t ≤ n → ∀ i, (representative t ∩ faces t i).Nonempty
  face_diameter : ∀ t, t ≤ n →
    (spanningFaceDiameter (restrictedGraph critical (cube t : Set (Vertex d)))
      (representative t) (faces t) : ℝ) ≤ K
  step : ∀ t, t < n → NestSprinklingStep d (Finset (Vertex d)) ω D B
  critical_sides : ∀ t (ht : t < n),
    (step t ht).leftGraph ≤ openGraph critical ∧ (step t ht).rightGraph ≤ openGraph critical
  source_on_face : ∀ t (ht : t < n), ∀ x ∈ (step t ht).sourceBoundary,
    ∃ i, x ∈ representative t ∩ faces t i
  target_on_face : ∀ t (ht : t < n), ∀ C, ∀ y ∈ (step t ht).targetBoundary C,
    C ∈ finiteClusterFamily critical (cube (t+1)) ∧ ∃ i, y ∈ C ∩ faces (t+1) i
  next_nest_offspring : ∀ t (ht : t < n), nest (t+1) ⊆ (step t ht).offspring

namespace ComponentLabelNestData

/-- Computed offspring labels are genuine next-cube components: membership
supplies a nonempty target boundary, which carries its actual-component certificate. -/
lemma offspring_actual {d : ℕ} {φ : Type*} [Fintype φ] [DecidableEq φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ComponentLabelNestData d φ ω D K B n) {t : ℕ} (ht : t < n) :
    (dat.step t ht).offspring ⊆ finiteClusterFamily dat.critical (dat.cube (t+1)) := by
  intro C hc
  let s := dat.step t ht
  obtain ⟨_, x, _, y, hy, _⟩ := (mem_sprinklingOffspring s.leftGraph s.rightGraph
    s.sourceBoundary s.candidates s.targetBoundary s.pivots C).mp hc
  exact (dat.target_on_face t ht C y hy).1

/-- Only initial nest validity is supplied. Every later nest is proved actual
from its containment in computed offspring, rather than assumed valid again. -/
lemma nest_actual {d : ℕ} {φ : Type*} [Fintype φ] [DecidableEq φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ComponentLabelNestData d φ ω D K B n) {t : ℕ} (ht : t ≤ n) :
    dat.nest t ⊆ finiteClusterFamily dat.critical (dat.cube t) := by
  cases t with
  | zero => exact dat.initial_nest_actual
  | succ t => exact (dat.next_nest_offspring t (by omega)).trans (dat.offspring_actual (by omega))

lemma representative_actual {d : ℕ} {φ : Type*} [Fintype φ] [DecidableEq φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ComponentLabelNestData d φ ω D K B n) {t : ℕ} (ht : t ≤ n) :
    dat.representative t ∈ finiteClusterFamily dat.critical (dat.cube t) :=
  dat.nest_actual ht (dat.representative_mem t ht)

lemma representative_recovered {d : ℕ} {φ : Type*} [Fintype φ] [DecidableEq φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ComponentLabelNestData d φ ω D K B n) {t : ℕ} (ht : t ≤ n) :
    finiteBoxCluster dat.critical (dat.cube t) (finiteClusterRoot (dat.representative t)) =
      dat.representative t :=
  finiteClusterRoot_recovers _ _ (dat.representative_actual ht)

/-- Exact component-label instantiation. The selected site's graph is the
critical graph induced on that actual component, not a separately supplied set. -/
def toActualData {d : ℕ} {φ : Type*} [Fintype φ] [DecidableEq φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ComponentLabelNestData d φ ω D K B n) :
    ActualClusterNestData d (Finset (Vertex d)) φ ω D K B n where
  critical := dat.critical
  critical_le := dat.critical_le
  cube := dat.cube
  cube_subset := dat.cube_subset
  root := fun _ C => finiteClusterRoot C
  faces := dat.faces
  nest := dat.nest
  representative := dat.representative
  representative_mem := dat.representative_mem
  spanning := by
    intro t ht i
    rw [dat.representative_recovered ht]
    exact dat.spanning t ht i
  face_diameter := by
    intro t ht
    rw [dat.representative_recovered ht]
    exact dat.face_diameter t ht
  step := dat.step
  critical_sides := dat.critical_sides
  source_on_face := by
    intro t ht x hx
    rw [dat.representative_recovered (by omega)]
    exact dat.source_on_face t ht x hx
  target_on_face := by
    intro t ht C y hy
    obtain ⟨hC, i, hi⟩ := dat.target_on_face t ht C y hy
    refine ⟨i, ?_⟩
    rwa [finiteClusterRoot_recovers dat.critical (dat.cube (t+1)) hC]
  next_nest_offspring := dat.next_nest_offspring

/-- Canonical roots recover the actual label exactly at every selected stage. -/
lemma toActualData_component {d : ℕ} {φ : Type*} [Fintype φ] [DecidableEq φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ComponentLabelNestData d φ ω D K B n) {t : ℕ} (ht : t ≤ n) :
    dat.toActualData.component t (dat.representative t) = dat.representative t :=
  dat.representative_recovered ht

/-- Confined path from source component labels; metric/site fields are derived. -/
theorem exists_path_with_exit {d : ℕ} {φ : Type*}
    [Fintype φ] [DecidableEq φ] [Nontrivial φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ComponentLabelNestData d φ ω D K B n) {x y z : Vertex d}
    (hx : x ∈ clusterFaceBoundary (dat.representative 0) (dat.faces 0))
    (hy : y ∈ clusterFaceBoundary (dat.representative n) (dat.faces n))
    (hexit : (openGraph ω).Adj y z) (hz : z ∈ D) :
    ∃ p : (restrictedGraph ω D).Walk x z, p.IsPath ∧
      (p.length : ℝ) ≤ ((n:ℝ)+1)*(2*K)+(n:ℝ)*B+1 := by
  apply dat.toActualData.exists_path_with_exit ?_ ?_ hexit hz
  · change x ∈ clusterFaceBoundary (dat.toActualData.component 0 (dat.representative 0)) _
    rwa [dat.toActualData_component (by omega)]
  · change y ∈ clusterFaceBoundary (dat.toActualData.component n (dat.representative n)) _
    rwa [dat.toActualData_component (by omega)]

/-- Literal source-scale crossing with genuine component labels. All site/metric
fields and the final length budget are derived through the existing consumers. -/
theorem crossing_with_source_length {d R : ℕ} {φ : Type*}
    [Fintype φ] [DecidableEq φ] [Nontrivial φ] (a : Vertex d) (i : Fin d)
    {ω : Configuration d} {Kspn Kskl : ℝ} {n M ell0 s n0 ellStar : ℕ}
    (dat : ComponentLabelNestData d φ ω
      (translateSites a (chemicalCrossingSupport d R i) : Set (Vertex d))
      (Kspn*(ell0:ℝ)^2) (Kskl*(ell0:ℝ)^2) n)
    (hspn : 0≤Kspn) (hskl : 0≤Kskl)
    (hbottom : ∃ x ∈ chemicalBottomFace d R i,
      a+x ∈ clusterFaceBoundary (dat.representative 0) (dat.faces 0))
    (hexit : ∃ y ∈ clusterFaceBoundary (dat.representative n) (dat.faces n),
      ∃ z ∈ chemicalExitFace d R i, (openGraph ω).Adj y (a+z))
    (hn : n+1≤2*M) (hM : 2≤M) (hscale : ell0=n0*ellStar)
    (hstar : 1≤ellStar) (hs : 1≤s) (hside : (M-1)*ell0+s=2*R+1) :
    ω ∈ chemicalBoxCrossingEvent a R i
      ((4*(2*Kspn+Kskl)*(n0:ℝ)+1)*(ellStar:ℝ)) := by
  apply dat.toActualData.crossing_with_source_length a i hspn hskl ?_ ?_
    hn hM hscale hstar hs hside
  · obtain ⟨x, hx, hxsite⟩ := hbottom
    refine ⟨x, hx, ?_⟩
    change a+x ∈ clusterFaceBoundary (dat.toActualData.component 0 (dat.representative 0)) _
    rwa [dat.toActualData_component (by omega)]
  · obtain ⟨y, hysite, z, hz, hopen⟩ := hexit
    refine ⟨y, ?_, z, hz, hopen⟩
    change y ∈ clusterFaceBoundary (dat.toActualData.component n (dat.representative n)) _
    rwa [dat.toActualData_component (by omega)]

end ComponentLabelNestData
end NearCritical
