module

public import NearCritical.Section10LatticeRuleBuild
public import NearCritical.Section10StepGeometry

/-! Small deterministic facts used by the lattice path certificate.

* `routeLab_next_site`: the site of the next step is the target of the current
  one; kinds of the steps (`start`, steps, `exit`).
* regular patches lie in the face boundary of their cluster;
* typical clusters lie in their cube.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem routeLab_next_site {D : ℕ} {M : ℕ} (X : ℕ → Fin D → ℤ) {t : ℕ} (ht : t + 1 < 2 * M) :
    (routeLab M X (t+1)).site = (routeLab M X t).target := by
  by_cases h0 : t = 0
  · subst h0
    have hz : routeLab M X 0 = RouteLabel.start (0, X 0) := by
      unfold routeLab
      rw [if_pos rfl]
    rw [hz]
    unfold routeLab
    rw [if_neg (by omega : ¬ 0 + 1 = 0), if_neg (by omega : ¬ 2 * M ≤ 0 + 1)]
    by_cases hlast : 0 + 1 = 2 * M - 1
    · rw [if_pos hlast]
      simp only [RouteLabel.site, RouteLabel.target]
      have h1 : M - 1 = 0 := by omega
      rw [h1]
    · rw [if_neg hlast, if_pos (by norm_num : (0 + 1) % 2 = 1)]
      simp only [RouteLabel.site, RouteLabel.target]
  · unfold routeLab
    rw [if_neg h0, if_neg (by omega : ¬ 2 * M ≤ t), if_neg (by omega : ¬ t = 2 * M - 1)]
    rw [if_neg (by omega : ¬ t + 1 = 0), if_neg (by omega : ¬ 2 * M ≤ t + 1)]
    by_cases hodd : t % 2 = 1
    · rw [if_pos hodd, if_neg (by omega : ¬ t + 1 = 2 * M - 1),
        if_neg (by omega : ¬ (t + 1) % 2 = 1)]
      simp only [RouteLabel.site, RouteLabel.target]
      have h1 : (t + 1) / 2 = (t - 1) / 2 + 1 := by omega
      have h2 : (t + 1) / 2 - 1 = (t - 1) / 2 := by omega
      rw [h2, h1]
    · rw [if_neg hodd]
      by_cases hlast : t + 1 = 2 * M - 1
      · rw [if_pos hlast]
        simp only [RouteLabel.site, RouteLabel.target]
        have h1 : M - 1 = t / 2 := by omega
        rw [h1]
      · rw [if_neg hlast, if_pos (by omega : (t + 1) % 2 = 1)]
        simp only [RouteLabel.site, RouteLabel.target]
        have h1 : (t + 1 - 1) / 2 = t / 2 := by omega
        rw [h1]

theorem routeLab_isStep {D : ℕ} {M : ℕ} (X : ℕ → Fin D → ℤ) {t : ℕ} (h1 : 1 ≤ t)
    (h2 : t < 2 * M - 1) : (routeLab M X t).isStep := by
  unfold routeLab
  rw [if_neg (by omega : ¬ t = 0), if_neg (by omega : ¬ 2 * M ≤ t),
    if_neg (by omega : ¬ t = 2 * M - 1)]
  split_ifs <;> trivial

theorem routeLab_zero {D : ℕ} (M : ℕ) (X : ℕ → Fin D → ℤ) :
    routeLab M X 0 = RouteLabel.start (0, X 0) := by
  unfold routeLab
  rw [if_pos rfl]

theorem routeLab_last {D : ℕ} {M : ℕ} (hM : 1 ≤ M) (X : ℕ → Fin D → ℤ) :
    routeLab M X (2 * M - 1) = RouteLabel.exit (M - 1, X (M - 1)) := by
  unfold routeLab
  rw [if_neg (by omega : ¬ 2 * M - 1 = 0), if_neg (by omega : ¬ 2 * M ≤ 2 * M - 1), if_pos rfl]

lemma typicalRegularPatch_subset_faceBoundary {d : ℕ} (a : TypicalParameters) (t : ℕ)
    (c : Vertex d) (ω : Configuration d) (C : Finset (Vertex d)) (face : Fin d × Bool)
    (plus : Bool) :
    typicalRegularPatch a t c ω C face plus ⊆ clusterFaceBoundary C (typicalFace t c) := by
  intro x hx
  unfold typicalRegularPatch at hx
  have h1 := (Finset.mem_filter.mp hx).1
  have h2 := Finset.mem_inter.mp h1
  unfold typicalSplitFace at h2
  have h3 := (Finset.mem_filter.mp h2.2).1
  unfold clusterFaceBoundary
  exact Finset.mem_biUnion.mpr ⟨face, Finset.mem_univ _, Finset.mem_inter.mpr ⟨h2.1, h3⟩⟩

lemma typicalRegularPatch_subset_splitFace {d : ℕ} (a : TypicalParameters) (t : ℕ)
    (c : Vertex d) (ω : Configuration d) (C : Finset (Vertex d)) (face : Fin d × Bool)
    (plus : Bool) :
    typicalRegularPatch a t c ω C face plus ⊆ typicalSplitFace t c face plus := by
  intro x hx
  unfold typicalRegularPatch at hx
  exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2

lemma typicalCluster_subset_cube {d : ℕ} (a : TypicalParameters) (t : ℕ) (c : Vertex d)
    (ω : Configuration d) {C : Finset (Vertex d)} (hC : C ∈ typicalClusterFamily a t c ω) :
    C ⊆ typicalCube t c := by
  obtain ⟨x, _, rfl⟩ := (mem_finiteClusterFamily ω (typicalCube t c) C).mp
    ((mem_typicalClusterFamily a t c ω C).mp hC).1
  exact finiteBoxCluster_subset ω (typicalCube t c) x

end NearCritical.Section10
