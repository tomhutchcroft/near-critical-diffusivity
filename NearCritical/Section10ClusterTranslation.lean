module

public import NearCritical.Section10StepTranslation
public import NearCritical.Section10TypicalClusters

/-! Translation covariance of finite clusters and of the typical-cube geometry.

With `ω' = translateConfiguration a ω`:
* `finiteBoxCluster_translate`, `heartClusterUnion_translate`,
  `finiteClusterFamily_translate`: clusters in a translated box are translates of
  clusters of `ω'`;
* `typicalCube_translate` and the same for the heart, inner cube, faces, split
  faces and boundary: the geometry at `a + z` is the translate of the geometry
  at `z`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
open MeasureTheory

theorem restrictedGraph_translate_adj {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (S : Finset (Vertex d)) (x y : Vertex d) :
    (restrictedGraph (translateConfiguration a ω) (S : Set (Vertex d))).Adj x y ↔
      (restrictedGraph ω (translateSites a S : Set (Vertex d))).Adj (a + x) (a + y) := by
  show ((openGraph (translateConfiguration a ω)).Adj x y ∧ x ∈ (S : Set (Vertex d)) ∧
      y ∈ (S : Set (Vertex d))) ↔
    ((openGraph ω).Adj (a + x) (a + y) ∧ a + x ∈ (translateSites a S : Set (Vertex d)) ∧
      a + y ∈ (translateSites a S : Set (Vertex d)))
  simp only [Finset.mem_coe, mem_translateSites, openGraph_translate_adj]

/-- The graph isomorphism of restricted graphs. -/
def restrictedTranslateIso {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (S : Finset (Vertex d)) :
    restrictedGraph (translateConfiguration a ω) (S : Set (Vertex d)) ≃g
      restrictedGraph ω (translateSites a S : Set (Vertex d)) where
  toEquiv := Equiv.addLeft a
  map_rel_iff' := (restrictedGraph_translate_adj a ω S _ _).symm

theorem finiteBoxCluster_translate {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (U : Finset (Vertex d)) (root : Vertex d) :
    finiteBoxCluster ω (translateSites a U) (a + root) =
      translateSites a (finiteBoxCluster (translateConfiguration a ω) U root) := by
  ext x
  rw [mem_finiteBoxCluster]
  constructor
  · rintro ⟨hxU, hreach⟩
    obtain ⟨y, hy, rfl⟩ := (mem_translateSites_iff a U x).mp hxU
    refine (mem_translateSites a _ y).mpr ((mem_finiteBoxCluster _ _ _ _).mpr ⟨hy, ?_⟩)
    exact ((restrictedTranslateIso a ω U).reachable_iff (u := root) (v := y)).mp hreach
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (mem_translateSites_iff a _ x).mp hx
    obtain ⟨hyU, hreach⟩ := (mem_finiteBoxCluster _ _ _ _).mp hy
    exact ⟨(mem_translateSites a U y).mpr hyU,
      ((restrictedTranslateIso a ω U).reachable_iff (u := root) (v := y)).mpr hreach⟩

theorem heartClusterUnion_translate {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (Q H : Finset (Vertex d)) :
    heartClusterUnion ω (translateSites a Q) (translateSites a H) =
      translateSites a (heartClusterUnion (translateConfiguration a ω) Q H) := by
  ext x
  unfold heartClusterUnion
  rw [mem_translateSites_iff]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hr, hx⟩
    obtain ⟨r0, hr0, rfl⟩ := (mem_translateSites_iff a H r).mp hr
    rw [finiteBoxCluster_translate] at hx
    obtain ⟨y, hy, rfl⟩ := (mem_translateSites_iff a _ x).mp hx
    exact ⟨y, ⟨r0, hr0, hy⟩, rfl⟩
  · rintro ⟨y, ⟨r0, hr0, hy⟩, rfl⟩
    refine ⟨a + r0, (mem_translateSites a H r0).mpr hr0, ?_⟩
    rw [finiteBoxCluster_translate]
    exact (mem_translateSites a _ y).mpr hy

theorem finiteClusterFamily_translate {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (U : Finset (Vertex d)) :
    finiteClusterFamily ω (translateSites a U) =
      (finiteClusterFamily (translateConfiguration a ω) U).image (translateSites a) := by
  ext C
  rw [mem_finiteClusterFamily, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (mem_translateSites_iff a U x).mp hx
    exact ⟨finiteBoxCluster (translateConfiguration a ω) U x0,
      (mem_finiteClusterFamily _ _ _).mpr ⟨x0, hx0, rfl⟩, (finiteBoxCluster_translate a ω U x0).symm⟩
  · rintro ⟨C0, hC0, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (mem_finiteClusterFamily _ _ _).mp hC0
    exact ⟨a + x0, (mem_translateSites a U x0).mpr hx0, finiteBoxCluster_translate a ω U x0⟩

lemma translateSites_filter {d : ℕ} (a : Vertex d) (U : Finset (Vertex d))
    (P P' : Vertex d → Prop) [DecidablePred P] [DecidablePred P']
    (h : ∀ x, P' (a + x) ↔ P x) :
    (translateSites a U).filter P' = translateSites a (U.filter P) := by
  ext x
  rw [Finset.mem_filter, mem_translateSites_iff, mem_translateSites_iff]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hP⟩
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, (h y).mp hP⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, (Finset.mem_filter.mp hy).1, rfl⟩, (h y).mpr (Finset.mem_filter.mp hy).2⟩

lemma translateSites_add {d : ℕ} (a z : Vertex d) (U : Finset (Vertex d)) :
    translateSites (a + z) U = translateSites a (translateSites z U) := by
  unfold translateSites
  rw [Finset.image_image]
  refine Finset.image_congr (fun x _ => ?_)
  show a + z + x = a + (z + x)
  rw [add_assoc]

lemma coord_sub_translate {d : ℕ} (a z x : Vertex d) (j : Fin d) :
    (a + x) j - (a + z) j = x j - z j := by
  simp only [Pi.add_apply]
  ring

theorem typicalCube_translate {d : ℕ} (t : ℕ) (a z : Vertex d) :
    typicalCube t (a + z) = translateSites a (typicalCube t z) := by
  unfold typicalCube
  rw [translateSites_add]
  refine translateSites_filter a _ _ _ ?_
  intro x
  simp only [coord_sub_translate]

theorem typicalInnerCube_translate {d : ℕ} (t : ℕ) (a z : Vertex d) :
    typicalInnerCube t (a + z) = translateSites a (typicalInnerCube t z) := by
  unfold typicalInnerCube
  rw [typicalCube_translate]
  refine translateSites_filter a _ _ _ ?_
  intro x
  simp only [coord_sub_translate]

theorem typicalHeart_translate {d : ℕ} (t : ℕ) (a z : Vertex d) (cc : ℝ) :
    typicalHeart t (a + z) cc = translateSites a (typicalHeart t z cc) := by
  unfold typicalHeart
  rw [typicalCube_translate]
  refine translateSites_filter a _ _ _ ?_
  intro x
  simp only [coord_sub_translate]

theorem typicalFace_translate {d : ℕ} (t : ℕ) (a z : Vertex d) (face : Fin d × Bool) :
    typicalFace t (a + z) face = translateSites a (typicalFace t z face) := by
  unfold typicalFace
  rw [typicalCube_translate]
  refine translateSites_filter a _ _ _ ?_
  intro x
  simp only [coord_sub_translate]

theorem typicalSplitFace_translate {d : ℕ} (t : ℕ) (a z : Vertex d) (face : Fin d × Bool)
    (plus : Bool) :
    typicalSplitFace t (a + z) face plus = translateSites a (typicalSplitFace t z face plus) := by
  unfold typicalSplitFace
  rw [typicalFace_translate]
  refine translateSites_filter a _ _ _ ?_
  intro x
  simp only [coord_sub_translate]

theorem typicalBoundary_translate {d : ℕ} (t : ℕ) (a z : Vertex d) :
    typicalBoundary t (a + z) = translateSites a (typicalBoundary t z) := by
  unfold typicalBoundary
  ext x
  rw [mem_translateSites_iff]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨face, hx⟩
    rw [typicalFace_translate] at hx
    obtain ⟨y, hy, rfl⟩ := (mem_translateSites_iff a _ x).mp hx
    exact ⟨y, ⟨face, hy⟩, rfl⟩
  · rintro ⟨y, ⟨face, hy⟩, rfl⟩
    refine ⟨face, ?_⟩
    rw [typicalFace_translate]
    exact (mem_translateSites a _ y).mpr hy


/-! ### Covariance of the typical-cluster conditions and of pre-goodness -/

lemma translateSites_inter {d : ℕ} (a : Vertex d) (U W : Finset (Vertex d)) :
    translateSites a (U ∩ W) = translateSites a U ∩ translateSites a W :=
  Finset.image_inter _ _ (add_right_injective a)

lemma translateSites_sdiff {d : ℕ} (a : Vertex d) (U W : Finset (Vertex d)) :
    translateSites a (U \ W) = translateSites a U \ translateSites a W :=
  Finset.image_sdiff _ _ (add_right_injective a)

lemma translateSites_subset_iff {d : ℕ} (a : Vertex d) (U W : Finset (Vertex d)) :
    translateSites a U ⊆ translateSites a W ↔ U ⊆ W :=
  Finset.image_subset_image_iff (add_right_injective a)

lemma translateSites_nonempty {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) :
    (translateSites a U).Nonempty ↔ U.Nonempty :=
  Finset.image_nonempty

lemma sum_translateSites {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) (f : Vertex d → ℝ) :
    ∑ y ∈ translateSites a U, f y = ∑ y ∈ U, f (a + y) :=
  Finset.sum_image (fun _ _ _ _ h => add_right_injective a h)

lemma latticeDistance_translate {d : ℕ} (a x y : Vertex d) :
    latticeDistance (a + x) (a + y) = latticeDistance x y := by
  have h : ∀ w : Vertex d, vertexReal (a + w) = vertexReal a + vertexReal w := by
    intro w
    funext i
    simp only [vertexReal, Pi.add_apply, Int.cast_add]
  unfold latticeDistance
  rw [h, h, dist_add_left]

lemma sourceRegularPoint_translate {d : ℕ} (a : Vertex d) (F S B : Finset (Vertex d))
    (r : ℕ) (δ : ℝ) (x : Vertex d) :
    sourceRegularPoint (translateSites a F) (translateSites a S) (translateSites a B) r δ
      (a + x) ↔ sourceRegularPoint F S B r δ x := by
  unfold sourceRegularPoint regularityEnergyOne regularityEnergyTwo
  rw [← translateSites_inter, ← translateSites_sdiff, mem_translateSites, sum_translateSites,
    sum_translateSites]
  simp only [latticeDistance_translate]

lemma iso_dist_le {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G ≃g G')
    (u v : V) (hr : G.Reachable u v) : G'.dist (φ u) (φ v) ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← hp, ← SimpleGraph.Walk.length_map φ.toHom p]
  exact SimpleGraph.dist_le _

/-- Graph distance is invariant under graph isomorphisms. -/
lemma iso_dist_eq {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G ≃g G')
    (u v : V) : G'.dist (φ u) (φ v) = G.dist u v := by
  by_cases hr : G.Reachable u v
  · refine le_antisymm (iso_dist_le φ u v hr) ?_
    have h := iso_dist_le φ.symm (φ u) (φ v) ((φ.reachable_iff (u := u) (v := v)).mpr hr)
    simpa only [RelIso.symm_apply_apply] using h
  · have hr' : ¬ G'.Reachable (φ u) (φ v) := fun h => hr ((φ.reachable_iff).mp h)
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hr,
      SimpleGraph.dist_eq_zero_of_not_reachable hr']

lemma spanningFaceDiameter_translate {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Vertex d) (G G' : SimpleGraph (Vertex d))
    (hdist : ∀ x y, G'.dist (a + x) (a + y) = G.dist x y)
    (C : Finset (Vertex d)) (faces : ι → Finset (Vertex d)) :
    spanningFaceDiameter G' (translateSites a C) (fun i => translateSites a (faces i)) =
      spanningFaceDiameter G C faces := by
  unfold spanningFaceDiameter
  refine Finset.sup_congr rfl (fun p _ => ?_)
  apply le_antisymm
  · refine Finset.sup_le (fun xy hxy => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxy
    rw [← translateSites_inter] at h1 h2
    obtain ⟨x, hx, hx'⟩ := (mem_translateSites_iff a _ _).mp h1
    obtain ⟨y, hy, hy'⟩ := (mem_translateSites_iff a _ _).mp h2
    rw [← hx', ← hy', hdist]
    exact Finset.le_sup (f := fun xy : Vertex d × Vertex d => G.dist xy.1 xy.2)
      (Finset.mem_product.mpr ⟨hx, hy⟩ : (x, y) ∈ _)
  · refine Finset.sup_le (fun xy hxy => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxy
    rw [← hdist]
    refine Finset.le_sup (f := fun xy : Vertex d × Vertex d => G'.dist xy.1 xy.2)
      (b := (a + xy.1, a + xy.2)) (Finset.mem_product.mpr ⟨?_, ?_⟩)
    · rw [← translateSites_inter]
      exact (mem_translateSites a _ _).mpr h1
    · rw [← translateSites_inter]
      exact (mem_translateSites a _ _).mpr h2

theorem typicalRegularPatch_translate {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (a z : Vertex d) (ω : Configuration d) (C : Finset (Vertex d)) (face : Fin d × Bool)
    (plus : Bool) :
    typicalRegularPatch typ t (a + z) ω (translateSites a C) face plus =
      translateSites a (typicalRegularPatch typ t z (translateConfiguration a ω) C face plus) := by
  unfold typicalRegularPatch
  rw [typicalSplitFace_translate, typicalCube_translate, typicalHeart_translate,
    typicalInnerCube_translate, typicalBoundary_translate, heartClusterUnion_translate,
    ← translateSites_inter]
  refine translateSites_filter a _ _ _ ?_
  intro x
  exact sourceRegularPoint_translate a _ _ _ _ _ x

theorem isTypicalCluster_translate {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (a z : Vertex d) (ω : Configuration d) (C : Finset (Vertex d)) :
    IsTypicalCluster typ t (a + z) ω (translateSites a C) ↔
      IsTypicalCluster typ t z (translateConfiguration a ω) C := by
  have hface : typicalFace t (a + z) = fun f => translateSites a (typicalFace t z f) := by
    funext f
    exact typicalFace_translate t a z f
  have hd : spanningFaceDiameter
      (restrictedGraph ω (typicalCube t (a + z) : Set (Vertex d))) (translateSites a C)
        (typicalFace t (a + z)) =
      spanningFaceDiameter (restrictedGraph (translateConfiguration a ω)
        (typicalCube t z : Set (Vertex d))) C (typicalFace t z) := by
    rw [hface, typicalCube_translate]
    exact spanningFaceDiameter_translate a _ _
      (fun x y => iso_dist_eq (restrictedTranslateIso a ω (typicalCube t z)) x y) C _
  unfold IsTypicalCluster
  rw [hd]
  simp only [typicalRegularPatch_translate, card_translateSites, typicalCube_translate,
    typicalHeart_translate, heartClusterUnion_translate, typicalFace_translate,
    ← translateSites_inter, translateSites_subset_iff, translateSites_nonempty]

theorem typicalClusterFamily_translate {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (a z : Vertex d) (ω : Configuration d) :
    typicalClusterFamily typ t (a + z) ω =
      (typicalClusterFamily typ t z (translateConfiguration a ω)).image (translateSites a) := by
  ext C
  rw [mem_typicalClusterFamily, Finset.mem_image, typicalCube_translate,
    finiteClusterFamily_translate, Finset.mem_image]
  constructor
  · rintro ⟨⟨C0, hC0, rfl⟩, htyp⟩
    exact ⟨C0, (mem_typicalClusterFamily _ _ _ _ _).mpr
      ⟨hC0, (isTypicalCluster_translate typ t a z ω C0).mp htyp⟩, rfl⟩
  · rintro ⟨C0, hC0, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_typicalClusterFamily _ _ _ _ _).mp hC0
    exact ⟨⟨C0, h1, rfl⟩, (isTypicalCluster_translate typ t a z ω C0).mpr h2⟩

/-- **Pre-goodness is translation covariant.** -/
theorem isPreGoodCube_translate {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (a z : Vertex d) (ω : Configuration d) :
    IsPreGoodCube typ t (a + z) ω ↔ IsPreGoodCube typ t z (translateConfiguration a ω) := by
  unfold IsPreGoodCube
  rw [typicalClusterFamily_translate,
    Finset.card_image_of_injective
      (typicalClusterFamily typ t z (translateConfiguration a ω))
      (show Function.Injective (translateSites a) from
        Finset.image_injective (add_right_injective a))]

/-- Translation as a measurable equivalence of configurations. -/
def translateConfigEquiv {d : ℕ} (a : Vertex d) : Configuration d ≃ᵐ Configuration d where
  toFun := translateConfiguration a
  invFun := translateConfiguration (-a)
  left_inv ω := by
    funext e
    show ω (translateBond a (translateBond (-a) e)) = ω e
    congr 1
    simp [translateBond]
  right_inv ω := by
    funext e
    show ω (translateBond (-a) (translateBond a e)) = ω e
    congr 1
    simp [translateBond]
  measurable_toFun := measurable_translateConfiguration a
  measurable_invFun := measurable_translateConfiguration (-a)

/-- Integrals against the percolation law are translation invariant; no
measurability of the integrand is needed. -/
theorem percolation_integral_translate {d : ℕ} (p : unitInterval) (a : Vertex d)
    (f : Configuration d → ℝ) :
    (∫ ω, f (translateConfiguration a ω) ∂(percolation d p)) = ∫ ω, f ω ∂(percolation d p) := by
  have h := (translateConfigEquiv a).measurableEmbedding.integral_map (μ := percolation d p) f
  have hmap : (percolation d p).map (translateConfigEquiv a) = percolation d p :=
    percolation_map_translation p a
  rw [hmap] at h
  exact h.symm

/-- **The pre-good probability is the same at every cube.** -/
theorem preGood_integral_translate {d : ℕ} (p : unitInterval) (typ : TypicalParameters)
    (t : ℕ) (a : Vertex d) :
    (∫ ω, (if IsPreGoodCube typ t a ω then (1:ℝ) else 0) ∂(percolation d p)) =
      ∫ ω, (if IsPreGoodCube typ t 0 ω then (1:ℝ) else 0) ∂(percolation d p) := by
  rw [← percolation_integral_translate p a
    (fun ω => if IsPreGoodCube typ t 0 ω then (1:ℝ) else 0)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  have h := isPreGoodCube_translate typ t a 0 ω
  rw [add_zero] at h
  show (if IsPreGoodCube typ t a ω then (1:ℝ) else 0) =
    if IsPreGoodCube typ t 0 (translateConfiguration a ω) then (1:ℝ) else 0
  simp only [h]

/-- `prop.proba.pregood` at the origin cube gives it at every cube: the
hypothesis `hpre` of the capstones needs proving for one cube only. -/
theorem preGood_all_of_origin {d : ℕ} (p : unitInterval) (typ : TypicalParameters)
    (t : ℕ) (c : ℝ)
    (h0 : c ≤ ∫ ω, (if IsPreGoodCube typ t (0 : Vertex d) ω then (1:ℝ) else 0)
      ∂(percolation d p)) (a : Vertex d) :
    c ≤ ∫ ω, (if IsPreGoodCube typ t a ω then (1:ℝ) else 0) ∂(percolation d p) := by
  rw [preGood_integral_translate]
  exact h0

end NearCritical.Section10
