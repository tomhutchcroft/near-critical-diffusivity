module

public import NearCritical.Section10SemanticNestRule
public import NearCritical.Section10StepSemantics
public import NearCritical.Section10ChainMeanReveal
public import NearCritical.Section10TypicalIncident

/-! The Section 10 nest rule on the lattice, as a `SemanticRule`.

`NestLayout` is the deterministic geometry: typical cubes at the coarse sites,
and for every route step its two half tubes `L`, `R`, their overlap `Mid`, a
face direction, and a bond region containing everything the step reads, with
regions of distinct steps disjoint. (The actual tubes are supplied later; no
real arithmetic happens here.)

`NestLayout.rule` builds the `SemanticRule`:
* reveal: the critical cluster union of the cubes (`criticalReveal`), refined by
  the critical bits on the explored bonds;
* states: nests, i.e. finite sets of clusters;
* start step: any `k`-subset of the typical clusters of the first cube;
* a moving step from a `k`-nest of typical clusters: success iff the sprinkling
  cluster of the nest is typical (`svTypical`), next nests `svNext`;
* exit step: success iff some cluster of the nest has a regular top-face point
  with an open exit bond in `z.1 OR z.2`;
* stays, and all steps outside this context: trivial success;
* site events: the cube is pre-good.

Its two probability inputs are arguments: `hs` (success probability at least
`1/rho`, source `prop.proba.k-nest`; trivial outside the context) and
`hsiteProb` (`P[pre-good] >= 1/kappa`, source `prop.proba.pregood`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

namespace RouteLabel
variable {D : ℕ}

/-- The site reached by a step. -/
def target : RouteLabel D → RSite D
  | start z => z
  | up z => (z.1 + 1, z.2)
  | side z y => (z.1, y)
  | exit z => z
  | pad _ => (0, 0)

def isStep : RouteLabel D → Prop
  | up _ => True
  | side _ _ => True
  | _ => False

def isExit : RouteLabel D → Prop
  | exit _ => True
  | _ => False

def isStart : RouteLabel D → Prop
  | start _ => True
  | _ => False

end RouteLabel

/-- Both layers of a bond set. -/
def bothLayers {d : ℕ} (E : Finset (Bond d)) : Finset (LBond d) :=
  E.image (fun b => ((false, b) : LBond d)) ∪ E.image (fun b => ((true, b) : LBond d))

lemma bothLayers_disjoint {d : ℕ} {E E' : Finset (Bond d)} (h : Disjoint E E') :
    Disjoint (bothLayers E) (bothLayers E') := by
  rw [Finset.disjoint_left] at h ⊢
  intro e he he'
  unfold bothLayers at he he'
  have h1 : e.2 ∈ E := by
    rcases Finset.mem_union.mp he with h | h <;>
      (obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h; exact hb)
  have h2 : e.2 ∈ E' := by
    rcases Finset.mem_union.mp he' with h | h <;>
      (obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h; exact hb)
  exact h h1 h2

lemma bothLayers_mono {d : ℕ} {E E' : Finset (Bond d)} (h : E ⊆ E') :
    bothLayers E ⊆ bothLayers E' :=
  Finset.union_subset_union (Finset.image_subset_image h) (Finset.image_subset_image h)

/-- A function reading only `U` composes to a local function. -/
lemma isLocal_of_readsOnly {d : ℕ} {β : Type*} {U : Finset (LBond d)}
    {P : Configuration d × Configuration d → β} (hP : ReadsOnly U P) (φ : β → ℝ) :
    IsLocal U (fun z => φ (P z)) := by
  refine ⟨fun b => φ (P (gluePair (S := U) (T := U) b b)), fun z => ?_⟩
  have h := glue_fun_eq (S := U) (T := U) P (hP.mono Finset.subset_union_left) z
  show φ (P z) = φ (P (gluePair (U.restrict (layerVal z)) (U.restrict (layerVal z))))
  rw [h]

/-- Deterministic geometry of the construction. -/
structure NestLayout (D d : ℕ) where
  typ : TypicalParameters
  t : ℕ
  k : ℕ
  hk : 0 < k
  MOff : ℕ
  Mcoal : ℕ
  Kdiam : ℕ
  siteBox : Finset (RSite D)
  center : RSite D → Vertex d
  hdisj : (siteBox : Set (RSite D)).PairwiseDisjoint (fun s => typicalCube t (center s))
  i₀ : Fin d
  dir : RouteLabel D → Fin d
  Mid : RouteLabel D → Finset (Vertex d)
  L : RouteLabel D → Finset (Vertex d)
  R : RouteLabel D → Finset (Vertex d)
  region : RouteLabel D → Finset (Bond d)
  hregion : ∀ a b, a ≠ b → Disjoint (region a) (region b)
  hL : ∀ ℓ, internalBondSet (L ℓ) ⊆ region ℓ
  hR : ∀ ℓ, internalBondSet (R ℓ) ⊆ region ℓ
  hMid : ∀ ℓ, internalBondSet (Mid ℓ) ⊆ region ℓ
  top : ℕ
  hexit : ∀ z : RSite D, z.1 = top →
    (typicalFace t (center z) (i₀, true)).image (fun y => ((y, i₀) : Bond d)) ⊆
      region (RouteLabel.exit z)

namespace NestLayout
variable {D d : ℕ} (Λ : NestLayout D d)

/-- The cube of a site. -/
def Q (s : RSite D) : Finset (Vertex d) := typicalCube Λ.t (Λ.center s)

/-- The heart of the cube of a site. -/
def Hh (s : RSite D) : Finset (Vertex d) := typicalHeart Λ.t (Λ.center s) Λ.typ.heartRatio

lemma hH (s : RSite D) : Λ.Hh s ⊆ Λ.Q s := Finset.filter_subset _ _

/-- Values of the base reveal. -/
abbrev Φ₀ : Type := RevealValue Λ.siteBox Λ.Q

/-- Explored bonds. -/
def S₀ (F : Λ.Φ₀) : Finset (LBond d) := revealBondsOf Λ.siteBox Λ.Q F

/-- The base reveal. -/
def ρ₀ (z : Configuration d × Configuration d) : Λ.Φ₀ :=
  criticalReveal Λ.siteBox Λ.Q Λ.Hh z

/-- Values of the refined reveal. -/
abbrev Φ : Type := Σ F : Λ.Φ₀, (Λ.S₀ F → Bool)

/-- The critical configuration as known from the refined reveal (closed off the
explored bonds). -/
def revealConfig (G : Λ.Φ) : Configuration d :=
  (gluePair (S := Λ.S₀ G.1) (T := (∅ : Finset (LBond d))) G.2 (fun _ => false)).1

/-- Typical clusters of a cube, as known from the reveal. -/
def fam (G : Λ.Φ) (s : RSite D) : Finset (Finset (Vertex d)) :=
  typicalClusterFamily Λ.typ Λ.t (Λ.center s) (Λ.revealConfig G)

/-- The cube is pre-good, as known from the reveal. -/
def goodCube (G : Λ.Φ) (s : RSite D) : Prop :=
  IsPreGoodCube Λ.typ Λ.t (Λ.center s) (Λ.revealConfig G)

/-- Revealed union inside the cube of a site. -/
def Fat (F : Λ.Φ₀) (s : RSite D) : Finset (Vertex d) := F.val ∩ Λ.Q s

/-- Source patch of a cluster for a step. -/
def src (G : Λ.Φ) (ℓ : RouteLabel D) (pl : Bool) (C : Finset (Vertex d)) : Finset (Vertex d) :=
  typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.site) (Λ.revealConfig G) C (Λ.dir ℓ, true) pl

/-- Target patch of a cluster of the next cube. -/
def tgt (G : Λ.Φ) (ℓ : RouteLabel D) (C : Finset (Vertex d)) : Finset (Vertex d) :=
  typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.target) (Λ.revealConfig G) C (Λ.dir ℓ, false) true ∪
    typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.target) (Λ.revealConfig G) C (Λ.dir ℓ, false) false

/-- All source patches of the cube. -/
def faceAll (G : Λ.Φ) (ℓ : RouteLabel D) (pl : Bool) : Finset (Vertex d) :=
  sprinklingTargetBoundary (Λ.fam G ℓ.site) (Λ.src G ℓ pl)

/-- Top patch of a cluster, for the exit. -/
def exitPatch (G : Λ.Φ) (ℓ : RouteLabel D) (C : Finset (Vertex d)) : Finset (Vertex d) :=
  typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.site) (Λ.revealConfig G) C (Λ.i₀, true) true

/-- All clusters that can occur. -/
def allClusters : Finset (Finset (Vertex d)) :=
  (Finset.univ : Finset Λ.Φ).biUnion (fun G => Λ.siteBox.biUnion (Λ.fam G))

/-- All nests. -/
def P : Finset (Finset (Finset (Vertex d))) := Λ.allClusters.powerset

/-- States: nests. -/
abbrev X : Type := ↥Λ.P × Bool

lemma fam_powerset_subset (G : Λ.Φ) {s : RSite D} (hs : s ∈ Λ.siteBox) :
    (Λ.fam G s).powerset ⊆ Λ.P := by
  intro N hN
  refine Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hN).trans ?_)
  intro C hC
  exact Finset.mem_biUnion.mpr ⟨G, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨s, hs, hC⟩⟩

/-- Exit points of a label. -/
def exitPts (ℓ : RouteLabel D) : Finset (Vertex d) :=
  if ℓ.isExit ∧ ℓ.site.1 = Λ.top then typicalFace Λ.t (Λ.center ℓ.site) (Λ.i₀, true) else ∅

/-- Layered bonds read by a step. -/
def readSet (F : Λ.Φ₀) (ℓ : RouteLabel D) : Finset (LBond d) :=
  stepReadSet (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site) (Λ.Fat F ℓ.site) (Λ.Q ℓ.target)
      (Λ.Fat F ℓ.target) ∪
    bothLayers ((Λ.exitPts ℓ).image (fun y => ((y, Λ.i₀) : Bond d)))

/-- Fresh block of a step. -/
def Bl₀ (F : Λ.Φ₀) (ℓ : RouteLabel D) : Finset (LBond d) := Λ.readSet F ℓ \ Λ.S₀ F

lemma readSet_subset_region (F : Λ.Φ₀) (ℓ : RouteLabel D) :
    Λ.readSet F ℓ ⊆ bothLayers (Λ.region ℓ) := by
  unfold readSet stepReadSet
  refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
  · refine (Finset.image_subset_image ?_).trans Finset.subset_union_left
    refine Finset.union_subset (Finset.union_subset ?_ ?_) (Λ.hMid ℓ)
    · exact Finset.sdiff_subset.trans (Λ.hL ℓ)
    · exact Finset.sdiff_subset.trans (Λ.hR ℓ)
  · exact (Finset.image_subset_image (Λ.hMid ℓ)).trans Finset.subset_union_right
  · apply bothLayers_mono
    unfold exitPts
    cases ℓ with
    | exit z =>
      by_cases htop : z.1 = Λ.top
      · have h : (RouteLabel.exit z : RouteLabel D).isExit ∧
            (RouteLabel.exit z : RouteLabel D).site.1 = Λ.top := ⟨trivial, htop⟩
        rw [if_pos h]
        exact Λ.hexit z htop
      · have h : ¬ ((RouteLabel.exit z : RouteLabel D).isExit ∧
            (RouteLabel.exit z : RouteLabel D).site.1 = Λ.top) := fun h => htop h.2
        rw [if_neg h]
        simp
    | start z => simp [RouteLabel.isExit]
    | up z => simp [RouteLabel.isExit]
    | side z y => simp [RouteLabel.isExit]
    | pad k => simp [RouteLabel.isExit]

lemma hBl₀ (F : Λ.Φ₀) (a b : RouteLabel D) (hab : a ≠ b) :
    Disjoint (Λ.Bl₀ F a) (Λ.Bl₀ F b) :=
  Finset.disjoint_of_subset_left
    (Finset.sdiff_subset.trans (Λ.readSet_subset_region F a))
    (Finset.disjoint_of_subset_right
      (Finset.sdiff_subset.trans (Λ.readSet_subset_region F b))
      (bothLayers_disjoint (Λ.hregion a b hab)))

lemma hS₀ (F : Λ.Φ₀) (a : RouteLabel D) : Disjoint (Λ.S₀ F) (Λ.Bl₀ F a) :=
  Finset.disjoint_sdiff

/-- What a step sees of the configuration pair. -/
def view (F : Λ.Φ₀) (ℓ : RouteLabel D) (z : Configuration d × Configuration d) :
    StepView d × Finset (Vertex d) :=
  (stepView (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site) (Λ.Fat F ℓ.site) (Λ.Q ℓ.target)
      (Λ.Fat F ℓ.target) z,
    (Λ.exitPts ℓ).filter (fun y => sprinkleOrConfiguration z.1 z.2 (y, Λ.i₀) = true))

theorem view_readsOnly (F : Λ.Φ₀) (ℓ : RouteLabel D) :
    ReadsOnly (Λ.S₀ F ∪ Λ.Bl₀ F ℓ) (Λ.view F ℓ) := by
  have hsub : Λ.readSet F ℓ ⊆ Λ.S₀ F ∪ Λ.Bl₀ F ℓ := by
    intro e he
    by_cases h : e ∈ Λ.S₀ F
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, h⟩)
  refine ReadsOnly.mono hsub ?_
  refine ReadsOnly.pair ?_ ?_
  · exact (stepView_readsOnly _ _ _ _ _ _ _).mono Finset.subset_union_left
  · intro z z' hz
    refine Finset.filter_congr (fun y hy => ?_)
    have hmem : ((y, Λ.i₀) : Bond d) ∈ (Λ.exitPts ℓ).image (fun y => ((y, Λ.i₀) : Bond d)) :=
      Finset.mem_image_of_mem _ hy
    have h1 : z.1 (y, Λ.i₀) = z'.1 (y, Λ.i₀) :=
      hz ((false, (y, Λ.i₀)) : LBond d) (Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))
    have h2 : z.2 (y, Λ.i₀) = z'.2 (y, Λ.i₀) :=
      hz ((true, (y, Λ.i₀)) : LBond d) (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmem)))
    unfold sprinkleOrConfiguration
    rw [h1, h2]

/-- Context of a moving step: a `k`-nest of typical clusters between two
PRE-GOOD cubes of the box, on a reveal value that is actually realised. The
source states `prop.proba.k-nest` exactly in this context; without the pre-good
condition the target cube may have no typical cluster and success is
impossible. -/
def moveCtx (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X) : Prop :=
  ℓ.isStep ∧ ℓ.target ≠ ℓ.site ∧ ℓ.site ∈ Λ.siteBox ∧ ℓ.target ∈ Λ.siteBox ∧
    x.1.val.card = Λ.k ∧ x.1.val ⊆ Λ.fam G ℓ.site ∧
    Λ.goodCube G ℓ.site ∧ Λ.goodCube G ℓ.target ∧
    ∃ z, refineReveal Λ.ρ₀ Λ.S₀ z = G

/-- Context of the exit step. -/
def exitCtx (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X) : Prop :=
  ℓ.isExit ∧ ℓ.site.1 = Λ.top ∧ ℓ.site ∈ Λ.siteBox ∧ x.1.val.card = Λ.k ∧
    x.1.val ⊆ Λ.fam G ℓ.site

/-- Context of the start step. -/
def startCtx (G : Λ.Φ) (ℓ : RouteLabel D) : Prop :=
  ℓ.isStart ∧ ℓ.site ∈ Λ.siteBox ∧ Λ.k ≤ (Λ.fam G ℓ.site).card

/-- Typicality of the sprinkling cluster of the nest, on a view. -/
def moveTypical (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X) (w : StepView d × Finset (Vertex d)) :
    Prop :=
  svTypical w.1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2) (Λ.tgt G ℓ) (Λ.faceAll G ℓ x.2)
    Λ.k Λ.MOff Λ.Mcoal Λ.Kdiam

/-- Success of a step, on a view. -/
def succσ (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X) (w : StepView d × Finset (Vertex d)) : Prop :=
  (Λ.moveCtx G ℓ x → Λ.moveTypical G ℓ x w) ∧
  (Λ.exitCtx G ℓ x → ∃ rep ∈ x.1.val, ∃ y ∈ Λ.exitPatch G ℓ rep, y ∈ w.2)

/-- Next states of a step, on a view. -/
def offσ (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X) (w : StepView d × Finset (Vertex d)) :
    Finset Λ.X :=
  if Λ.moveCtx G ℓ x ∧ Λ.moveTypical G ℓ x w then
    (svNext w.1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2) (Λ.tgt G ℓ) Λ.k Λ.P) ×ˢ
      (Finset.univ : Finset Bool)
  else if Λ.startCtx G ℓ then
    (Λ.P.attach.filter (fun N' => N'.val.card = Λ.k ∧ N'.val ⊆ Λ.fam G ℓ.site)) ×ˢ
      (Finset.univ : Finset Bool)
  else {x}

lemma offσ_nonempty (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X)
    (w : StepView d × Finset (Vertex d)) : (Λ.offσ G ℓ x w).Nonempty := by
  unfold offσ
  split_ifs with h1 h2
  · exact (svNext_nonempty w.1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2) (Λ.tgt G ℓ) Λ.hk
      h1.1.2.2.2.2.1 h1.2 Λ.P (Λ.fam_powerset_subset G h1.1.2.2.2.1)).product
      Finset.univ_nonempty
  · obtain ⟨N', hsub, hcard⟩ := Finset.exists_subset_card_eq h2.2.2
    have hP : N' ∈ Λ.P := Λ.fam_powerset_subset G h2.2.1 (Finset.mem_powerset.mpr hsub)
    exact (show (Λ.P.attach.filter (fun N' => N'.val.card = Λ.k ∧
        N'.val ⊆ Λ.fam G ℓ.site)).Nonempty from
      ⟨⟨N', hP⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hcard, hsub⟩⟩).product
      Finset.univ_nonempty
  · exact Finset.singleton_nonempty x

/-- The cube of a site is pre-good (sites outside the box impose nothing). -/
def siteEvent (s : RSite D) : Set (Configuration d × Configuration d) :=
  {z | s ∈ Λ.siteBox → IsPreGoodCube Λ.typ Λ.t (Λ.center s) z.1}

/-- Bonds of the cube of a site, critical layer. -/
def Es (s : RSite D) : Finset (LBond d) :=
  if s ∈ Λ.siteBox then (internalBondSet (Λ.Q s)).image (fun b => ((false, b) : LBond d))
  else ∅

lemma hEs (a b : RSite D) (hab : a ≠ b) : Disjoint (Λ.Es a) (Λ.Es b) := by
  unfold Es
  by_cases ha : a ∈ Λ.siteBox
  · by_cases hb : b ∈ Λ.siteBox
    · rw [if_pos ha, if_pos hb]
      have hQ : Disjoint (Λ.Q a) (Λ.Q b) := Λ.hdisj ha hb hab
      rw [Finset.disjoint_left] at hQ ⊢
      intro e he he'
      obtain ⟨b1, hb1, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b2, hb2, h⟩ := Finset.mem_image.mp he'
      have hbb : b2 = b1 := (Prod.mk.inj h).2
      rw [hbb] at hb2
      exact hQ ((mem_internalBondSet _ _).mp hb1).1 ((mem_internalBondSet _ _).mp hb2).1
    · rw [if_neg hb]
      exact Finset.disjoint_empty_right _
  · rw [if_neg ha]
    exact Finset.disjoint_empty_left _

lemma siteEvent_readsOnly (s : RSite D) :
    ReadsOnly (Λ.Es s) (fun z => decide (z ∈ Λ.siteEvent s)) := by
  intro z z' hz
  have hiff : z ∈ Λ.siteEvent s ↔ z' ∈ Λ.siteEvent s := by
    unfold siteEvent
    by_cases hs : s ∈ Λ.siteBox
    · have hagree : ∀ e ∈ internalBondSet (typicalCube Λ.t (Λ.center s)), z.1 e = z'.1 e := by
        intro e he
        have hmem : ((false, e) : LBond d) ∈ Λ.Es s := by
          unfold Es
          rw [if_pos hs]
          exact Finset.mem_image_of_mem _ he
        exact hz _ hmem
      have h := isPreGoodCube_iff_of_internal_agree Λ.typ Λ.t (Λ.center s) z.1 z'.1 hagree
      simp only [Set.mem_setOf_eq, hs, forall_true_left]
      exact h
    · simp only [Set.mem_setOf_eq, hs, IsEmpty.forall_iff]
  simp only [hiff]

lemma hsite (s : RSite D) :
    IsLocal (Λ.Es s) (fun z => if z ∈ Λ.siteEvent s then (1:ℝ) else 0) := by
  have h := isLocal_of_readsOnly (Λ.siteEvent_readsOnly s) (fun b => if b = true then (1:ℝ) else 0)
  refine ⟨h.choose, fun z => ?_⟩
  rw [← h.choose_spec z]
  by_cases hz : z ∈ Λ.siteEvent s
  · simp [hz]
  · simp [hz]

end NestLayout
end NearCritical.Section10
