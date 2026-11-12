module

public import NearCritical.NestRepresentative

/-! Deterministic extraction of the microscopic path of a selected nest trace.
The trace contains only local source data, not an assumed concatenated path or
MicroscopicChainGeometry. Its stochastic construction remains unresolved. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- Local tube data at one successful source step. The diameter is the literal
boundary-to-boundary maximum, not an arbitrary graph diameter. No short bridge
is a field: that bridge is constructed from offspring incidence and this bound. -/
structure NestSprinklingStep (d : ℕ) (ι : Type*) (ω : Configuration d)
    (D : Set (Vertex d)) (B : ℝ) where
  leftRegion : Set (Vertex d)
  rightRegion : Set (Vertex d)
  firstCube : Set (Vertex d)
  firstRevealed : Set (Vertex d)
  lastCube : Set (Vertex d)
  lastRevealed : Set (Vertex d)
  left_subset : leftRegion ⊆ D
  right_subset : rightRegion ⊆ D
  left_avoid : Disjoint leftRegion lastCube
  right_avoid : Disjoint rightRegion firstCube
  leftGraph : SimpleGraph (Vertex d)
  rightGraph : SimpleGraph (Vertex d)
  left_deleted : leftGraph ≤ microscopicPieceGraph ω leftRegion
    (exploredEdgeSet firstCube firstRevealed)ᶜ
  right_deleted : rightGraph ≤ microscopicPieceGraph ω rightRegion
    (exploredEdgeSet lastCube lastRevealed)ᶜ
  sourceBoundary : Finset (Vertex d)
  candidates : Finset ι
  targetBoundary : ι → Finset (Vertex d)
  pivots : Finset (Vertex d × Vertex d)
  source_mem : ∀ x ∈ sourceBoundary, x ∈ leftRegion
  pivot_open : ∀ e ∈ pivots, e.2 ∈ rightRegion ∧ (openGraph ω).Adj e.1 e.2
  intrinsic_bound : (sprinklingIntrinsicDiameter leftGraph rightGraph sourceBoundary
    (sprinklingTargetBoundary candidates targetBoundary) pivots : ℝ) ≤ B

namespace NestSprinklingStep

def offspring {d : ℕ} {ι : Type*} {ω : Configuration d} {D : Set (Vertex d)} {B : ℝ}
    (s : NestSprinklingStep d ι ω D B) : Finset ι :=
  sprinklingOffspring s.leftGraph s.rightGraph s.sourceBoundary s.candidates s.targetBoundary s.pivots

/-- Restrict a whole-nest datum to one representative's boundary. The source
whole-nest intrinsic bound supplies the restricted bound by monotonicity. -/
def restrictSource {d : ℕ} {ι : Type*} {ω : Configuration d}
    {D : Set (Vertex d)} {B : ℝ} (s : NestSprinklingStep d ι ω D B)
    (A : Finset (Vertex d)) (hA : A ⊆ s.sourceBoundary) : NestSprinklingStep d ι ω D B :=
  { s with
    sourceBoundary := A
    source_mem := fun x hx => s.source_mem x (hA hx)
    intrinsic_bound := (Nat.cast_le.mpr (sprinklingIntrinsicDiameter_mono
      s.leftGraph s.rightGraph hA (Finset.Subset.refl _)
      (Finset.Subset.refl _))).trans s.intrinsic_bound }

lemma offspring_restrictSource {d : ℕ} {ι : Type*} {ω : Configuration d}
    {D : Set (Vertex d)} {B : ℝ} (s : NestSprinklingStep d ι ω D B)
    (A : Finset (Vertex d)) (hA : A ⊆ s.sourceBoundary) :
    (s.restrictSource A hA).offspring =
      sprinklingOffspring s.leftGraph s.rightGraph A s.candidates s.targetBoundary s.pivots := rfl

/-- Every computed offspring has a newly constructed exact-union short bridge;
the entire bridge graph avoids both explored edge sets. -/
theorem bridge {d : ℕ} {ι : Type*} {ω : Configuration d} {D : Set (Vertex d)} {B : ℝ}
    (s : NestSprinklingStep d ι ω D B) {c : ι} (hc : c ∈ s.offspring) :
    ∃ x ∈ s.sourceBoundary, ∃ y ∈ s.targetBoundary c, ∃ a b,
      (a,b) ∈ s.pivots ∧
      BoundedIntrinsicConnection (sprinklingBridgeGraph s.leftGraph s.rightGraph a b) x y B ∧
      sprinklingBridgeGraph s.leftGraph s.rightGraph a b ≤ microscopicPieceGraph ω D
        (exploredEdgeSet s.firstCube s.firstRevealed ∪
          exploredEdgeSet s.lastCube s.lastRevealed)ᶜ :=
  sprinkling_offspring_short_bridge D s.leftRegion s.rightRegion
    s.firstCube s.firstRevealed s.lastCube s.lastRevealed
    s.left_subset s.right_subset s.left_avoid s.right_avoid s.left_deleted s.right_deleted
    s.sourceBoundary s.candidates s.targetBoundary s.pivots s.source_mem s.pivot_open hc s.intrinsic_bound

end NestSprinklingStep

/-- Nonrecursive local data of a finite selected nest trace. The representative
graphs are EXACTLY the critical configuration restricted to the supplied FULL sites;
metric bounds are required only on interfaceSites, usually boundary points;
they cannot be replaced by unrelated full-p cluster paths. First-good selection
can instantiate these representatives via NestRepresentative. The stochastic
survival/typicality-to-data theorem is not part of this deterministic record. -/
structure SelectedNestTrace (d : ℕ) (ι : Type*) (ω : Configuration d)
    (D : Set (Vertex d)) (A B : ℝ) (n : ℕ) where
  critical : Configuration d
  critical_le : ∀ e, critical e = true → ω e = true
  nest : ℕ → Finset ι
  representative : ℕ → ι
  representative_mem : ∀ t, t ≤ n → representative t ∈ nest t
  sites : ℕ → ι → Set (Vertex d)
  interfaceSites : ℕ → ι → Set (Vertex d)
  interface_subset : ∀ t, t ≤ n → interfaceSites t (representative t) ⊆ sites t (representative t)
  sites_subset : ∀ t, t ≤ n → sites t (representative t) ⊆ D
  typical_diameter : ∀ t, t ≤ n → ∀ x ∈ interfaceSites t (representative t),
    ∀ y ∈ interfaceSites t (representative t),
      BoundedIntrinsicConnection (restrictedGraph critical (sites t (representative t))) x y A
  step : ∀ t, t < n → NestSprinklingStep d ι ω D B
  critical_sides : ∀ t (ht : t < n),
    (step t ht).leftGraph ≤ openGraph critical ∧ (step t ht).rightGraph ≤ openGraph critical
  source_in_representative : ∀ t (ht : t < n), ∀ x ∈ (step t ht).sourceBoundary,
    x ∈ interfaceSites t (representative t)
  target_in_cluster : ∀ t (ht : t < n), ∀ c, ∀ y ∈ (step t ht).targetBoundary c,
    y ∈ interfaceSites (t+1) c
  next_nest_offspring : ∀ t (ht : t < n), nest (t+1) ⊆ (step t ht).offspring

namespace SelectedNestTrace

lemma representativeGraph_le {d : ℕ} {ι : Type*} {ω : Configuration d}
    {D : Set (Vertex d)} {A B : ℝ} {n : ℕ}
    (tr : SelectedNestTrace d ι ω D A B n) {t : ℕ} (ht : t ≤ n) :
    restrictedGraph tr.critical (tr.sites t (tr.representative t)) ≤ restrictedGraph ω D := by
  rintro x y ⟨hxy, hx, hy⟩
  exact ⟨openGraph_mono tr.critical_le hxy, tr.sites_subset t ht hx, tr.sites_subset t ht hy⟩

/-- Next representative membership follows from nest containment, exactly as in
the first sentence of the source proof of lem.nw.path. -/
lemma next_representative_offspring {d : ℕ} {ι : Type*} {ω : Configuration d}
    {D : Set (Vertex d)} {A B : ℝ} {n : ℕ}
    (tr : SelectedNestTrace d ι ω D A B n) {t : ℕ} (ht : t < n) :
    tr.representative (t+1) ∈ (tr.step t ht).offspring :=
  tr.next_nest_offspring t ht (tr.representative_mem (t+1) (by omega))

/-- Local selected offspring and typical intrinsic bounds construct the actual
recursive geometry expected by the existing global assembler. That geometry is
not an input. The offset form also covers every suffix of the selected trace. -/
theorem geometry_suffix {d : ℕ} {ι : Type*} {ω : Configuration d}
    {D : Set (Vertex d)} {A B : ℝ} {n : ℕ}
    (tr : SelectedNestTrace d ι ω D A B n) {m t : ℕ} (ht : t+m=n)
    {x y : Vertex d} (hx : x ∈ tr.interfaceSites t (tr.representative t))
    (hy : y ∈ tr.interfaceSites n (tr.representative n)) :
    MicroscopicChainGeometry (restrictedGraph ω D) A B m x y := by
  induction m generalizing t x with
  | zero =>
    have heq : t=n := by omega
    subst t
    exact ⟨restrictedGraph tr.critical (tr.sites n (tr.representative n)),
      tr.representativeGraph_le (by omega), tr.typical_diameter n (by omega) x hx y hy⟩
  | succ m ih =>
    have htn : t<n := by omega
    let s := tr.step t htn
    have hc : tr.representative (t+1) ∈ s.offspring := tr.next_representative_offspring htn
    obtain ⟨u, hu, v, hv, a, b, _, hbridge, hdeleted⟩ := s.bridge hc
    have hu' := tr.source_in_representative t htn u hu
    have hv' := tr.target_in_cluster t htn (tr.representative (t+1)) v hv
    refine ⟨restrictedGraph tr.critical (tr.sites t (tr.representative t)),
      sprinklingBridgeGraph s.leftGraph s.rightGraph a b, u, v,
      tr.representativeGraph_le (by omega), ?_,
      tr.typical_diameter t (by omega) x hx u hu', hbridge, ?_⟩
    · exact hdeleted.trans (microscopicPieceGraph_le_restricted ω D _)
    · exact ih (t := t+1) (by omega) hv'

/-- Full selected trace, including the zero-step case. -/
theorem geometry {d : ℕ} {ι : Type*} {ω : Configuration d}
    {D : Set (Vertex d)} {A B : ℝ} {n : ℕ}
    (tr : SelectedNestTrace d ι ω D A B n) {x y : Vertex d}
    (hx : x ∈ tr.interfaceSites 0 (tr.representative 0))
    (hy : y ∈ tr.interfaceSites n (tr.representative n)) :
    MicroscopicChainGeometry (restrictedGraph ω D) A B n x y :=
  tr.geometry_suffix (t := 0) (by omega) hx hy

/-- Actual confined self-avoiding path from local selected-trace data and the
actual open exit bond. The terminal +1 is retained exactly. -/
theorem exists_path_with_exit {d : ℕ} {ι : Type*} {ω : Configuration d}
    {D : Set (Vertex d)} {A B : ℝ} {n : ℕ}
    (tr : SelectedNestTrace d ι ω D A B n) {x y z : Vertex d}
    (hx : x ∈ tr.interfaceSites 0 (tr.representative 0))
    (hy : y ∈ tr.interfaceSites n (tr.representative n))
    (hexit : (openGraph ω).Adj y z) (hz : z ∈ D) :
    ∃ p : (restrictedGraph ω D).Walk x z, p.IsPath ∧
      (p.length : ℝ) ≤ ((n:ℝ)+1)*A+(n:ℝ)*B+1 := by
  obtain ⟨_, p, hp, _, _, hlen⟩ := microscopicChain_exists_path_with_exit
    (tr.geometry hx hy) ⟨hexit, tr.sites_subset n (by omega) (tr.interface_subset n (by omega) hy), hz⟩
  exact ⟨p, hp, hlen⟩

/-- Face intersection of the first representative and success of the terminal
exit convert local selected-trace data to the literal confined crossing event.
The probabilistic production of the trace and these face witnesses is separate. -/
theorem crossing {d r : ℕ} {ι : Type*} (a : Vertex d) (i : Fin d)
    {ω : Configuration d} {A B K : ℝ} {n : ℕ}
    (tr : SelectedNestTrace d ι ω
      (translateSites a (chemicalCrossingSupport d r i) : Set (Vertex d)) A B n)
    (hbottom : ∃ x ∈ chemicalBottomFace d r i,
      a+x ∈ tr.interfaceSites 0 (tr.representative 0))
    (hexit : ∃ y ∈ tr.interfaceSites n (tr.representative n),
      ∃ z ∈ chemicalExitFace d r i, (openGraph ω).Adj y (a+z))
    (hlen : ((n:ℝ)+1)*A+(n:ℝ)*B+1 ≤ K*(2*r+1:ℕ)) :
    ω ∈ chemicalBoxCrossingEvent a r i K := by
  obtain ⟨x, hx, hxsite⟩ := hbottom
  obtain ⟨y, hysite, z, hz, hopen⟩ := hexit
  apply microscopicChain_crossing a i hx hz (tr.geometry hxsite hysite)
    ⟨hopen, tr.sites_subset n (by omega) (tr.interface_subset n (by omega) hysite), ?_⟩ hlen
  exact (mem_translateSites a (chemicalCrossingSupport d r i) z).mpr
    (Finset.mem_union.mpr (Or.inr hz))

end SelectedNestTrace
end NearCritical
