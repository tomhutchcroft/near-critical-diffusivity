module

public import NearCritical.SpanningEmbeddedPath
public import NearCritical.TranslationInvariance
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section
noncomputable section

namespace NearCritical

open scoped Classical

/-- Retraction onto the open cluster of the root. The ambient
pseudometric below collapses all vertices outside this cluster to the
root, so it restricts to the actual chemical metric on the cluster. -/
def clusterChemicalRetraction {d : ℕ} (ω : Configuration d) (o x : Vertex d) : Vertex d :=
  if (openGraph ω).Reachable o x then x else o

theorem clusterChemicalRetraction_reachable {d : ℕ} (ω : Configuration d) (o x : Vertex d) :
    (openGraph ω).Reachable o (clusterChemicalRetraction ω o x) := by
  unfold clusterChemicalRetraction
  split_ifs with h
  · exact h
  · exact SimpleGraph.Reachable.refl _

theorem clusterChemicalRetraction_of_reachable {d : ℕ} (ω : Configuration d) {o x : Vertex d}
    (h : (openGraph ω).Reachable o x) : clusterChemicalRetraction ω o x = x := if_pos h

/-- Rescale the chemical distances on the open cluster. -/
def clusterChemicalPseudoMetric {d : ℕ} (ω : Configuration d) (o : Vertex d)
    (c : ℝ) (hc : 0 ≤ c) : PseudoMetricSpace (Vertex d) where
  dist x y := c * ((openGraph ω).dist (clusterChemicalRetraction ω o x)
    (clusterChemicalRetraction ω o y):ℝ)
  dist_self x := by simp
  dist_comm x y := by rw [SimpleGraph.dist_comm]
  dist_triangle x y z := by
    let G := openGraph ω
    let r := clusterChemicalRetraction ω o
    have hxy := (clusterChemicalRetraction_reachable ω o x).symm.trans
      (clusterChemicalRetraction_reachable ω o y)
    have h : (G.dist (r x) (r z):ℝ) ≤ (G.dist (r x) (r y):ℝ)+(G.dist (r y) (r z):ℝ) := by
      exact_mod_cast hxy.dist_triangle_left (r z)
    change c*(G.dist (r x) (r z):ℝ) ≤ c*(G.dist (r x) (r y):ℝ)+c*(G.dist (r y) (r z):ℝ)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left h hc

/-- Distances add along any shortest open walk. -/
theorem walk_dist_add_of_shortest {V : Type*} {G : SimpleGraph V} {o v : V}
    (w : G.Walk o v) (hw : w.length = G.dist o v) {x : V} (hx : x ∈ w.support) :
    G.dist o x + G.dist x v = G.dist o v := by
  have h₁ := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_takeUntil hx)
  have h₂ := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_dropUntil hx)
  calc
    G.dist o x + G.dist x v = (w.takeUntil x hx).length + (w.dropUntil x hx).length := by rw [h₁,h₂]
    _ = w.length := by rw [← SimpleGraph.Walk.length_append, w.take_spec hx]
    _ = _ := hw

/-- Translating a configuration transports the actual shortest-walk
metric by the same lattice translation. -/
theorem chemicalDist_translate {d : ℕ} (a x y : Vertex d) (ω : Configuration d) :
    (openGraph (translateConfiguration a ω)).dist x y = (openGraph ω).dist (a+x) (a+y) := by
  let I := translationGraphIso a ω
  have hr : (openGraph ω).Reachable (a+x) (a+y) ↔
      (openGraph (translateConfiguration a ω)).Reachable x y :=
    SimpleGraph.Iso.reachable_iff (φ := I)
  by_cases h : (openGraph (translateConfiguration a ω)).Reachable x y
  · obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist
    obtain ⟨q,hq⟩ := (hr.mpr h).exists_walk_length_eq_dist
    have hp' := SimpleGraph.dist_le (p.map I.toHom)
    rw [SimpleGraph.Walk.length_map,hp] at hp'
    have hq' := SimpleGraph.dist_le (q.map I.symm.toHom)
    rw [SimpleGraph.Walk.length_map,hq] at hq'
    have hx : I.symm (a+x) = x := I.left_inv x
    have hy : I.symm (a+y) = y := I.left_inv y
    change (openGraph (translateConfiguration a ω)).dist (I.symm (a+x)) (I.symm (a+y)) ≤ _ at hq'
    rw [hx,hy] at hq'
    exact le_antisymm hq' hp'
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable h,
      SimpleGraph.dist_eq_zero_of_not_reachable (fun h' => h (hr.mp h'))]

/-- Every point of a shortest open walk lies near the embedded limiting
geodesic under a pointed chemical-metric correspondence. -/
theorem chemical_correspondence_geodesic_near {d n : ℕ} {T : Type*} [PseudoMetricSpace T]
    (ω : Configuration d) {o v : Vertex d}
    (c : ℝ) (hc : 0 ≤ c) (R : Vertex d → T → Prop) (ε η : ℝ)
    (hR : ∀ x t, R x t → (openGraph ω).Reachable o x)
    (hcover : ∀ x, (openGraph ω).Reachable o x → ∃ t, R x t)
    (hdist : ∀ x t x' t', R x t → R x' t' →
      |c*((openGraph ω).dist x x':ℝ)-dist t t'| ≤ ε)
    (treeProjection : ∀ r y b : T, ∃ a : T,
      dist r a+dist a y = dist r y ∧ 2*dist b a = dist r b+dist b y-dist r y)
    (Φ : T → (Fin d → ℝ))
    (hembed : ∀ x t, R x t → dist (scaledSpanningVertex n x) (Φ t) ≤ ε)
    (hmodulus : ∀ s t : T, dist s t ≤ 3*ε/2 → dist (Φ s) (Φ t) ≤ η)
    {r y : T} (hor : R o r) (hvy : R v y)
    : ∃ w : (openGraph ω).Walk o v, ∀ a ∈ w.support, ∃ b : T,
        dist r b + dist b y = dist r y ∧ dist (scaledSpanningVertex n a) (Φ b) ≤ ε + η := by
  obtain ⟨w,hw⟩ := (hR v y hvy).exists_walk_length_eq_dist
  letI := clusterChemicalPseudoMetric ω o c hc
  have hd (x x' : Vertex d) (hx : (openGraph ω).Reachable o x)
      (hx' : (openGraph ω).Reachable o x') :
      dist x x' = c*((openGraph ω).dist x x':ℝ) := by
    change c*((openGraph ω).dist (clusterChemicalRetraction ω o x)
      (clusterChemicalRetraction ω o x'):ℝ) = _
    rw [clusterChemicalRetraction_of_reachable ω hx,clusterChemicalRetraction_of_reachable ω hx']
  have hd' (x : Vertex d) (s : T) (x' : Vertex d) (t : T) (hx : R x s) (hx' : R x' t) :
      |dist x x' - dist s t| ≤ ε := by
    rw [hd x x' (hR x s hx) (hR x' t hx')]
    exact hdist x s x' t hx hx'
  refine ⟨w, ?_⟩
  intro x hx
  have hxo := (w.takeUntil x hx).reachable
  have hoo : (openGraph ω).Reachable o o := SimpleGraph.Reachable.refl _
  have hgeo : dist o x + dist x v = dist o v := by
    rw [hd o x hoo hxo,hd x v hxo w.reachable,hd o v hoo w.reachable,← mul_add]
    exact congrArg (fun u : ℝ => c*u) (by exact_mod_cast walk_dist_add_of_shortest w hw hx)
  obtain ⟨b,hxb⟩ := hcover x hxo
  exact correspondence_geodesic_embedding_near R ε η hd' treeProjection
    (scaledSpanningVertex n) Φ hembed hmodulus hor hxb hvy hgeo

/-- Transfer a robust limiting geodesic to a connection in the actual
source cuboid using the cluster's rescaled chemical distance. The
walk is a shortest open walk chosen in the actual configuration. -/
theorem chemical_correspondence_source_connection {d n : ℕ} {T : Type*} [PseudoMetricSpace T]
    (hn : 1 ≤ n) (f : Fin d × Bool) (ω : Configuration d) {o v : Vertex d}
    (c : ℝ) (hc : 0 ≤ c) (R : Vertex d → T → Prop) (ε η : ℝ)
    (hη : 0 ≤ η) (hsmall : ε+η ≤ (1/32:ℝ))
    (hR : ∀ x t, R x t → (openGraph ω).Reachable o x)
    (hcover : ∀ x, (openGraph ω).Reachable o x → ∃ t, R x t)
    (hdist : ∀ x t x' t', R x t → R x' t' →
      |c*((openGraph ω).dist x x':ℝ)-dist t t'| ≤ ε)
    (treeProjection : ∀ r y b : T, ∃ a : T,
      dist r a+dist a y = dist r y ∧ 2*dist b a = dist r b+dist b y-dist r y)
    (Φ : T → (Fin d → ℝ))
    (hembed : ∀ x t, R x t → dist (scaledSpanningVertex n x) (Φ t) ≤ ε)
    (hmodulus : ∀ s t : T, dist s t ≤ 3*ε/2 → dist (Φ s) (Φ t) ≤ η)
    {r y : T} (hor : R o r) (hvy : R v y)
    (hcorridor : ∀ a : T, dist r a+dist a y = dist r y →
      (-(1/4:ℝ) ≤ realSpanningHeight f (Φ a) ∧ realSpanningHeight f (Φ a) ≤ 5/2) ∧
        (∀ j, j ≠ f.1 → |Φ a j| ≤ (1/32:ℝ)))
    (htarget : |realSpanningHeight f (Φ y)-2| ≤ (1/32:ℝ))
    (htargetTransverse : ∀ j, j ≠ f.1 → |Φ y j| ≤ (1/32:ℝ)) :
    ω ∈ connectionToSetEvent (roundedSourceSpanningCuboid n f) o (roundedSourceSpanningTarget n f) := by
  obtain ⟨w,hnear⟩ := chemical_correspondence_geodesic_near ω c hc R ε η hR hcover hdist
    treeProjection Φ hembed hmodulus hor hvy
  have hpath : ∀ a ∈ w.support, a ∈ roundedSourceSpanningCuboid n f := by
    intro a ha
    obtain ⟨b,hb,hclose⟩ := hnear a ha
    obtain ⟨hh,ht⟩ := hcorridor b hb
    exact spanning_limit_corridor_to_integer hn f a (Φ b) (hclose.trans hsmall) hh ht
  have hend := spanning_limit_target_to_integer hn f v (Φ y)
    ((hembed v y hvy).trans (by linarith)) htarget htargetTransverse
  exact ⟨hpath o w.start_mem_support,v,hend,hpath v w.end_mem_support,
    ⟨openWalkRestrictOfSupport (roundedSourceSpanningCuboid n f) w hpath⟩⟩

end NearCritical
