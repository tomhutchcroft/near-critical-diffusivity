module

public import NearCritical.NetworkMaximumPrinciple

/-! Two-arm witnesses from the deterministic maximum principle. The witnesses
are disjoint sets of positive network edges; connectivity survives after all
other edge weights are deleted. Since E is finite these are finite witnesses
of disjoint occurrence, including when the tested edge itself is closed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open Set
variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

/-- Delete every edge outside F. -/
def edgeRestrictedWeights (a : E → ℝ) (F : Set E) (e : E) : ℝ := by
  classical
  exact if e ∈ F then a e else 0

/-- Positive edges entirely inside a vertex set. -/
def positiveEdgesInside (a : E → ℝ) (S : Set V) : Set E :=
  {e | 0 < a e ∧ G.tail e ∈ S ∧ G.head e ∈ S}

omit [Fintype E] in
lemma positiveGraph_le_edgeRestricted (a : E → ℝ) (S : Set V) :
    G.positiveGraph a S ≤
      G.positiveGraph (edgeRestrictedWeights a (G.positiveEdgesInside a S)) Set.univ := by
  classical
  rintro x y ⟨hne, hx, hy, e, he, h | h⟩
  · have heF : e ∈ G.positiveEdgesInside a S := by
      exact ⟨he, h.1.symm ▸ hx, h.2.symm ▸ hy⟩
    exact ⟨hne, Set.mem_univ _, Set.mem_univ _, e,
      by simpa [edgeRestrictedWeights, heF] using he, Or.inl h⟩
  · have heF : e ∈ G.positiveEdgesInside a S := by
      exact ⟨he, h.1.symm ▸ hy, h.2.symm ▸ hx⟩
    exact ⟨hne, Set.mem_univ _, Set.mem_univ _, e,
      by simpa [edgeRestrictedWeights, heF] using he, Or.inr h⟩

omit [Fintype E] in
lemma positiveEdgesInside_disjoint {a : E → ℝ} {S T : Set V} (hst : Disjoint S T) :
    Disjoint (G.positiveEdgesInside a S) (G.positiveEdgesInside a T) := by
  apply Set.disjoint_left.mpr
  intro e hs ht
  exact Set.disjoint_left.mp hst hs.2.1 ht.2.1

/-- Disjoint-occurrence witnesses for connections to two target vertex sets.
Both witnessing edge sets consist entirely of open (positive-weight) edges,
and each connection holds using only its own witnessing edge set. -/
def DisjointBoundaryConnections (a : E → ℝ) (x : V) (A : Set V) (y : V) (B : Set V) : Prop :=
  ∃ F H : Set E, F.Finite ∧ H.Finite ∧ Disjoint F H ∧
    (∀ e ∈ F, 0 < a e) ∧ (∀ e ∈ H, 0 < a e) ∧
    (∃ z ∈ A, (G.positiveGraph (edgeRestrictedWeights a F) Set.univ).Reachable x z) ∧
    (∃ z ∈ B, (G.positiveGraph (edgeRestrictedWeights a H) Set.univ).Reachable y z)

lemma disjointBoundaryConnections_of_vertex_sets {a : E → ℝ} {x y : V}
    {A B S T : Set V} (hst : Disjoint S T)
    (hx : ∃ z ∈ A, (G.positiveGraph a S).Reachable x z)
    (hy : ∃ z ∈ B, (G.positiveGraph a T).Reachable y z) :
    G.DisjointBoundaryConnections a x A y B := by
  obtain ⟨zx, hzx, hxz⟩ := hx
  obtain ⟨zy, hzy, hyz⟩ := hy
  refine ⟨G.positiveEdgesInside a S, G.positiveEdgesInside a T,
    Set.toFinite _, Set.toFinite _, G.positiveEdgesInside_disjoint hst, ?_, ?_, ?_, ?_⟩
  · exact fun e he ↦ he.1
  · exact fun e he ↦ he.1
  · exact ⟨zx, hzx, SimpleGraph.Reachable.mono (G.positiveGraph_le_edgeRestricted a S) hxz⟩
  · exact ⟨zy, hzy, SimpleGraph.Reachable.mono (G.positiveGraph_le_edgeRestricted a T) hyz⟩

omit [Fintype E] in
/-- Swapping the two arms also swaps the two witnessing edge sets. -/
lemma DisjointBoundaryConnections.symm {a : E → ℝ} {x y : V} {A B : Set V}
    (h : G.DisjointBoundaryConnections a x A y B) : G.DisjointBoundaryConnections a y B x A := by
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hx, hy⟩ := h
  exact ⟨H, F, hFinH, hFinF, hdisj.symm, hH, hF, hy, hx⟩

/-- Ordered certificates retain potential separation on every witness edge.
This makes exclusion of a tested edge joining x to y explicit. -/
def SeparatedBoundaryConnections (a : E → ℝ) (u : V → ℝ)
    (x : V) (A : Set V) (y : V) (B : Set V) : Prop :=
  ∃ F H : Set E, F.Finite ∧ H.Finite ∧ Disjoint F H ∧
    (∀ e ∈ F, 0 < a e ∧ u (G.tail e) ≤ u x ∧ u (G.head e) ≤ u x) ∧
    (∀ e ∈ H, 0 < a e ∧ u y ≤ u (G.tail e) ∧ u y ≤ u (G.head e)) ∧
    (∃ z ∈ A, (G.positiveGraph (edgeRestrictedWeights a F) Set.univ).Reachable x z) ∧
    (∃ z ∈ B, (G.positiveGraph (edgeRestrictedWeights a H) Set.univ).Reachable y z)

omit [Fintype E] in
lemma SeparatedBoundaryConnections.to_disjoint {a : E → ℝ} {u : V → ℝ}
    {x y : V} {A B : Set V} (h : G.SeparatedBoundaryConnections a u x A y B) :
    G.DisjointBoundaryConnections a x A y B := by
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hx, hy⟩ := h
  exact ⟨F, H, hFinF, hFinH, hdisj, fun e he ↦ (hF e he).1,
    fun e he ↦ (hH e he).1, hx, hy⟩

omit [Fintype E] in
/-- A tested edge crossing the potential gap belongs to neither certificate.
Changing only that edge therefore preserves the disjoint connections. This is
the step allowing opened-configuration certificates to survive closing it. -/
theorem SeparatedBoundaryConnections.change_crossing_edge {a b : E → ℝ} {u : V → ℝ}
    {x y : V} {A B : Set V} (h : G.SeparatedBoundaryConnections a u x A y B)
    (hxy : u x < u y) (e : E)
    (hends : (G.tail e = x ∧ G.head e = y) ∨ (G.tail e = y ∧ G.head e = x))
    (hab : ∀ f, f ≠ e → b f = a f) : G.DisjointBoundaryConnections b x A y B := by
  classical
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hx, hy⟩ := h
  have heF : e ∉ F := by
    intro he
    rcases hends with hends | hends
    · have hb : u y ≤ u x := by simpa only [hends.2] using (hF e he).2.2
      exact (not_le_of_gt hxy) hb
    · have hb : u y ≤ u x := by simpa only [hends.1] using (hF e he).2.1
      exact (not_le_of_gt hxy) hb
  have heH : e ∉ H := by
    intro he
    rcases hends with hends | hends
    · have hb : u y ≤ u x := by simpa only [hends.1] using (hH e he).2.1
      exact (not_le_of_gt hxy) hb
    · have hb : u y ≤ u x := by simpa only [hends.2] using (hH e he).2.2
      exact (not_le_of_gt hxy) hb
  have hFne (f : E) (hf : f ∈ F) : f ≠ e := fun hfe ↦ heF (hfe ▸ hf)
  have hHne (f : E) (hf : f ∈ H) : f ≠ e := fun hfe ↦ heH (hfe ▸ hf)
  have hweightsF : edgeRestrictedWeights b F = edgeRestrictedWeights a F := by
    funext f
    by_cases hf : f ∈ F
    · simp [edgeRestrictedWeights, hf, hab f (hFne f hf)]
    · simp [edgeRestrictedWeights, hf]
  have hweightsH : edgeRestrictedWeights b H = edgeRestrictedWeights a H := by
    funext f
    by_cases hf : f ∈ H
    · simp [edgeRestrictedWeights, hf, hab f (hHne f hf)]
    · simp [edgeRestrictedWeights, hf]
  refine ⟨F, H, hFinF, hFinH, hdisj, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [hab f (hFne f hf)]
    exact (hF f hf).1
  · intro f hf
    rw [hab f (hHne f hf)]
    exact (hH f hf).1
  · rw [hweightsF]
    exact hx
  · rw [hweightsH]
    exact hy

/-- A lower-potential vertex has a sublevel connection to the low face, and a
higher-potential vertex has a superlevel connection to the high face. Endpoint
boundary access supplies the required potential bounds; no global range bound
or openness of an edge joining the two starting points is assumed. -/
theorem IsHarmonic.separatedBoundaryConnections_of_lt {a : E → ℝ} {u : V → ℝ}
    {low high : Set V} {lo hi : ℝ} {x y : V}
    (hu : G.IsHarmonic a (low ∪ high) u) (ha : ∀ e, 0 ≤ a e)
    (hlohi : lo ≤ hi)
    (hlow : ∀ v ∈ low, u v = lo) (hhigh : ∀ v ∈ high, u v = hi)
    (hx : ∃ z ∈ low ∪ high, (G.positiveGraph a Set.univ).Reachable x z)
    (hy : ∃ z ∈ low ∪ high, (G.positiveGraph a Set.univ).Reachable y z)
    (hxy : u x < u y) : G.SeparatedBoundaryConnections a u x low y high := by
  obtain ⟨zx, hzx, hxz⟩ := hx
  obtain ⟨zy, hzy, hyz⟩ := hy
  obtain ⟨bx, hbx, hpathx⟩ := hu.sublevel_reaches_boundary G ha hxz hzx
  obtain ⟨bY, hby, hpathy⟩ := hu.superlevel_reaches_boundary G ha hyz hzy
  have hvalx : u bx ≤ u x := G.positiveGraph_reachable_mem (S := {v | u v ≤ u x})
    (show u x ≤ u x from le_rfl) hpathx
  have hvaly : u y ≤ u bY := G.positiveGraph_reachable_mem (S := {v | u y ≤ u v})
    (show u y ≤ u y from le_rfl) hpathy
  have hlo_x : lo ≤ u x := by
    rcases hbx with hlow' | hhigh'
    · rw [hlow bx hlow'] at hvalx
      exact hvalx
    · rw [hhigh bx hhigh'] at hvalx
      exact hlohi.trans hvalx
  have hhi_y : u y ≤ hi := by
    rcases hby with hlow' | hhigh'
    · rw [hlow bY hlow'] at hvaly
      exact hvaly.trans hlohi
    · rw [hhigh bY hhigh'] at hvaly
      exact hvaly
  have hbxlow : bx ∈ low := by
    rcases hbx with hlow' | hhigh'
    · exact hlow'
    · rw [hhigh bx hhigh'] at hvalx
      linarith
  have hbyhigh : bY ∈ high := by
    rcases hby with hlow' | hhigh'
    · rw [hlow bY hlow'] at hvaly
      linarith
    · exact hhigh'
  have hdisj : Disjoint {v | u v ≤ u x} {v | u y ≤ u v} := by
    apply Set.disjoint_left.mpr
    intro v hvx hvy
    exact (not_lt_of_ge (hvy.trans hvx)) hxy
  refine ⟨G.positiveEdgesInside a {v | u v ≤ u x},
    G.positiveEdgesInside a {v | u y ≤ u v}, Set.toFinite _, Set.toFinite _,
    G.positiveEdgesInside_disjoint hdisj, ?_, ?_, ?_, ?_⟩
  · exact fun e he ↦ ⟨he.1, he.2.1, he.2.2⟩
  · exact fun e he ↦ ⟨he.1, he.2.1, he.2.2⟩
  · exact ⟨bx, hbxlow, SimpleGraph.Reachable.mono (G.positiveGraph_le_edgeRestricted _ _) hpathx⟩
  · exact ⟨bY, hbyhigh, SimpleGraph.Reachable.mono (G.positiveGraph_le_edgeRestricted _ _) hpathy⟩

theorem IsHarmonic.disjointBoundaryConnections_of_lt {a : E → ℝ} {u : V → ℝ}
    {low high : Set V} {lo hi : ℝ} {x y : V}
    (hu : G.IsHarmonic a (low ∪ high) u) (ha : ∀ e, 0 ≤ a e)
    (hlohi : lo ≤ hi)
    (hlow : ∀ v ∈ low, u v = lo) (hhigh : ∀ v ∈ high, u v = hi)
    (hx : ∃ z ∈ low ∪ high, (G.positiveGraph a Set.univ).Reachable x z)
    (hy : ∃ z ∈ low ∪ high, (G.positiveGraph a Set.univ).Reachable y z)
    (hxy : u x < u y) : G.DisjointBoundaryConnections a x low y high :=
  (hu.separatedBoundaryConnections_of_lt G ha hlohi hlow hhigh hx hy hxy).to_disjoint G

/-- The deterministic content of `lem.two_arm`: unequal endpoint potentials
force disjoint open connections to opposite boundary faces. The tested
endpoints need not be joined by an open edge. -/
theorem IsHarmonic.two_arm {a : E → ℝ} {u : V → ℝ}
    {low high : Set V} {lo hi : ℝ} {x y : V}
    (hu : G.IsHarmonic a (low ∪ high) u) (ha : ∀ e, 0 ≤ a e)
    (hlohi : lo ≤ hi)
    (hlow : ∀ v ∈ low, u v = lo) (hhigh : ∀ v ∈ high, u v = hi)
    (hx : ∃ z ∈ low ∪ high, (G.positiveGraph a Set.univ).Reachable x z)
    (hy : ∃ z ∈ low ∪ high, (G.positiveGraph a Set.univ).Reachable y z)
    (hne : u x ≠ u y) :
    G.DisjointBoundaryConnections a x low y high ∨
      G.DisjointBoundaryConnections a x high y low := by
  obtain hlt | hgt := lt_or_gt_of_ne hne
  · exact Or.inl (hu.disjointBoundaryConnections_of_lt G ha hlohi hlow hhigh hx hy hlt)
  · exact Or.inr ((hu.disjointBoundaryConnections_of_lt G ha hlohi hlow hhigh hy hx hgt).symm G)

end NearCritical.Network
