module

public import NearCritical.SlabTubeChart
public import NearCritical.SlabTubeResampleAgree
public import NearCritical.SlabTubeChartLaw

/-! The chart preserves which bonds are deleted by an endpoint reveal.
This compares the chart used by the probability bound with the chart of the
actual composite configuration. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

theorem slabChartBond_endpoints {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2)
    (rev : Bool) (b : Bond d) :
    let f := slabChartVertex hd n e rev
    let c := slabChartBond hd n e rev b
    (c.1 = f b.1 ∧ bondTip c = f (bondTip b)) ∨
      (c.1 = f (bondTip b) ∧ bondTip c = f b.1) := by
  cases rev
  · exact Or.inl ⟨rfl, bondTip_translate _ _⟩
  · let i := Fin.castLE hd e.2
    let a : Vertex d := coarseShift n (bondTip e)
    change ((translateBond a (reflBond i b)).1 = a + reflVertex i b.1 ∧
        bondTip (translateBond a (reflBond i b)) = a + reflVertex i (bondTip b)) ∨
      ((translateBond a (reflBond i b)).1 = a + reflVertex i (bondTip b) ∧
        bondTip (translateBond a (reflBond i b)) = a + reflVertex i b.1)
    rw [bondTip_translate]
    by_cases h : b.2 = i
    · have hr : reflBond i b = (reflVertex i (bondTip b),i) := if_pos h
      rw [hr, bondTip_reflBond_eq i b h]
      exact Or.inr ⟨rfl,rfl⟩
    · have hr : reflBond i b = (reflVertex i b.1,b.2) := if_neg h
      rw [hr, bondTip_reflBond_ne i b h]
      exact Or.inl ⟨rfl,rfl⟩

theorem slabChartBond_mem_clusterReveal_iff {d : ℕ} (hd : 2 ≤ d) (n : ℕ)
    (e : Bond 2) (rev : Bool) (Q F Q' F' : Finset (Vertex d))
    (hQ : ∀ x, x ∈ Q ↔ slabChartVertex hd n e rev x ∈ Q')
    (hF : ∀ x, x ∈ F ↔ slabChartVertex hd n e rev x ∈ F') (b : Bond d) :
    slabChartBond hd n e rev b ∈ clusterRevealBonds Q' F' ↔ b ∈ clusterRevealBonds Q F := by
  rw [mem_clusterRevealBonds, mem_clusterRevealBonds]
  rcases slabChartBond_endpoints hd n e rev b with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [h₁,h₂, ← hQ, ← hQ, ← hF, ← hF]
  · rw [h₁,h₂, ← hQ, ← hQ, ← hF, ← hF, or_comm]
    tauto

/-- The chart of the actual edge block and the chart of the composite
sample give the same step view with corresponding endpoint masks. -/
theorem slab_chart_stepView_resample_eq {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (R : ℕ) (A : Finset (Bond d)) (cc : ℝ) (e : boxBonds (centeredBox 2 R)) (rev : Bool)
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (M L V Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hA : ∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A) :
    let i := Fin.castLE hd e.1.2
    let T := sprinklingTube i n (-(5:ℝ)/8) (5/8)
    let Q := fun v => typicalCube n (coarseShift (d := d) n v)
    let H := fun v => typicalHeart n (coarseShift (d := d) n v) cc
    let F := fun v => heartClusterUnion (criticalLayer q.1) (Q v) (H v)
    let u := e.1.1
    let v := bondTip e.1
    let a := if rev then v else u
    let b := if rev then u else v
    let f := slabChartVertex hd n e.1 rev
    let g := slabChartBond hd n e.1 rev
    let ω := resampleLayers (centeredBox 2 R) Q H (slabKfix n A R) q
    (M : Set (Vertex d)) ⊆ T → (L : Set (Vertex d)) ⊆ T → (V : Set (Vertex d)) ⊆ T →
    Disjoint L Q₃ → Disjoint V Q₁ → Disjoint M Q₁ → Disjoint M Q₃ →
    (∀ x, x ∈ Q₁ ↔ f x ∈ Q a) → (∀ x, x ∈ F₁ ↔ f x ∈ F a) →
    (∀ x, x ∈ Q₃ ↔ f x ∈ Q b) → (∀ x, x ∈ F₃ ↔ f x ∈ F b) →
    stepView M L V Q₁ F₁ Q₃ F₃ (pullbackLayerPair g (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e)))) =
      stepView M L V Q₁ F₁ Q₃ F₃ (pullbackLayerPair g (criticalLayer ω, sprinkleLayer q.1)) := by
  intro i T Q H F u v a b f g ω hM hL hV hLV hVu hMu hMv hQ₁ hF₁ hQ₃ hF₃
  apply stepView_readsOnly
  have hTube {U : Finset (Vertex d)} {c : Bond d}
      (hU : (U : Set (Vertex d)) ⊆ T) (hc : c ∈ internalBondSet U) :
      bondIn (slabTube n e.1.1 e.1.2) (g c) :=
    slabChartBond_mem_tube hd n e.1 rev c
      ⟨hU ((mem_internalBondSet U c).mp hc).1, hU ((mem_internalBondSet U c).mp hc).2⟩
  have hAvoid {U W E : Finset (Vertex d)} {c : Bond d}
      (hU : Disjoint U W) (hc : c ∈ internalBondSet U) : c ∉ clusterRevealBonds W E := fun h =>
    Finset.disjoint_left.mp hU ((mem_internalBondSet U c).mp hc).1
      ((mem_clusterRevealBonds W E c).mp h).1
  have hCritical (c : Bond d) (hc : bondIn (slabTube n e.1.1 e.1.2) (g c))
      (hc₁ : c ∉ clusterRevealBonds Q₁ F₁) (hc₃ : c ∉ clusterRevealBonds Q₃ F₃) :
      (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e))).1 (g c) = criticalLayer ω (g c) := by
    have h₁ : g c ∉ heartRevealSet (Q a) (H a) (criticalLayer q.1) := fun h =>
      hc₁ ((slabChartBond_mem_clusterReveal_iff hd n e.1 rev Q₁ F₁ (Q a) (F a) hQ₁ hF₁ c).1 h)
    have h₃ : g c ∉ heartRevealSet (Q b) (H b) (criticalLayer q.1) := fun h =>
      hc₃ ((slabChartBond_mem_clusterReveal_iff hd n e.1 rev Q₃ F₃ (Q b) (F b) hQ₃ hF₃ c).1 h)
    cases rev
    · exact slabTubePair_critical_agrees hd hn R A cc e q _ (hA _ hc) hc h₁ h₃
    · exact slabTubePair_critical_agrees hd hn R A cc e q _ (hA _ hc) hc h₃ h₁
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · obtain ⟨hi, hr⟩ := Finset.mem_sdiff.mp hc
        exact hCritical c (hTube hL hi) hr (hAvoid hLV hi)
      · obtain ⟨hi, hr⟩ := Finset.mem_sdiff.mp hc
        exact hCritical c (hTube hV hi) (hAvoid hVu hi) hr
    · exact hCritical c (hTube hM hc) (hAvoid hMu hc) (hAvoid hMv hc)
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
    exact slabTubePair_sprinkle_agrees n R A e q (g c) (hA _ (hTube hM hc)) (hTube hM hc)

end NearCritical
