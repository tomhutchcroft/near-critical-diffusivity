module

public import NearCritical.Section10SemanticNestRule
public import NearCritical.Section10ChainPath
public import NearCritical.ChemicalCrossingAssembly

/-! Surviving chains of a semantic rule carry a chain certificate.

`semanticRule_certificate`: for an actual configuration pair `z` and a route
`γ`, suppose the configuration-level success/offspring of the rule satisfy
* `hinit`: the start step produces a state satisfying the invariant;
* `hbottom`: every cluster of an initial state has a boundary point on the
  bottom face of the box;
* `hstep`: a successful step is a stay or a bridge step (as in
  `chainSurvives_geometry`);
* `hexit`: a successful exit step gives an open edge to the exit face.
Then a surviving chain puts the supercritical configuration `z.1 OR z.2` in
`chemicalChainCertificateEvent`. All four are deterministic statements about
the actual objects; this theorem is the bookkeeping of `lem.nw.path`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem semanticRule_certificate {D M d : ℕ} {p q : unitInterval} {ϱ κ : ℝ} {X Φ₀ : Type}
    [Fintype X] [Fintype Φ₀] (R : SemanticRule D M d p q ϱ κ X Φ₀) (hM : 1 ≤ M)
    (z : Configuration d × Configuration d) (γ : SourceRoute D M)
    (hsurv : ChainSurvives (R.toNestRule.kernel γ (R.toNestRule.ρ z)) (2 * M) 0
      (R.toNestRule.x₀ γ (R.toNestRule.ρ z)) z)
    {ι : Type*} (cl : X → Set ι) (bd : ℕ → ι → Set (Vertex d)) (Inv : ℕ → X → Prop)
    (aC : Vertex d) (r : ℕ) (i : Fin d) (A B : ℝ)
    (hinit : ∀ y, R.succ γ (refineReveal R.ρ₀ R.S₀ z) 0 (R.x₀ γ (refineReveal R.ρ₀ R.S₀ z)) z →
      y ∈ R.off γ (refineReveal R.ρ₀ R.S₀ z) 0 (R.x₀ γ (refineReveal R.ρ₀ R.S₀ z)) z →
      Inv 1 y)
    (hbottom : ∀ y rep, Inv 1 y → rep ∈ cl y →
      ∃ pt ∈ bd 1 rep, ∃ x ∈ chemicalBottomFace d r i, pt = aC + x)
    (hexit : ∀ x y, Inv (2 * M - 1) x →
      R.succ γ (refineReveal R.ρ₀ R.S₀ z) (2 * M - 1) x z →
      y ∈ R.off γ (refineReveal R.ρ₀ R.S₀ z) (2 * M - 1) x z →
      ∃ rep ∈ cl x, ∃ v w, v ∈ bd (2 * M - 1) rep ∧
        (restrictedGraph (sprinkleOrConfiguration z.1 z.2)
          (translateSites aC (chemicalCrossingSupport d r i) : Set (Vertex d))).Adj v w ∧
        (∃ z' ∈ chemicalExitFace d r i, w = aC + z') ∧
        ∀ pt ∈ bd (2 * M - 1) rep, ∃ C : SimpleGraph (Vertex d),
          C ≤ restrictedGraph (sprinkleOrConfiguration z.1 z.2)
            (translateSites aC (chemicalCrossingSupport d r i) : Set (Vertex d)) ∧
          BoundedIntrinsicConnection C pt v A)
    (hstep : ∀ t, 1 ≤ t → t < 2 * M - 1 → ∀ x y, Inv t x →
      R.succ γ (refineReveal R.ρ₀ R.S₀ z) t x z →
      y ∈ R.off γ (refineReveal R.ρ₀ R.S₀ z) t x z →
      Inv (t+1) y ∧ ((cl y = cl x ∧ ∀ c ∈ cl x, bd t c ⊆ bd (t+1) c) ∨
        ∃ rep ∈ cl x,
          (∀ c' ∈ cl y, ∃ u ∈ bd t rep, ∃ v ∈ bd (t+1) c', ∃ Dg : SimpleGraph (Vertex d),
            Dg ≤ restrictedGraph (sprinkleOrConfiguration z.1 z.2)
              (translateSites aC (chemicalCrossingSupport d r i) : Set (Vertex d)) ∧
            BoundedIntrinsicConnection Dg u v B) ∧
          ∀ pt ∈ bd t rep, ∀ u ∈ bd t rep, ∃ C : SimpleGraph (Vertex d),
            C ≤ restrictedGraph (sprinkleOrConfiguration z.1 z.2)
              (translateSites aC (chemicalCrossingSupport d r i) : Set (Vertex d)) ∧
            BoundedIntrinsicConnection C pt u A)) :
    sprinkleOrConfiguration z.1 z.2 ∈ chemicalChainCertificateEvent aC r i A B M := by
  have h2M : 2 * M = (2 * M - 1) + 1 := by omega
  rw [h2M] at hsurv
  obtain ⟨y1, hk0, hrest⟩ := hsurv
  obtain ⟨hs0, ho0⟩ := R.kernel_pos γ z 0 _ y1 hk0
  have hInv1 : Inv 1 y1 := hinit y1 hs0 ho0
  obtain ⟨rep, hrep, n, yend, w, hn, hadj, ⟨z', hz', hwz⟩, hgeo⟩ :=
    chainSurvives_geometry
      (restrictedGraph (sprinkleOrConfiguration z.1 z.2)
        (translateSites aC (chemicalCrossingSupport d r i) : Set (Vertex d))) A B
      (R.toNestRule.kernel γ (R.toNestRule.ρ z)) z cl bd (fun t x => 1 ≤ t ∧ Inv t x)
      (fun w => ∃ z' ∈ chemicalExitFace d r i, w = aC + z') (2 * M - 1)
      (fun x y hI hk => by
        obtain ⟨h1, h2⟩ := R.kernel_pos γ z _ x y hk
        exact hexit x y hI.2 h1 h2)
      (fun t ht x y hI hk => by
        obtain ⟨h1, h2⟩ := R.kernel_pos γ z t x y hk
        obtain ⟨h3, h4⟩ := hstep t hI.1 ht x y hI.2 h1 h2
        exact ⟨⟨by omega, h3⟩, h4⟩)
      (2 * M - 1) 1 y1 (by omega) (by omega) ⟨le_refl 1, hInv1⟩ hrest
  obtain ⟨pt, hpt, x, hx, hptx⟩ := hbottom y1 rep hInv1 hrep
  have hg := hgeo pt hpt
  rw [hptx] at hg
  rw [hwz] at hadj
  exact ⟨x, hx, z', hz', yend, n, by omega, hg, hadj⟩

end NearCritical.Section10
