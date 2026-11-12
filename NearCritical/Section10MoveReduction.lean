module

public import NearCritical.Section10LatticeRule

/-! `prop.proba.k-nest`: the offspring upper bound and the coalescence bound
are deterministic.

In the typical-bridge event of a lattice step, the offspring are among the
candidates (typical clusters of the target cube) and the coalescing sites lie
on the source face. Since `M_off` and `M_coal` do not enter the time-constant
bound, they can be taken at least these two cardinalities, and then
typicality is exactly: at least `2 k^4` offspring and intrinsic diameter at
most `K_diam` (`svTypical_stepView_iff`, `NestLayout.moveTypical_view_iff`).
So `hmove` needs no probabilistic bound for `M_off` or `M_coal`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem svTypical_stepView_iff {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (z : Configuration d × Configuration d) (nest cand : Finset (Finset (Vertex d)))
    (src tgt : Finset (Vertex d) → Finset (Vertex d)) (face : Finset (Vertex d))
    (k MOff Mcoal Kdiam : ℕ) (hMOff : cand.card ≤ MOff) (hMcoal : face.card ≤ Mcoal) :
    svTypical (stepView M L R Q₁ F₁ Q₃ F₃ z) nest cand src tgt face k MOff Mcoal Kdiam ↔
      (10 ≤ 2 * k ^ 4 ∧
        2 * k ^ 4 ≤ (sprinklingOffspring (stepView M L R Q₁ F₁ Q₃ F₃ z).1
          (stepView M L R Q₁ F₁ Q₃ F₃ z).2.1 (sprinklingTargetBoundary nest src) cand tgt
          (svPivots (stepView M L R Q₁ F₁ Q₃ F₃ z) nest cand src tgt)).card ∧
        svDiameter (stepView M L R Q₁ F₁ Q₃ F₃ z) nest cand src tgt ≤ Kdiam) := by
  have hoff : (sprinklingOffspring (stepView M L R Q₁ F₁ Q₃ F₃ z).1
      (stepView M L R Q₁ F₁ Q₃ F₃ z).2.1 (sprinklingTargetBoundary nest src) cand tgt
      (svPivots (stepView M L R Q₁ F₁ Q₃ F₃ z) nest cand src tgt)).card ≤ MOff :=
    (Finset.card_le_card (fun c hc =>
      ((mem_sprinklingOffspring _ _ _ _ _ _ c).mp hc).1)).trans hMOff
  have hcoal : ((stepView M L R Q₁ F₁ Q₃ F₃ z).2.2.2 (sprinklingTargetBoundary nest src) face
      (sprinklingTargetBoundary cand tgt)).card ≤ Mcoal := by
    refine (Finset.card_le_card ?_).trans hMcoal
    show bridgeCoalescingSites z.1 (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs M)
      L R Q₁ F₁ Q₃ F₃ (sprinklingTargetBoundary nest src) face
      (sprinklingTargetBoundary cand tgt) ⊆ face
    intro x hx
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
  unfold svTypical IsTypicalSprinklingBridge
  constructor
  · rintro ⟨h1, h2, _, _, h5⟩
    exact ⟨h1, h2, h5⟩
  · rintro ⟨h1, h2, h5⟩
    exact ⟨h1, h2, hoff, hcoal, h5⟩

variable {D d : ℕ} (Λ : NestLayout D d)

/-- Typicality of a lattice step with deterministic `M_off`, `M_coal`. -/
theorem NestLayout.moveTypical_view_iff (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X)
    (z : Configuration d × Configuration d)
    (hMOff : (Λ.fam G ℓ.target).card ≤ Λ.MOff)
    (hMcoal : (Λ.faceAll G ℓ x.2).card ≤ Λ.Mcoal) :
    Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z) ↔
      (10 ≤ 2 * Λ.k ^ 4 ∧
        2 * Λ.k ^ 4 ≤ (sprinklingOffspring (Λ.view G.1 ℓ z).1.1 (Λ.view G.1 ℓ z).1.2.1
          (sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)) (Λ.fam G ℓ.target) (Λ.tgt G ℓ)
          (svPivots (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
            (Λ.tgt G ℓ))).card ∧
        svDiameter (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
          (Λ.tgt G ℓ) ≤ Λ.Kdiam) :=
  svTypical_stepView_iff _ _ _ _ _ _ _ z _ _ _ _ _ _ _ _ _ hMOff hMcoal

/-- The number of typical clusters of a cube is at most its volume. -/
theorem typicalClusterFamily_card_le_cube {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (z : Vertex d) (ω : Configuration d) :
    (typicalClusterFamily typ t z ω).card ≤ (typicalCube t z).card := by
  unfold typicalClusterFamily
  refine (Finset.card_filter_le _ _).trans ?_
  unfold finiteClusterFamily
  exact Finset.card_image_le

/-- Regular patches lie on the cube. -/
theorem typicalRegularPatch_subset_cube {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (z : Vertex d) (ω : Configuration d) (C : Finset (Vertex d)) (face : Fin d × Bool)
    (plus : Bool) : typicalRegularPatch typ t z ω C face plus ⊆ typicalCube t z := by
  intro x hx
  have h1 := (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2
  have h2 := (Finset.mem_filter.mp h1).1
  exact (Finset.mem_filter.mp h2).1

end NearCritical.Section10
