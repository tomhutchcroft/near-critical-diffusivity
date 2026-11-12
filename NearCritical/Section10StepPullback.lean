module

public import NearCritical.Section10ActualStepData

/-! Pull-back of a step's patches to the origin.

* `NestLayout.patch_pullback_regular`: for a realised reveal and a cube centred
  at `a + c0`, the points of a regular patch, translated by `-a`, are regular
  with respect to the pulled-back revealed set, the inner cube at `c0` and the
  boundary at `c0`. (Source cube: `c0 = 0`; target cube: `c0 = 2t e_i`.)
* `biUnion_pullback`, `pairwiseDisjoint_pullback`, `card_pullback`: unions,
  disjointness and cardinalities are unchanged by the pull-back.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

lemma translateSites_add_neg_cancel {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) :
    translateSites a (translateSites (-a) U) = U := by
  unfold translateSites
  rw [Finset.image_image]
  have h : ((fun x : Vertex d => a + x) ∘ fun x : Vertex d => -a + x) = id := by
    funext x
    simp
  rw [h, Finset.image_id]

lemma card_pullback {d : ℕ} (b : Vertex d) (U : Finset (Vertex d)) :
    (translateSites b U).card = U.card := card_translateSites b U

lemma biUnion_pullback {d : ℕ} (b : Vertex d) (cand : Finset (Finset (Vertex d)))
    (tgt : Finset (Vertex d) → Finset (Vertex d)) :
    cand.biUnion (fun c => translateSites b (tgt c)) =
      translateSites b (sprinklingTargetBoundary cand tgt) := by
  unfold sprinklingTargetBoundary translateSites
  exact Finset.biUnion_image.symm

lemma pairwiseDisjoint_pullback {d : ℕ} (b : Vertex d) (cand : Finset (Finset (Vertex d)))
    (tgt : Finset (Vertex d) → Finset (Vertex d))
    (h : Set.PairwiseDisjoint (cand : Set (Finset (Vertex d))) tgt) :
    Set.PairwiseDisjoint (cand : Set (Finset (Vertex d)))
      (fun c => translateSites b (tgt c)) := by
  intro C hC E hE hne
  exact (Finset.disjoint_image (add_right_injective b)).mpr (h hC hE hne)

variable {D d : ℕ} (Λ : NestLayout D d)

theorem NestLayout.patch_pullback_regular (z : Configuration d × Configuration d)
    {s : RSite D} (hs : s ∈ Λ.siteBox) (a c0 : Vertex d) (hc : Λ.center s = a + c0)
    (C : Finset (Vertex d)) (face : Fin d × Bool) (pl : Bool) :
    ∀ x ∈ translateSites (-a) (typicalRegularPatch Λ.typ Λ.t (Λ.center s)
        (Λ.revealConfig (refineReveal Λ.ρ₀ Λ.S₀ z)) C face pl),
      sourceRegularPoint (translateSites (-a) (Λ.Fat (Λ.ρ₀ z) s))
        (typicalInnerCube Λ.t c0) (typicalBoundary Λ.t c0)
        Λ.typ.regularRadius Λ.typ.regularTolerance x := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := (mem_translateSites_iff (-a) _ x).mp hx
  have hreg : sourceRegularPoint
      (heartClusterUnion (Λ.revealConfig (refineReveal Λ.ρ₀ Λ.S₀ z)) (Λ.Q s) (Λ.Hh s))
      (typicalInnerCube Λ.t (Λ.center s)) (typicalBoundary Λ.t (Λ.center s))
      Λ.typ.regularRadius Λ.typ.regularTolerance x' := (Finset.mem_filter.mp hx').2
  rw [Λ.heartUnion_revealConfig z hs, hc, typicalInnerCube_translate,
    typicalBoundary_translate] at hreg
  have key : sourceRegularPoint
      (translateSites a (translateSites (-a) (Λ.Fat (Λ.ρ₀ z) s)))
      (translateSites a (typicalInnerCube Λ.t c0)) (translateSites a (typicalBoundary Λ.t c0))
      Λ.typ.regularRadius Λ.typ.regularTolerance (a + (-a + x')) := by
    rw [translateSites_add_neg_cancel, add_neg_cancel_left]
    exact hreg
  exact (sourceRegularPoint_translate a _ _ _ _ _ _).mp key

end NearCritical.Section10
