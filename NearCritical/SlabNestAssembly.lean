module

public import NearCritical.SlabRootSite
public import NearCritical.SlabKfix

/-! Assembly of the slab nest rule from its edge part.

`resampledSlabNestInputs_of_edge`: the site and root parts of the rule
(`SlabRootSite`) and the fixed set (`SlabKfix`) are filled in. Given

* a child-nest function with its locality and its edge bound `pedge`,
* a predicate `Q` on (sample, site, nest) holding for the root nest, propagated
  by the child nest into a cube that passes the site test, and implying
  `slabNestJoined` for the resampled configuration,
* the pre-good probability bound at `p_c` (conclusion form of
  `Section10.pregood_eventually`), `κ{true} <= 1 - η`, `k <= countLower (2n)^(d-6)`
  and ambient bonds containing the cubes,

one obtains `ResampledSlabNestInputs`, hence (with
`slab_upper_of_resampledNestInputs`) prop.slab.upper. So what remains for
prop.slab.upper is exactly the edge data listed above.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set Function
open scoped Classical ENNReal
open Section10

variable {d : ℕ}

theorem resampledSlabNestInputs_of_edge {n R : ℕ} (hn : 0 < n) (s : I) (A : Finset (Bond d))
    (typ : TypicalParameters) (k : ℕ) (S : Set (Vertex d)) (F : Finset (Vertex d))
    (κ : Measure Bool)
    (hk : (k : ℝ) ≤ typ.countLower * (2 * (n : ℝ)) ^ (d - 6))
    (hA : ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A)
    {η : ℝ} (hκ : κ {true} ≤ ENNReal.ofReal (1 - η))
    (hpre : ∀ c : Vertex d, 1 - η ≤ ∫ ω, (if IsPreGoodCube typ n c ω then (1:ℝ) else 0)
      ∂(percolation d (criticalPoint d)))
    (childNest : boxBonds (centeredBox 2 R) → centeredBox 2 R → SlabNest d →
      (∀ i, rsΩ d n A R i) → Option (SlabNest d))
    (child_local : ∀ e z ℓ (x x' : ∀ i, rsΩ d n A R i), x (Sum.inr e) = x' (Sum.inr e) →
      x (Sum.inl z) = x' (Sum.inl z) → childNest e z ℓ x = childNest e z ℓ x')
    (pedge : ∀ e z ℓ (x : ∀ j, rsΩ d n A R j),
      κ {true} ≤ rsν d n A R (criticalPoint d) s (Sum.inr e)
        {y | (childNest e z ℓ (update x (Sum.inr e) y)).isSome = true})
    (Q : ((Bond d × Bool → Bool) × (Bond d × Bool → Bool)) → centeredBox 2 R →
      SlabNest d → Prop)
    (rootQ : ∀ q ℓ, slabRootNest d n A R typ k (rsΦ d n A R q) = some ℓ →
      Q q ⟨0, zero_mem_centeredBox_two R⟩ ℓ)
    (edgeQ : ∀ q e z ℓ ℓ',
      (z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) →
      slabSiteOK d n A R typ z (rsΦ d n A R q) = true →
      Q q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ →
      childNest e z ℓ (rsΦ d n A R q) = some ℓ' → Q q z ℓ')
    (join : ∀ q v ℓ, Q q v ℓ →
      slabNestJoined n S F (rsCfg d n R typ.heartRatio (slabKfix n A R) q) (v : Vertex 2)) :
    Nonempty (ResampledSlabNestInputs d n R (criticalPoint d) s S F κ) :=
  ⟨{ A := A
     cc := typ.heartRatio
     Kfix := slabKfix n A R
     hK := slabKfix_subset n A R
     L := SlabNest d
     Ru :=
       { rootNest := slabRootNest d n A R typ k
         siteOK := slabSiteOK d n A R typ
         childNest := childNest
         root_local := slabRootNest_local n A R typ k
         site_local := slabSiteOK_local n A R typ
         child_local := child_local }
     proot := slab_proot hn s A R typ k hk hA κ hκ hpre
     psite := slab_psite hn s A R typ hA κ hκ hpre
     pedge := pedge
     Q := Q
     rootQ := rootQ
     rootSite := fun q ℓ h => slabRootNest_site n A R typ k _ ℓ h
     edgeQ := edgeQ
     join := join }⟩

end NearCritical
