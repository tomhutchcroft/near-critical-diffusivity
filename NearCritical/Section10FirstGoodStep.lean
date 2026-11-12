module

public import NearCritical.Section10LatticeRuleBuild

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

section StepView

variable {d : ℕ} (v : StepView d) (nest cand : Finset (Finset (Vertex d)))
  (src tgt : Finset (Vertex d) → Finset (Vertex d))

/-- The source samples its next nest only among offspring of the first good
representative in the fixed component order. -/
def svFirstGoodNext [LinearOrder (Finset (Vertex d))] (k : ℕ)
    (P : Finset (Finset (Finset (Vertex d)))) : Finset ↥P :=
  if h : (goodNestRepresentatives nest (svOffOf v nest cand src tgt) k).Nonempty then
    P.attach.filter fun N' => N'.val.card = k ∧
      N'.val ⊆ svOffOf v nest cand src tgt
        (nestRepresentative nest (svOffOf v nest cand src tgt) k h)
  else ∅

/-- The paper's representative choice always supplies a nonempty set of
next nests on a typical step. Each is also an admissible geometric move. -/
theorem svFirstGoodNext_spec [LinearOrder (Finset (Vertex d))]
    {face : Finset (Vertex d)} {k MOff Mcoal Kdiam : ℕ} (hk : 0 < k)
    (hcard : nest.card = k)
    (htyp : svTypical v nest cand src tgt face k MOff Mcoal Kdiam)
    (P : Finset (Finset (Finset (Vertex d)))) (hP : cand.powerset ⊆ P) :
    (svFirstGoodNext v nest cand src tgt k P).Nonempty ∧
      svFirstGoodNext v nest cand src tgt k P ⊆ svNext v nest cand src tgt k P := by
  let offspring := svOffOf v nest cand src tgt
  have htotal : 2 * k ^ 4 ≤ (nest.biUnion offspring).card := by
    have h := htyp.2.1
    rw [sprinklingOffspring_union] at h
    exact h
  have hgood := goodNestRepresentatives_nonempty nest offspring hk hcard htotal
  let rep := nestRepresentative nest offspring k hgood
  have hrep := nestRepresentative_spec nest offspring k hgood
  unfold svFirstGoodNext
  rw [dif_pos hgood]
  constructor
  · obtain ⟨N', hsub, hsize⟩ := nestRepresentative_next_nest nest offspring hk hgood
    have hmem : N' ∈ P := hP (Finset.mem_powerset.mpr
      (hsub.trans (svOffOf_subset_cand v nest cand src tgt rep)))
    exact ⟨⟨N', hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hsize, hsub⟩⟩
  · intro N' hN'
    obtain ⟨hattach, hsize, hsub⟩ := Finset.mem_filter.mp hN'
    unfold svNext
    exact Finset.mem_filter.mpr ⟨hattach, hsize, rep, hrep.1, hrep.2.1, hsub⟩

end StepView

namespace NestLayout
variable {D d : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]

/-- Keep the source's start and exit choices and restrict a moving step
to the next nests of its first good representative. -/
def offFirstGood (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X)
    (view : StepView d × Finset (Vertex d)) : Finset Λ.X :=
  if Λ.moveCtx G ℓ x ∧ Λ.moveTypical G ℓ x view then
    (svFirstGoodNext view.1 x.1.val (Λ.fam G ℓ.target)
      (Λ.src G ℓ x.2) (Λ.tgt G ℓ) Λ.k Λ.P) ×ˢ (Finset.univ : Finset Bool)
  else Λ.offσ G ℓ x view

theorem offFirstGood_nonempty (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X)
    (view : StepView d × Finset (Vertex d)) : (Λ.offFirstGood G ℓ x view).Nonempty := by
  unfold offFirstGood
  split_ifs with h
  · exact (svFirstGoodNext_spec _ _ _ _ _ Λ.hk h.1.2.2.2.2.1 h.2 Λ.P
      (Λ.fam_powerset_subset G h.1.2.2.2.1)).1.product Finset.univ_nonempty
  · exact Λ.offσ_nonempty G ℓ x view

theorem offFirstGood_subset (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X)
    (view : StepView d × Finset (Vertex d)) : Λ.offFirstGood G ℓ x view ⊆ Λ.offσ G ℓ x view := by
  unfold offFirstGood
  split_ifs with h
  · unfold offσ
    rw [if_pos h]
    exact Finset.product_subset_product_left
      (svFirstGoodNext_spec _ _ _ _ _ Λ.hk h.1.2.2.2.2.1 h.2 Λ.P
        (Λ.fam_powerset_subset G h.1.2.2.2.1)).2
  · intro y hy
    exact hy

/-- Lattice semantic rule with the source's fixed representative choice.
The local view, success event and probability inputs are inherited. -/
def ruleFirstGood (M : ℕ) (p q : unitInterval) (ϱ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ϱ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
          (Λ.view G.1 (routeLab M γ.position t) z))))
    (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)) :
    SemanticRule D M d p q ϱ κ Λ.X Λ.Φ₀ :=
  { Λ.rule M p q ϱ κ hκ hs hsiteProb with
    off := fun γ G t x z => Λ.offFirstGood G (routeLab M γ.position t) x
      (Λ.view G.1 (routeLab M γ.position t) z)
    hoff := fun γ G t x => (Λ.view_readsOnly G.1 (routeLab M γ.position t)).comp _
    hnonempty := fun γ G t x z _ => Λ.offFirstGood_nonempty G _ x _ }

end NestLayout

end NearCritical.Section10
