module

public import NearCritical.Section10LatticeRule

/-! The lattice nest rule as a `SemanticRule`.

* `revealConfig_eq`, `mem_S₀`: on an actual configuration, the configuration
  rebuilt from the refined reveal agrees with the critical layer on the explored
  bonds, and these contain the reveal bonds of each cube.
* `fam_eq`, `goodCube_iff`: so the typical clusters and pre-goodness read off
  the reveal are the actual ones.
* `NestLayout.rule`: the `SemanticRule`, with the two probability inputs `hs`
  (`prop.proba.k-nest`) and `hsiteProb` (`prop.proba.pregood`) as arguments.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

namespace NestLayout
variable {D d : ℕ} (Λ : NestLayout D d)

lemma revealConfig_eq (z : Configuration d × Configuration d) (e : Bond d)
    (he : ((false, e) : LBond d) ∈ Λ.S₀ (Λ.ρ₀ z)) :
    Λ.revealConfig (refineReveal Λ.ρ₀ Λ.S₀ z) e = z.1 e := by
  show (if h : ((false, e) : LBond d) ∈ Λ.S₀ (Λ.ρ₀ z) then
      ((Λ.S₀ (Λ.ρ₀ z)).restrict (layerVal z)) ⟨_, h⟩
    else if h' : ((false, e) : LBond d) ∈ (∅ : Finset (LBond d)) then false else false) = z.1 e
  rw [dif_pos he]
  rfl

lemma mem_S₀ (z : Configuration d × Configuration d) {s : RSite D} (hs : s ∈ Λ.siteBox)
    {e : Bond d}
    (he : e ∈ clusterRevealBonds (Λ.Q s) (heartClusterUnion z.1 (Λ.Q s) (Λ.Hh s))) :
    ((false, e) : LBond d) ∈ Λ.S₀ (Λ.ρ₀ z) := by
  have hinter := clusterFamilyUnion_inter_cube z.1 Λ.siteBox Λ.Q Λ.Hh Λ.hdisj s hs
  unfold S₀ revealBondsOf
  refine Finset.mem_image_of_mem _ ?_
  unfold clusterFamilyRevealBonds
  refine Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩
  show e ∈ clusterRevealBonds (Λ.Q s) (clusterFamilyUnion z.1 Λ.siteBox Λ.Q Λ.Hh ∩ Λ.Q s)
  rw [hinter]
  exact he

lemma fam_eq (z : Configuration d × Configuration d) {s : RSite D} (hs : s ∈ Λ.siteBox) :
    Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) s = typicalClusterFamily Λ.typ Λ.t (Λ.center s) z.1 :=
  (typicalClusterFamily_eq_of_union_reveal_agree Λ.typ Λ.t (Λ.center s) _ z.1
    (Λ.revealConfig (refineReveal Λ.ρ₀ Λ.S₀ z)) rfl
    (fun e he => (Λ.revealConfig_eq z e (Λ.mem_S₀ z hs he)).symm)).symm

lemma goodCube_iff (z : Configuration d × Configuration d) {s : RSite D}
    (hs : s ∈ Λ.siteBox) :
    Λ.goodCube (refineReveal Λ.ρ₀ Λ.S₀ z) s ↔ IsPreGoodCube Λ.typ Λ.t (Λ.center s) z.1 :=
  (isPreGoodCube_iff_of_union_reveal_agree Λ.typ Λ.t (Λ.center s) _ z.1
    (Λ.revealConfig (refineReveal Λ.ρ₀ Λ.S₀ z)) rfl
    (fun e he => (Λ.revealConfig_eq z e (Λ.mem_S₀ z hs he)).symm)).symm

/-- The lattice nest rule. -/
def rule (M : ℕ) (p q : unitInterval) (ϱ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ϱ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
          (Λ.view G.1 (routeLab M γ.position t) z))))
    (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)) :
    SemanticRule D M d p q ϱ κ Λ.X Λ.Φ₀ where
  ρ₀ := Λ.ρ₀
  S₀ := Λ.S₀
  hρ₀ := criticalReveal_atom_isLocal Λ.siteBox Λ.Q Λ.Hh Λ.hdisj (fun j _ => Λ.hH j)
  Bl₀ := Λ.Bl₀
  hBl₀ := Λ.hBl₀
  hS₀ := Λ.hS₀
  succ := fun γ G t x z => Λ.succσ G (routeLab M γ.position t) x
    (Λ.view G.1 (routeLab M γ.position t) z)
  off := fun γ G t x z => Λ.offσ G (routeLab M γ.position t) x
    (Λ.view G.1 (routeLab M γ.position t) z)
  hsucc := fun γ G t x => (Λ.view_readsOnly G.1 (routeLab M γ.position t)).comp _
  hoff := fun γ G t x => (Λ.view_readsOnly G.1 (routeLab M γ.position t)).comp _
  hnonempty := fun γ G t x z _ => Λ.offσ_nonempty G _ x _
  hs := hs
  Es := Λ.Es
  hEs := Λ.hEs
  site := Λ.siteEvent
  hsite := Λ.hsite
  hκ := hκ
  hsiteProb := hsiteProb
  good := fun G s => s ∈ Λ.siteBox → Λ.goodCube G s
  hgood := fun z s => by
    unfold siteEvent
    constructor
    · intro h hs
      exact (Λ.goodCube_iff z hs).mpr (h hs)
    · intro h hs
      exact (Λ.goodCube_iff z hs).mp (h hs)
  x₀ := fun _ _ => (⟨∅, Finset.empty_mem_powerset _⟩, true)

end NestLayout
end NearCritical.Section10
