module

public import NearCritical.Section10LatticeRuleBuild
public import NearCritical.Section10PairOverlap

/-! The synchronous pair chain of the lattice nest rule: blocks and locality.

For two routes `γ`, `γ'` the pair chain at time `t` reads
`pairBlock = Bl₀ F (label of γ at t) ∪ Bl₀ F (label of γ' at t)`.

* `pairBlock_disjoint`: blocks at different times are disjoint (labels at
  different times have different ranks, hence disjoint regions).
* `pairBlock_fresh`: they avoid the explored bonds.
* `pairKernel_isLocal`: the pair kernel of the rule is local on its block.

These are the structural hypotheses `_hB`, `_hSB`, `_hK` of
`sourceRoute_energy_le` for the lattice rule.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

namespace NestLayout
variable {D d : ℕ} (Λ : NestLayout D d)

/-- Block read by the pair chain of two routes at time `t`. -/
def pairBlock (M : ℕ) (γ γ' : SourceRoute D M) (F : Λ.Φ₀) (t : ℕ) : Finset (LBond d) :=
  Λ.Bl₀ F (routeLab M γ.position t) ∪ Λ.Bl₀ F (routeLab M γ'.position t)

theorem pairBlock_disjoint {M : ℕ} (hM : 1 ≤ M) (γ γ' : SourceRoute D M) (F : Λ.Φ₀)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Λ.pairBlock M γ γ' F i) (Λ.pairBlock M γ γ' F j) := by
  have hne : ∀ (X Y : ℕ → Fin D → ℤ), routeLab M X i ≠ routeLab M Y j := by
    intro X Y h
    have := congrArg RouteLabel.rank h
    rw [rank_routeLab hM, rank_routeLab hM] at this
    exact hij this
  unfold pairBlock
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
  exact ⟨⟨Λ.hBl₀ F _ _ (hne _ _), Λ.hBl₀ F _ _ (hne _ _)⟩,
    Λ.hBl₀ F _ _ (hne _ _), Λ.hBl₀ F _ _ (hne _ _)⟩

theorem pairBlock_fresh (M : ℕ) (γ γ' : SourceRoute D M) (F : Λ.Φ₀) (t : ℕ) :
    Disjoint (Λ.S₀ F) (Λ.pairBlock M γ γ' F t) := by
  unfold pairBlock
  rw [Finset.disjoint_union_right]
  exact ⟨Λ.hS₀ F _, Λ.hS₀ F _⟩

theorem pairKernel_isLocal (M : ℕ) (p q : unitInterval) (ϱ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ϱ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
          (Λ.view G.1 (routeLab M γ.position t) z))))
    (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x y : Λ.X × Λ.X) :
    IsLocal (Λ.pairBlock M γ γ' G.1 t)
      (pairKernel ((Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ G)
        ((Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ' G) t x y) := by
  unfold pairKernel pairBlock
  exact (stepKernel_isLocal _ _ _ _ _).mul_union (stepKernel_isLocal _ _ _ _ _)

end NestLayout
end NearCritical.Section10
