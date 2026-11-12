module

public import NearCritical.Section10SemanticRule

/-! A `NestRule` from configuration-level data.

`SemanticRule` is the form in which the source describes the construction:
* a base reveal `ρ₀` (the critical cluster union) with local atoms; the rule
  uses its refinement `⟨F, bits on the explored bonds⟩`;
* for each step, a success predicate `succ` and an offspring function `off` of
  the configuration pair, which only read the explored bonds and the block of
  the step;
* for each coarse site an event `site s` (the cube is pre-good), local on the
  bonds of the cube, of probability at least `1/kappa`, and decided by the
  refined reveal (`good`).

`SemanticRule.toNestRule` builds the `NestRule`. `kernel_pos` and `weight_pos`
translate back: a positive kernel means success and offspring membership for
the actual configuration; a positive weight means all cubes of the route are
good.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

structure SemanticRule (D M d : ℕ) (p q : unitInterval) (ϱ κ : ℝ) (X Φ₀ : Type)
    [Fintype X] [Fintype Φ₀] where
  ρ₀ : Configuration d × Configuration d → Φ₀
  S₀ : Φ₀ → Finset (LBond d)
  hρ₀ : ∀ F, IsLocal (S₀ F) (fun z => if ρ₀ z = F then (1:ℝ) else 0)
  Bl₀ : Φ₀ → RouteLabel D → Finset (LBond d)
  hBl₀ : ∀ F a b, a ≠ b → Disjoint (Bl₀ F a) (Bl₀ F b)
  hS₀ : ∀ F a, Disjoint (S₀ F) (Bl₀ F a)
  succ : SourceRoute D M → (Σ F : Φ₀, (S₀ F → Bool)) → ℕ → X →
    Configuration d × Configuration d → Prop
  off : SourceRoute D M → (Σ F : Φ₀, (S₀ F → Bool)) → ℕ → X →
    Configuration d × Configuration d → Finset X
  hsucc : ∀ γ G t x, ReadsOnly (S₀ G.1 ∪ Bl₀ G.1 (routeLab M γ.position t)) (succ γ G t x)
  hoff : ∀ γ G t x, ReadsOnly (S₀ G.1 ∪ Bl₀ G.1 (routeLab M γ.position t)) (off γ G t x)
  hnonempty : ∀ γ G t x z, succ γ G t x z → (off γ G t x z).Nonempty
  hs : ∀ γ G t x, ϱ⁻¹ ≤ localSuccessProbability p q (Bl₀ G.1 (routeLab M γ.position t))
    (bitSet G.2 (succ γ G t x))
  Es : RSite D → Finset (LBond d)
  hEs : ∀ a b, a ≠ b → Disjoint (Es a) (Es b)
  site : RSite D → Set (Configuration d × Configuration d)
  hsite : ∀ s, IsLocal (Es s) (fun z => if z ∈ site s then (1:ℝ) else 0)
  hκ : 0 < κ
  hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (site s)
  good : (Σ F : Φ₀, (S₀ F → Bool)) → RSite D → Prop
  hgood : ∀ z s, z ∈ site s ↔ good (refineReveal ρ₀ S₀ z) s
  x₀ : SourceRoute D M → (Σ F : Φ₀, (S₀ F → Bool)) → X

namespace SemanticRule
variable {D M d : ℕ} {p q : unitInterval} {ϱ κ : ℝ} {X Φ₀ : Type} [Fintype X] [Fintype Φ₀]

/-- The `NestRule` of a semantic rule. -/
def toNestRule (R : SemanticRule D M d p q ϱ κ X Φ₀) :
    NestRule D M d p q ϱ κ X (Σ F : Φ₀, (R.S₀ F → Bool)) where
  ρ := refineReveal R.ρ₀ R.S₀
  S := fun G => R.S₀ G.1
  hρ := fun G => by convert refineReveal_atom_isLocal R.ρ₀ R.S₀ R.hρ₀ G
  Bl := fun G => R.Bl₀ G.1
  hBl := fun G => R.hBl₀ G.1
  hS := fun G => R.hS₀ G.1
  a := fun γ G t x => bitSet G.2 (R.succ γ G t x)
  o := fun γ G t x b => R.off γ G t x (gluePair G.2 b)
  ho := fun γ G t x b hb => R.hnonempty γ G t x _ hb
  hs := R.hs
  Es := R.Es
  hEs := R.hEs
  u := fun s => normIndicator p q (R.site s)
  hu := fun s => normIndicator_isLocal p q (R.hsite s)
  hu0 := fun s z => normIndicator_nonneg p q (R.site s) z
  humean := fun s => normIndicator_mean p q (R.site s)
    (lt_of_lt_of_le (inv_pos.mpr R.hκ) (R.hsiteProb s))
  husq := fun s => normIndicator_sq p q (R.site s) R.hκ (R.hsiteProb s)
  w := fun γ G => ∏ s ∈ routeSites M γ.position,
    (if R.good G s then (coupledProb p q (R.site s))⁻¹ else 0)
  hw0 := fun γ G => Finset.prod_nonneg (fun s _ => by
    split_ifs
    · exact inv_nonneg.mpr (coupledProb_nonneg p q _)
    · exact le_refl _)
  hwu := fun γ z => Finset.prod_congr rfl (fun s _ => by
    unfold normIndicator
    by_cases h : z ∈ R.site s
    · rw [if_pos h, if_pos ((R.hgood z s).mp h), one_mul]
    · rw [if_neg h, if_neg (fun h' => h ((R.hgood z s).mpr h')), zero_mul])
  x₀ := R.x₀

/-- A positive kernel: the step succeeded for the actual configuration and the
new state is one of its offspring. -/
theorem kernel_pos (R : SemanticRule D M d p q ϱ κ X Φ₀) (γ : SourceRoute D M)
    (z : Configuration d × Configuration d) (t : ℕ) (x y : X)
    (h : 0 < R.toNestRule.kernel γ (refineReveal R.ρ₀ R.S₀ z) t x y z) :
    R.succ γ (refineReveal R.ρ₀ R.S₀ z) t x z ∧
      y ∈ R.off γ (refineReveal R.ρ₀ R.S₀ z) t x z := by
  obtain ⟨h1, h2⟩ := stepKernel_pos _ _ _ _ y z h
  constructor
  · exact (bitSet_iff (S := R.S₀ (R.ρ₀ z))
      (T := R.Bl₀ (R.ρ₀ z) (routeLab M γ.position t))
      (R.succ γ (refineReveal R.ρ₀ R.S₀ z) t x)
      (R.hsucc γ (refineReveal R.ρ₀ R.S₀ z) t x) z).mp h1
  · have h3 := glue_fun_eq (S := R.S₀ (R.ρ₀ z))
      (T := R.Bl₀ (R.ρ₀ z) (routeLab M γ.position t))
      (R.off γ (refineReveal R.ρ₀ R.S₀ z) t x)
      (R.hoff γ (refineReveal R.ρ₀ R.S₀ z) t x) z
    rw [← h3]
    exact h2

/-- A positive cube weight: every site of the route is good. -/
theorem weight_pos (R : SemanticRule D M d p q ϱ κ X Φ₀) (γ : SourceRoute D M)
    (z : Configuration d × Configuration d)
    (h : 0 < R.toNestRule.w γ (R.toNestRule.ρ z)) :
    ∀ s ∈ routeSites M γ.position, z ∈ R.site s := by
  intro s hs
  by_contra hns
  have hzero : R.toNestRule.w γ (R.toNestRule.ρ z) = 0 := by
    refine Finset.prod_eq_zero hs ?_
    show (if R.good (refineReveal R.ρ₀ R.S₀ z) s then (coupledProb p q (R.site s))⁻¹
      else (0:ℝ)) = 0
    exact if_neg (fun hg => hns ((R.hgood z s).mpr hg))
  rw [hzero] at h
  exact lt_irrefl _ h

end SemanticRule
end NearCritical.Section10
