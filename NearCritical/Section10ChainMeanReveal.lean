module

public import NearCritical.Section10ChainMean
public import NearCritical.Section10ClusterUnionReveal

/-! Source `lem.nw.mean` with the ACTUAL reveal: the critical layer's union `G`
of heart clusters over a finite family of disjoint cubes.

Coupling: `z.1` is the critical configuration and `z.2` the independent sprinkle
(the form used by the verified Section 9 theorems). The reveal is
`G(z) = clusterFamilyUnion z.1 s Q H`. Its atoms are local on the explored bonds
`clusterFamilyRevealBonds`, by the existing cylinder theorem.

`nestChain_mean_of_rule`: for ANY step rule (success set `a` and offspring map
`o` on the fresh bits of each step, both allowed to depend on the revealed `G`
and on the current state) whose blocks avoid the explored bonds and each other,
the weight `zeta` built from the normalised indicators and uniform offspring
choices satisfies `E[w(G) * zeta] = E[w(G)]`. With `w = omega_Gamma` this is
`lem.nw.mean` for one route; the rule itself (bridge typicality, offspring)
is not constructed here.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators
variable {J : Type*}

/-- Possible values of the revealed union: subsets of the union of the cubes. -/
abbrev RevealValue {d : ℕ} (s : Finset J) (Q : J → Finset (Vertex d)) : Type :=
  ↥((s.biUnion Q).powerset)

lemma clusterFamilyUnion_subset_cubes {d : ℕ} (ω : Configuration d) (s : Finset J)
    (Q H : J → Finset (Vertex d)) : clusterFamilyUnion ω s Q H ⊆ s.biUnion Q := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨j, hj, heartClusterUnion_subset ω (Q j) (H j) hxj⟩

/-- The actual reveal of the critical layer. -/
def criticalReveal {d : ℕ} (s : Finset J) (Q H : J → Finset (Vertex d))
    (z : Configuration d × Configuration d) : RevealValue s Q :=
  ⟨clusterFamilyUnion z.1 s Q H,
    Finset.mem_powerset.mpr (clusterFamilyUnion_subset_cubes z.1 s Q H)⟩

/-- Explored layered bonds of a reveal value: the cluster reveal bonds, in the
critical layer only. The sprinkle layer is not explored anywhere. -/
def revealBondsOf {d : ℕ} (s : Finset J) (Q : J → Finset (Vertex d))
    (F : RevealValue s Q) : Finset (LBond d) :=
  (clusterFamilyRevealBonds s Q (fun j => F.val ∩ Q j)).image (fun e => ((false, e) : LBond d))

/-- Reveal atoms are local on their explored bonds. -/
theorem criticalReveal_atom_isLocal {d : ℕ} (s : Finset J) (Q H : J → Finset (Vertex d))
    (hQ : (s : Set J).PairwiseDisjoint Q) (hH : ∀ j ∈ s, H j ⊆ Q j) (F : RevealValue s Q) :
    IsLocal (revealBondsOf s Q F)
      (fun z => @ite ℝ (criticalReveal s Q H z = F) (Classical.propDecidable _) 1 0) := by
  have hcyl := clusterFamilyUnion_event_cylinder s Q H hQ hH F.val
    (Finset.mem_powerset.mp F.property)
  unfold revealBondsOf
  refine ⟨fun b => if (fun e : ↥(clusterFamilyRevealBonds s Q (fun j => F.val ∩ Q j)) =>
      b ⟨((false, e.1) : LBond d), Finset.mem_image_of_mem _ e.2⟩) ∈
        clusterFamilyLocalEvent s Q H (fun j => F.val ∩ Q j)
    then (1:ℝ) else 0, fun z => ?_⟩
  have hiff : criticalReveal s Q H z = F ↔
      (clusterFamilyRevealBonds s Q (fun j => F.val ∩ Q j)).restrict z.1 ∈
        clusterFamilyLocalEvent s Q H (fun j => F.val ∩ Q j) := by
    have h1 : criticalReveal s Q H z = F ↔ clusterFamilyUnion z.1 s Q H = F.val :=
      Subtype.ext_iff
    have h2 : clusterFamilyUnion z.1 s Q H = F.val ↔
        z.1 ∈ {ω : Configuration d | clusterFamilyUnion ω s Q H = F.val} := Iff.rfl
    rw [h1, h2, hcyl]
    rfl
  have hfun : (fun e : ↥(clusterFamilyRevealBonds s Q (fun j => F.val ∩ Q j)) =>
      (((clusterFamilyRevealBonds s Q (fun j => F.val ∩ Q j)).image
        (fun e => ((false, e) : LBond d))).restrict (layerVal z))
        ⟨((false, e.1) : LBond d), Finset.mem_image_of_mem _ e.2⟩) =
      (clusterFamilyRevealBonds s Q (fun j => F.val ∩ Q j)).restrict z.1 := rfl
  beta_reduce
  rw [hfun]
  by_cases h : criticalReveal s Q H z = F
  · rw [if_pos h, if_pos (hiff.mp h)]
  · have h' : ¬ (clusterFamilyRevealBonds s Q (fun j => F.val ∩ Q j)).restrict z.1 ∈
        clusterFamilyLocalEvent s Q H (fun j => F.val ∩ Q j) := fun h' => h (hiff.mpr h')
    rw [if_neg h, if_neg h']

/-- **Source `lem.nw.mean` for one route with the actual reveal and an arbitrary
local step rule.** -/
theorem nestChain_mean_of_rule {d : ℕ} {X : Type*} [Fintype X] (p q : unitInterval)
    (s : Finset J) (Q H : J → Finset (Vertex d))
    (hQ : (s : Set J).PairwiseDisjoint Q) (hH : ∀ j ∈ s, H j ⊆ Q j)
    (B : RevealValue s Q → ℕ → Finset (LBond d))
    (hB : ∀ F i j, i ≠ j → Disjoint (B F i) (B F j))
    (hSB : ∀ F j, Disjoint (revealBondsOf s Q F) (B F j))
    (a : ∀ (F : RevealValue s Q) (t : ℕ), X → Set ((B F t → Bool)))
    (o : ∀ (F : RevealValue s Q) (t : ℕ), X → (B F t → Bool) → Finset X)
    (ho : ∀ F t x, ∀ b ∈ a F t x, (o F t x b).Nonempty)
    (hs : ∀ F t x, 0 < localSuccessProbability p q (B F t) (a F t x))
    (w : RevealValue s Q → ℝ) (n : RevealValue s Q → ℕ) (x₀ : RevealValue s Q → X) :
    (∫ z, w (criticalReveal s Q H z) *
        chainValue (fun t x y => stepKernel (B (criticalReveal s Q H z) t)
            (a (criticalReveal s Q H z) t x) (o (criticalReveal s Q H z) t x)
            (localSuccessProbability p q (B (criticalReveal s Q H z) t)
              (a (criticalReveal s Q H z) t x)) y)
          (n (criticalReveal s Q H z)) 0 (x₀ (criticalReveal s Q H z)) z
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z, w (criticalReveal s Q H z) ∂((percolation d p).prod (percolation d q)) :=
  revealed_chain_mean p q (criticalReveal s Q H) (revealBondsOf s Q)
    (criticalReveal_atom_isLocal s Q H hQ hH) B hB hSB
    (fun F t x y => stepKernel (B F t) (a F t x) (o F t x)
      (localSuccessProbability p q (B F t) (a F t x)) y)
    (fun F t x y => stepKernel_isLocal (B F t) (a F t x) (o F t x) _ y)
    (fun F t x => stepKernel_integral_eq_one p q (B F t) (a F t x) (o F t x)
      (ho F t x) (hs F t x))
    w n x₀

end NearCritical.Section10
