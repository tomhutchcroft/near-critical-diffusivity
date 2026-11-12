module

public import NearCritical.Section10StepLocality
public import NearCritical.NestRepresentative

/-! One sprinkling step, as a function of the step view.

`StepView d` is the tuple computed by `stepView`: the two unexplored graphs,
the opened pivotal pairs and the coalescing sites. For a nest (a finite set of
clusters) with source patches `src`, candidate clusters `cand` of the next cube
with target patches `tgt`:

* `svPivots`: the pivot pairs of the sprinkling cluster of the whole nest;
* `svOffOf rep`: the offspring of one cluster `rep` of the nest;
* `svTypical`: the sprinkling cluster of the nest is typical
  (`IsTypicalSprinklingBridge` with `m_off = 2 k^4`, source `def.goodskl`);
* `svNext`: the possible next nests, the `k`-subsets of the offspring of some
  good cluster (`>= 2 k^3` offspring). The source takes the first good cluster
  in a fixed order; here any good cluster is allowed.

`svNext_nonempty`: on a typical step from a `k`-nest there is a next nest
(pigeonhole, `eq.pigeonhole.k-nest`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- The type of `stepView`. -/
abbrev StepView (d : ℕ) : Type :=
  SimpleGraph (Vertex d) × SimpleGraph (Vertex d) ×
    (Finset (Vertex d) → Finset (Vertex d) → Finset (Vertex d × Vertex d)) ×
    (Finset (Vertex d) → Finset (Vertex d) → Finset (Vertex d) → Finset (Vertex d))

section
variable {d : ℕ} (v : StepView d) (nest cand : Finset (Finset (Vertex d)))
  (src tgt : Finset (Vertex d) → Finset (Vertex d))

/-- Pivot pairs of the sprinkling cluster of the nest. -/
def svPivots : Finset (Vertex d × Vertex d) :=
  v.2.2.1 (sprinklingTargetBoundary nest src) (sprinklingTargetBoundary cand tgt)

/-- Offspring of one cluster of the nest. -/
def svOffOf (rep : Finset (Vertex d)) : Finset (Finset (Vertex d)) :=
  sprinklingOffspring v.1 v.2.1 (src rep) cand tgt (svPivots v nest cand src tgt)

/-- Intrinsic diameter of the sprinkling cluster of the nest. -/
def svDiameter : ℕ :=
  sprinklingIntrinsicDiameter v.1 v.2.1 (sprinklingTargetBoundary nest src)
    (sprinklingTargetBoundary cand tgt) (svPivots v nest cand src tgt)

/-- The sprinkling cluster of the nest is typical. -/
def svTypical (face : Finset (Vertex d)) (k MOff Mcoal Kdiam : ℕ) : Prop :=
  IsTypicalSprinklingBridge
    (sprinklingOffspring v.1 v.2.1 (sprinklingTargetBoundary nest src) cand tgt
      (svPivots v nest cand src tgt))
    (v.2.2.2 (sprinklingTargetBoundary nest src) face (sprinklingTargetBoundary cand tgt))
    (svDiameter v nest cand src tgt) (2 * k ^ 4) MOff Mcoal Kdiam

/-- Possible next nests. -/
def svNext (k : ℕ) (P : Finset (Finset (Finset (Vertex d)))) : Finset ↥P :=
  P.attach.filter (fun N' => N'.val.card = k ∧ ∃ rep ∈ nest,
    2 * k ^ 3 ≤ (svOffOf v nest cand src tgt rep).card ∧
    N'.val ⊆ svOffOf v nest cand src tgt rep)

lemma svOffOf_subset_cand (rep : Finset (Vertex d)) :
    svOffOf v nest cand src tgt rep ⊆ cand := by
  intro c hc
  exact ((mem_sprinklingOffspring _ _ _ _ _ _ c).mp hc).1

theorem svNext_nonempty {face : Finset (Vertex d)} {k MOff Mcoal Kdiam : ℕ} (hk : 0 < k)
    (hcard : nest.card = k)
    (htyp : svTypical v nest cand src tgt face k MOff Mcoal Kdiam)
    (P : Finset (Finset (Finset (Vertex d)))) (hP : cand.powerset ⊆ P) :
    (svNext v nest cand src tgt k P).Nonempty := by
  have htotal : 2 * k ^ 4 ≤ (nest.biUnion (svOffOf v nest cand src tgt)).card := by
    have h := htyp.2.1
    rw [sprinklingOffspring_union] at h
    exact h
  obtain ⟨rep, hrep, hgood⟩ :=
    nest_exists_good_representative nest (svOffOf v nest cand src tgt) hk hcard htotal
  have hkle : k ≤ (svOffOf v nest cand src tgt rep).card := by
    refine le_trans ?_ hgood
    have h1 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
    calc k = k * 1 := (Nat.mul_one k).symm
      _ ≤ k * k ^ 2 := Nat.mul_le_mul_left k h1
      _ = k ^ 3 := by ring
      _ ≤ 2 * k ^ 3 := Nat.le_mul_of_pos_left _ (by norm_num)
  obtain ⟨N', hN'sub, hN'card⟩ := Finset.exists_subset_card_eq hkle
  have hN'P : N' ∈ P :=
    hP (Finset.mem_powerset.mpr (hN'sub.trans (svOffOf_subset_cand v nest cand src tgt rep)))
  refine ⟨⟨N', hN'P⟩, ?_⟩
  unfold svNext
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_attach _ _, hN'card, rep, hrep, hgood, hN'sub⟩

lemma mem_svNext {k : ℕ} {P : Finset (Finset (Finset (Vertex d)))} {N' : ↥P}
    (h : N' ∈ svNext v nest cand src tgt k P) :
    N'.val.card = k ∧ ∃ rep ∈ nest,
      2 * k ^ 3 ≤ (svOffOf v nest cand src tgt rep).card ∧
      N'.val ⊆ svOffOf v nest cand src tgt rep := by
  unfold svNext at h
  exact (Finset.mem_filter.mp h).2

end
end NearCritical.Section10
