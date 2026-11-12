module

public import NearCritical.Section10BridgeTypicality
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Every site of the patch's sprinkling cluster belongs to the sprinkling
cluster of a singleton root in that patch. -/
theorem sprinklingCluster_exists_singleton_root {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) {z : Vertex d}
    (hz : z ∈ section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B) :
    ∃ x ∈ A, z ∈ section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {x} B := by
  obtain ⟨e, he, hz'⟩ :=
    (mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B z).mp hz
  obtain ⟨heP, hopen⟩ := Finset.mem_filter.mp he
  obtain ⟨heE, hadj, hL, hR, hsource, htarget, hdisj⟩ := Finset.mem_filter.mp heP
  obtain ⟨x, hx⟩ := hsource
  obtain ⟨hxC, hxA⟩ := Finset.mem_inter.mp hx
  refine ⟨x, hxA, (mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {x} B z).mpr
    ⟨e, ?_, hz'⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨heE, hadj, hL, hR, ⟨x, Finset.mem_inter.mpr ⟨hxC, Finset.mem_singleton_self x⟩⟩,
      htarget, hdisj⟩, hopen⟩

theorem bridgeCoalescingSites_card_le_pairs {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A sourceFace B : Finset (Vertex d)) :
    (bridgeCoalescingSites ω η E L R Q₁ F₁ Q₃ F₃ A sourceFace B).card ≤
      section9CoalescenceCount ω η E L R Q₁ F₁ Q₃ F₃ (sourceFace \ A) A B := by
  unfold section9CoalescenceCount
  apply le_trans (Finset.card_le_card (t := (section9CoalescencePairs ω η E L R
    Q₁ F₁ Q₃ F₃ (sourceFace \ A) A B).image Prod.fst) ?_) Finset.card_image_le
  intro x hx
  obtain ⟨hxOutside, z, hz⟩ := Finset.mem_filter.mp hx
  obtain ⟨hzx, hzA⟩ := Finset.mem_inter.mp hz
  obtain ⟨y, hy, hzy⟩ :=
    sprinklingCluster_exists_singleton_root ω η E L R Q₁ F₁ Q₃ F₃ A B hzA
  exact Finset.mem_image.mpr ⟨(x,y),
    (mem_section9CoalescencePairs ω η E L R Q₁ F₁ Q₃ F₃ (sourceFace \ A) A B x y).mpr
      ⟨hxOutside, hy, z, Finset.mem_inter.mpr ⟨hzx, hzy⟩⟩, rfl⟩

/-- The count comparison holds under the joint critical and sprinkled law,
including its restriction to any measurable past event. -/
theorem bridgeCoalescingSites_lintegral_le_pairs {d : ℕ}
    (μ : MeasureTheory.Measure (Configuration d × Configuration d))
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A sourceFace B : Finset (Vertex d)) :
    (∫⁻ z, ((bridgeCoalescingSites z.1 z.2 E L R Q₁ F₁ Q₃ F₃ A sourceFace B).card : ENNReal) ∂μ) ≤
    ∫⁻ z, (section9CoalescenceCount z.1 z.2 E L R Q₁ F₁ Q₃ F₃ (sourceFace \ A) A B : ENNReal) ∂μ := by
  apply MeasureTheory.lintegral_mono
  intro z
  dsimp only
  exact_mod_cast bridgeCoalescingSites_card_le_pairs z.1 z.2 E L R Q₁ F₁ Q₃ F₃ A sourceFace B

end NearCritical.Section10
