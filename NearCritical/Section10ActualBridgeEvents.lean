module

public import NearCritical.Section10FirstGoodStep
public import NearCritical.Section10OffspringCount
public import NearCritical.Section10CommonDisjointOffspring
public import NearCritical.Section10SharedPhasePersistence
public import NearCritical.Section9MiddleGeometry

/-! Identifying actual next-nest membership and bridge intersections with
the events bounded in (H1)–(H3). -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- The middle geometry forces every critical pivot closed, so using the
OR configuration at the join has exactly the same effect as using the
independent sprinkle bits. -/
theorem middle_sprinkledPivotalPairs_or_eq {d : ℕ} (ω η : Configuration d)
    (M L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hML : M ⊆ L) (hMQ : Disjoint (M : Set (Vertex d)) (Q₁ : Set (Vertex d))) :
    sprinkledPivotalPairs ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
      L R Q₁ F₁ Q₃ F₃ A B =
    sprinkledPivotalPairs ω η (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B := by
  ext e
  simp only [sprinkledPivotalPairs, Finset.mem_filter]
  constructor
  · rintro ⟨he, b, hopen, hends⟩
    have hclosed := middle_sprinklingPivotalPairs_closed M L R Q₁ F₁ Q₃ F₃ A B hML hMQ he
    have hω : ω b = false := by
      cases hb : ω b
      · rfl
      · exact (hclosed ⟨b, hb, hends⟩).elim
    exact ⟨he, b, by simpa only [sprinkleOrConfiguration, hω, Bool.false_or] using hopen, hends⟩
  · rintro ⟨he, b, hopen, hends⟩
    exact ⟨he, b, by simp only [sprinkleOrConfiguration, hopen, Bool.or_true], hends⟩

theorem middle_sprinklingCluster_or_eq {d : ℕ} (ω η : Configuration d)
    (M L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hML : M ⊆ L) (hMQ : Disjoint (M : Set (Vertex d)) (Q₁ : Set (Vertex d))) :
    section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B =
      section9SprinklingCluster ω η (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B := by
  unfold section9SprinklingCluster
  rw [middle_sprinkledPivotalPairs_or_eq ω η M L R Q₁ F₁ Q₃ F₃ A B hML hMQ]

/-- The actual offspring of a representative are exactly those targets
with an opened pivot for its own source patch and the target's own patch.
The pivot set used to compute the step is the one for the whole nest. -/
theorem svOffOf_mem_iff_opened_target {d : ℕ} (ω η : Configuration d)
    (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (nest cand : Finset (Finset (Vertex d)))
    (src tgt : Finset (Vertex d) → Finset (Vertex d)) {rep : Finset (Vertex d)} (hrep : rep ∈ nest)
    (c : Finset (Vertex d)) :
    c ∈ svOffOf (stepView M L R Q₁ F₁ Q₃ F₃ (ω, η)) nest cand src tgt rep ↔
      c ∈ cand ∧ (sprinkledPivotalPairs ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
        L R Q₁ F₁ Q₃ F₃ (src rep) (tgt c)).Nonempty := by
  unfold svOffOf svPivots
  rw [mem_sprinklingOffspring]
  constructor
  · rintro ⟨hc, x, hx, y, hy, e, he, hxr, hyr⟩
    change e ∈ sprinkledPivotalPairs ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
      L R Q₁ F₁ Q₃ F₃ (sprinklingTargetBoundary nest src) (sprinklingTargetBoundary cand tgt) at he
    obtain ⟨he₀, hopen⟩ := Finset.mem_filter.mp he
    obtain ⟨heM, hadj, heL, heR, _, _, hdis⟩ := Finset.mem_filter.mp he₀
    have hxL : x ∈ L := by
      obtain ⟨p⟩ := hxr
      exact microscopicWalk_support p heL x p.end_mem_support
    have hyR : y ∈ R := by
      obtain ⟨p⟩ := hyr
      exact microscopicWalk_support p heR y p.end_mem_support
    have hxC := (mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mpr ⟨hxL, hxr⟩
    have hyC := (mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mpr ⟨hyR, hyr⟩
    exact ⟨hc, e, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨heM, hadj, heL, heR, ⟨x, Finset.mem_inter.mpr ⟨hxC, hx⟩⟩,
        ⟨y, Finset.mem_inter.mpr ⟨hyC, hy⟩⟩, hdis⟩, hopen⟩⟩
  · rintro ⟨hc, e, he⟩
    obtain ⟨he₀, hopen⟩ := Finset.mem_filter.mp he
    obtain ⟨heM, hadj, heL, heR, ⟨x, hx⟩, ⟨y, hy⟩, hdis⟩ := Finset.mem_filter.mp he₀
    obtain ⟨hxC, hx⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyC, hy⟩ := Finset.mem_inter.mp hy
    refine ⟨hc, x, hx, y, hy, e, ?_, (mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxC |>.2,
      (mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mp hyC |>.2⟩
    change e ∈ sprinkledPivotalPairs ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
      L R Q₁ F₁ Q₃ F₃ (sprinklingTargetBoundary nest src) (sprinklingTargetBoundary cand tgt)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨heM, hadj, heL, heR, ⟨x, Finset.mem_inter.mpr ⟨hxC, mem_sprinklingTargetBoundary _ _ hrep hx⟩⟩,
        ⟨y, Finset.mem_inter.mpr ⟨hyC, mem_sprinklingTargetBoundary _ _ hc hy⟩⟩, hdis⟩, hopen⟩

/-- A bridge from a union of patches is the union of their bridges. This
uses the critical pivotal definition, which tests intersection with the
source patch. -/
theorem bridge_of_nest_eq_biUnion {d : ℕ} {ι : Type*} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (J : Finset ι) (X : ι → Finset (Vertex d)) :
    section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ (J.biUnion X) B =
      J.biUnion (fun c => section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ (X c) B) := by
  ext z
  rw [Finset.mem_biUnion, mem_section9SprinklingCluster]
  constructor
  · rintro ⟨e, he, hz⟩
    obtain ⟨he₀, hopen⟩ := Finset.mem_filter.mp he
    obtain ⟨heE, hadj, heL, heR, ⟨x, hx⟩, htarget, hdis⟩ := Finset.mem_filter.mp he₀
    obtain ⟨hxC, hx⟩ := Finset.mem_inter.mp hx
    obtain ⟨c, hc, hx'⟩ := Finset.mem_biUnion.mp hx
    exact ⟨c, hc, (mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ (X c) B z).mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨heE, hadj, heL, heR, ⟨x, Finset.mem_inter.mpr ⟨hxC, hx'⟩⟩, htarget, hdis⟩, hopen⟩, hz⟩⟩
  · rintro ⟨c, hc, hz⟩
    obtain ⟨e, he, hz⟩ := (mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ (X c) B z).mp hz
    obtain ⟨he₀, hopen⟩ := Finset.mem_filter.mp he
    obtain ⟨heE, hadj, heL, heR, ⟨x, hx⟩, htarget, hdis⟩ := Finset.mem_filter.mp he₀
    obtain ⟨hxC, hx⟩ := Finset.mem_inter.mp hx
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨heE, hadj, heL, heR, ⟨x, Finset.mem_inter.mpr ⟨hxC, Finset.mem_biUnion.mpr ⟨c, hc, hx⟩⟩⟩,
        htarget, hdis⟩, hopen⟩, hz⟩

/-- The actual OR-configured bridge intersection is exactly the union
over the two incoming nests of the independent-sprinkling intersections. -/
theorem actual_bridge_intersection_iff {d : ℕ} {ι ι' : Type*}
    (ω η : Configuration d) (M L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (hML : M ⊆ L) (hMQ : Disjoint (M : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    (J : Finset ι) (J' : Finset ι') (X : ι → Finset (Vertex d)) (Y : ι' → Finset (Vertex d)) :
    (section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
        L R Q₁ F₁ Q₃ F₃ (J.biUnion X) B ∩
      section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
        L R Q₁ F₁ Q₃ F₃ (J'.biUnion Y) B).Nonempty ↔
      (ω, η) ∈ bridgeNestMeetEvent (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ B J J' X Y := by
  have heq (A : Finset (Vertex d)) := middle_sprinklingCluster_or_eq ω η M L R Q₁ F₁ Q₃ F₃ A B hML hMQ
  rw [heq, heq, bridge_of_nest_eq_biUnion, bridge_of_nest_eq_biUnion]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hz
    obtain ⟨x, hxJ, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hyJ, hy⟩ := Finset.mem_biUnion.mp hy
    exact ⟨x, hxJ, y, hyJ, z, Finset.mem_inter.mpr ⟨hx, hy⟩⟩
  · rintro ⟨x, hxJ, y, hyJ, z, hz⟩
    obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hz
    exact ⟨z, Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨x, hxJ, hx⟩,
      Finset.mem_biUnion.mpr ⟨y, hyJ, hy⟩⟩⟩

/-- Positive next-nest membership gives a source representative with a
sprinkled pivot to the selected child. This covers the first-good rule
through its inclusion in the set of possible next nests. -/
theorem svNext_member_has_opened_target {d : ℕ} (ω η : Configuration d)
    (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hML : M ⊆ L) (hMQ : Disjoint (M : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    (nest cand : Finset (Finset (Vertex d)))
    (src tgt : Finset (Vertex d) → Finset (Vertex d))
    {k : ℕ} {P : Finset (Finset (Finset (Vertex d)))} {N' : ↥P} {c : Finset (Vertex d)}
    (hN' : N' ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ (ω, η)) nest cand src tgt k P)
    (hc : c ∈ N'.val) :
    c ∈ cand ∧ ∃ rep ∈ nest,
      (sprinkledPivotalPairs ω η (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (src rep) (tgt c)).Nonempty := by
  obtain ⟨_, rep, hrep, _, hsub⟩ := mem_svNext _ _ _ _ _ hN'
  obtain ⟨hcand, hhit⟩ := (svOffOf_mem_iff_opened_target ω η M L R Q₁ F₁ Q₃ F₃ nest cand
    src tgt hrep c).mp (hsub hc)
  rw [middle_sprinkledPivotalPairs_or_eq ω η M L R Q₁ F₁ Q₃ F₃ (src rep) (tgt c) hML hMQ] at hhit
  exact ⟨hcand, rep, hrep, hhit⟩

/-- If two actual next nests share a child and the two full bridges are
disjoint, a pair of possible representatives realizes an H2 event for that
child. The representative choice can depend on the tube. -/
theorem svNext_common_member_disjoint_event {d : ℕ} (ω η : Configuration d)
    (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hML : M ⊆ L) (hMQ : Disjoint (M : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    (nest nest' cand : Finset (Finset (Vertex d)))
    (src src' tgt : Finset (Vertex d) → Finset (Vertex d))
    {k : ℕ} {P : Finset (Finset (Finset (Vertex d)))} {N N' : ↥P} {c : Finset (Vertex d)}
    (hN : N ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ (ω, η)) nest cand src tgt k P)
    (hN' : N' ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ (ω, η)) nest' cand src' tgt k P)
    (hc : c ∈ N.val) (hc' : c ∈ N'.val)
    (hdis : Disjoint (section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
      L R Q₁ F₁ Q₃ F₃ (sprinklingTargetBoundary nest src) (sprinklingTargetBoundary cand tgt))
      (section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
        L R Q₁ F₁ Q₃ F₃ (sprinklingTargetBoundary nest' src') (sprinklingTargetBoundary cand tgt))) :
    c ∈ cand ∧ ∃ a ∈ nest, ∃ b ∈ nest',
      (ω, η) ∈ disjointOffspringEvent (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃
        (src a) (src' b) (tgt c) (tgt c) (sprinklingTargetBoundary cand tgt) := by
  obtain ⟨hcand, a, ha, hhit⟩ := svNext_member_has_opened_target ω η M L R Q₁ F₁ Q₃ F₃ hML hMQ
    nest cand src tgt hN hc
  obtain ⟨_, b, hb, hhit'⟩ := svNext_member_has_opened_target ω η M L R Q₁ F₁ Q₃ F₃ hML hMQ
    nest' cand src' tgt hN' hc'
  let B := sprinklingTargetBoundary cand tgt
  have heq (A : Finset (Vertex d)) := middle_sprinklingCluster_or_eq ω η M L R Q₁ F₁ Q₃ F₃ A B hML hMQ
  change Disjoint (section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
    L R Q₁ F₁ Q₃ F₃ (nest.biUnion src) B)
    (section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
      L R Q₁ F₁ Q₃ F₃ (nest'.biUnion src') B) at hdis
  rw [heq, heq, bridge_of_nest_eq_biUnion, bridge_of_nest_eq_biUnion] at hdis
  exact ⟨hcand, a, ha, b, hb, hhit, hhit',
    hdis.mono (fun z hz => Finset.mem_biUnion.mpr ⟨a, ha, hz⟩)
      (fun z hz => Finset.mem_biUnion.mpr ⟨b, hb, hz⟩)⟩

end NearCritical.Section10
