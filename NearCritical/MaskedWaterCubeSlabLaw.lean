module

public import NearCritical.WaterCubeBulkBandGeometry
public import NearCritical.BulkPercolation
public import NearCritical.TwoPhaseSlabTranslation

/-! The actual bulk law agrees with a two-phase band ONLY on internal water-cube
coordinates. Translation and clipping are explicit; no assertion is made on
issued protrusions outside U or on full profiles. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- Rate identity on the physical bonds whose BOTH endpoints lie in U.
The original height is a_i+z_i, with a_i=-r, so z_i is normalized height. -/
theorem waterCube_bulkProfile_translate_internal {d : ℕ} (i : Fin d)
    (r R : ℕ) (δ : ℝ) (p q : unitInterval) (a : Vertex d)
    (ha : a i = -(r : ℤ)) (e : Bond d)
    (hb : a+e.1 ∈ waterCube d i r R)
    (ht : a+bondTip e ∈ waterCube d i r R) :
    (if translateBond a e ∈ internalBondSet
      (bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ) then q else p) =
      twoPhaseSlabProfile i ⌊δ*(2*(r : ℝ)+1)/2⌋
        ((2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1) p q e := by
  have hbiff := mem_bulkVertices_waterCube_iff_band i r R δ (a+e.1)
  have htiff := mem_bulkVertices_waterCube_iff_band i r R δ (a+bondTip e)
  simp only [hb,ht,true_and,Pi.add_apply,ha] at hbiff htiff
  have hend : translateBond a e ∈ internalBondSet
      (bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ) ↔
      e.1 ∈ finiteHeightSlab i (⌊δ*(2*(r : ℝ)+1)/2⌋+1)
          ((2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1) ∧
      bondTip e ∈ finiteHeightSlab i (⌊δ*(2*(r : ℝ)+1)/2⌋+1)
          ((2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1) := by
    rw [mem_internalBondSet, bondTip_translate]
    change (a+e.1 ∈ bulkVertices _ _ _ _ ∧ a+bondTip e ∈ bulkVertices _ _ _ _) ↔ _
    rw [hbiff,htiff]
    change ((_ < -(r : ℤ)+e.1 i+(r : ℤ) ∧ _ ≤ _) ∧
      (_ < -(r : ℤ)+bondTip e i+(r : ℤ) ∧ _ ≤ _)) ↔
      ((_ ≤ e.1 i ∧ e.1 i ≤ _) ∧ (_ ≤ bondTip e i ∧ bondTip e i ≤ _))
    omega
  simp only [twoPhaseSlabProfile,hend]

/-- Equality of actual translated, clipped laws. Thus arbitrary measurable
finite-coordinate events internal to the normalized U have the same law;
no equality is claimed for the unclipped global profiles. -/
theorem bulkPercolation_translate_clip_waterCube {d : ℕ} (i : Fin d)
    (r R : ℕ) (δ : ℝ) (p q : unitInterval) (a : Vertex d)
    (ha : a i = -(r : ℤ)) (S : Set (Vertex d))
    (hS : ∀ z ∈ S, a+z ∈ waterCube d i r R) :
    ((bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).map
      (translateConfiguration a)).map (domainClipConfiguration S) =
    (percolationProfile d (twoPhaseSlabProfile i ⌊δ*(2*(r : ℝ)+1)/2⌋
      ((2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1) p q)).map
      (domainClipConfiguration S) := by
  change ((percolationProfile d (fun e => if e ∈ internalBondSet
    (bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ) then q else p)).map
      (translateConfiguration a)).map _ = _
  rw [percolationProfile_map_translation]
  apply percolationProfile_domainClip_map_eq
  intro e he
  exact waterCube_bulkProfile_translate_internal i r R δ p q a ha e
    (hS e.1 he.1) (hS (bondTip e) he.2)

/-- Exact event-local bulk-to-band connection law on any domain translating
inside the actual base water cube. Nil paths and arbitrary targets are retained. -/
theorem bulkPercolation_waterCube_connection_band_law {d : ℕ} (i : Fin d)
    (r R : ℕ) (δ : ℝ) (p q : unitInterval) (a : Vertex d)
    (ha : a i = -(r : ℤ)) (S : Set (Vertex d))
    (hS : ∀ z ∈ S, a+z ∈ waterCube d i r R)
    (x : Vertex d) (A : Set (Vertex d)) :
    bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q
      (connectionToSetEvent ((fun z => a+z) '' S) (a+x) ((fun z => a+z) '' A)) =
    percolationProfile d (twoPhaseSlabProfile i ⌊δ*(2*(r : ℝ)+1)/2⌋
      ((2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1) p q)
      (connectionToSetEvent S x A) := by
  change percolationProfile d (fun e => if e ∈ internalBondSet
    (bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ) then q else p) _ = _
  rw [connectionToSet_profile_probability_translation]
  apply connectionToSet_profile_eq_of_internal_rates
  intro e he
  exact waterCube_bulkProfile_translate_internal i r R δ p q a ha e
    (hS e.1 he.1) (hS (bondTip e) he.2)

end NearCritical
