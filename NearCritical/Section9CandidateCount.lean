module

public import NearCritical.SprinklingPivots
public import NearCritical.BulkDomain

/-! Linear count of both physical orientations of the middle-box candidates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Positive-coordinate physical bonds are at most d per base vertex. -/
theorem internalBondSet_card_le {d : ℕ} (S : Finset (Vertex d)) :
    (internalBondSet S).card ≤ S.card * d := by
  have h := Finset.card_le_card (internalBondSet_subset_issued (V := S) (U := S) (fun _ h => h))
  simpa only [issuedBondSet, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin] using h

/-- Every oriented candidate is a forward or reversed internal physical bond.
The reverse orientation is retained even though physical bonds have one index. -/
theorem orientedLatticePairs_subset_bond_images {d : ℕ} (S : Finset (Vertex d)) :
    orientedLatticePairs S ⊆
      (internalBondSet S).image (fun b => (b.1, bondTip b)) ∪
      (internalBondSet S).image (fun b => (bondTip b, b.1)) := by
  rintro ⟨x,y⟩ he
  obtain ⟨hx,hy,hadj⟩ := (mem_orientedLatticePairs S x y).mp he
  obtain ⟨b,_,hends | hends⟩ := hadj
  · obtain ⟨rfl,rfl⟩ := hends
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
      ⟨b, (mem_internalBondSet S b).mpr ⟨hx,hy⟩, rfl⟩))
  · obtain ⟨rfl,rfl⟩ := hends
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨b, (mem_internalBondSet S b).mpr ⟨hy,hx⟩, rfl⟩))

/-- Count both orientations with the linear lattice-degree bound, valid for
all finite middle sets, including empty sets and dimension zero. -/
theorem orientedLatticePairs_card_le {d : ℕ} (S : Finset (Vertex d)) :
    (orientedLatticePairs S).card ≤ 2 * (S.card * d) := by
  calc
    (orientedLatticePairs S).card ≤
        ((internalBondSet S).image (fun b => (b.1, bondTip b)) ∪
          (internalBondSet S).image (fun b => (bondTip b, b.1))).card :=
      Finset.card_le_card (orientedLatticePairs_subset_bond_images S)
    _ ≤ ((internalBondSet S).image (fun b => (b.1, bondTip b))).card +
        ((internalBondSet S).image (fun b => (bondTip b, b.1))).card := Finset.card_union_le _ _
    _ ≤ (internalBondSet S).card + (internalBondSet S).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ ≤ 2 * (S.card * d) := by
      simpa only [two_mul] using Nat.add_le_add (internalBondSet_card_le S) (internalBondSet_card_le S)

end NearCritical
