module

public import NearCritical.SplitCrossNeck
public import NearCritical.SplitCrossSpineBoxes

/-! Branch positions vary over smaller boxes. The containing boxes retain all
the endpoints obtained by bounded shifts of these positions. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open scoped Classical

/-- An offset inside a centred box consumes only its radius in the
translated box containing the original point. -/
theorem translatedBox_add_mem {d r R s : ℕ} {a x u : Vertex d}
    (hrs : r + R ≤ s) (hx : x ∈ translateSites a (centeredBox d r))
    (hu : u ∈ centeredBox d R) :
    x + u ∈ translateSites a (centeredBox d s) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  rw [add_assoc, mem_translateSites]
  apply mem_centeredBox.mpr
  intro j
  have hz' := mem_centeredBox.mp hz j
  have hu' := mem_centeredBox.mp hu j
  simp only [Pi.add_apply]
  omega

def legBranchCore {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl inside : Bool) :
    Finset (Vertex d) :=
  translateSites (if inside then legBoxCenter t f pl (entryBoxHeight t true)
    else farLegBoxCenter t f pl) (centeredBox d (t / 2048))

theorem legBranchCore_card {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl inside : Bool) :
    (legBranchCore t f pl inside).card = (2 * (t / 2048) + 1) ^ d := by
  rw [legBranchCore, card_translateSites, card_centeredBox_exact]

theorem legBranchCore_add_mem {d t R : ℕ} (ht : 2048 * R ≤ t)
    {f : Fin d × Bool} {pl inside : Bool} {x u : Vertex d}
    (hx : x ∈ legBranchCore t f pl inside) (hu : u ∈ centeredBox d R) :
    x + u ∈ legBranchBox t f pl inside := by
  exact translatedBox_add_mem (by omega : t / 2048 + R ≤ t / 1024) hx hu

theorem legBranchBox_inside_subset_entry {d t : ℕ} (f : Fin d × Bool) (pl : Bool) :
    legBranchBox t f pl true ⊆ entryLegBox t f pl true := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_translateSites _ _ _).mpr
  apply mem_centeredBox.mpr
  intro j
  have hz' := mem_centeredBox.mp hz j
  unfold legBoxRadius
  omega

theorem legBranchBox_exterior_subset_halfBox {d t : ℕ} (f : Fin d × Bool) (pl : Bool) :
    legBranchBox t f pl false ⊆
      translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t / 2)) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_translateSites _ _ _).mpr
  apply mem_centeredBox.mpr
  intro j
  have hz' := mem_centeredBox.mp hz j
  unfold legBoxRadius
  omega

def spineBranchCore {d K : ℕ} (t : ℕ) (axis : Fin d) (k : Fin K) : Finset (Vertex d) :=
  translateSites (spineBoxCenter t axis k) (centeredBox d (spineRadius K t / 2))

theorem spineBranchCore_card {d K : ℕ} (t : ℕ) (axis : Fin d) (k : Fin K) :
    (spineBranchCore t axis k).card = (2 * (spineRadius K t / 2) + 1) ^ d := by
  rw [spineBranchCore, card_translateSites, card_centeredBox_exact]

theorem spineBranchCore_add_mem {d K t R : ℕ} (ht : 512 * (K + 1) * R ≤ t)
    {axis : Fin d} {k : Fin K} {x u : Vertex d}
    (hx : x ∈ spineBranchCore t axis k) (hu : u ∈ centeredBox d R) :
    x + u ∈ spineBox t axis k := by
  have hR : R ≤ spineRadius K t / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    unfold spineRadius
    apply (Nat.le_div_iff_mul_le (by positivity)).2
    calc R * 2 * (256 * (K + 1)) = 512 * (K + 1) * R := by ring
      _ ≤ t := ht
  exact translatedBox_add_mem (by omega : spineRadius K t / 2 + R ≤ spineRadius K t) hx hu

end NearCritical.SplitCrossDirect
