module

public import NearCritical.LatticeRectangularTiling
public import NearCritical.TransverseConductivityTranslation

/-! Exact support and actual annealed template identities for grid cells. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

def gridShift {d : ℕ} (w z : Vertex d) : Vertex d := fun k => z k * w k

theorem gridCell_eq_translate {d : ℕ} (w z : Vertex d) :
    gridCell w z = translateSites (gridShift w z) (gridCell w 0) := by
  classical
  ext x
  constructor
  · intro hx
    refine mem_image.mpr ⟨x-gridShift w z, ?_, ?_⟩
    · apply mem_latticeRectangle.mpr
      intro k
      have hk := mem_latticeRectangle.mp hx k
      simp only [Pi.zero_apply,zero_mul,Pi.sub_apply,gridShift]
      constructor <;> omega
    · ext k
      simp [gridShift]
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    apply mem_latticeRectangle.mpr
    intro k
    have hk := mem_latticeRectangle.mp hy k
    simp only [Pi.zero_apply,zero_mul] at hk
    simp only [Pi.add_apply,gridShift]
    constructor <;> omega

lemma card_gridCell_eq {d : ℕ} (w z : Vertex d) :
    (gridCell w z).card = (gridCell w 0).card := by
  rw [gridCell_eq_translate,card_translateSites]

theorem annealedFull_gridCell {d : ℕ} (w z : Vertex d) (i : Fin d)
    (p : unitInterval) : annealedFull (gridCell w z) i (p : ℝ) =
      annealedFull (gridCell w 0) i (p : ℝ) := by
  rw [gridCell_eq_translate,annealedFull_translation]

theorem annealedRelaxed_gridCell {d : ℕ} (w z : Vertex d) (i : Fin d)
    (hz : z i = 0) (p : unitInterval) : annealedRelaxed (gridCell w z) i (p : ℝ) =
      annealedRelaxed (gridCell w 0) i (p : ℝ) := by
  rw [gridCell_eq_translate,annealedRelaxed_transverse_translation _ _ i (by simp [gridShift,hz])]

end NearCritical
