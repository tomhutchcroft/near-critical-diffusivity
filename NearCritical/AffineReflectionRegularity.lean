module
public import NearCritical.AffineReflectionDeleted
public import NearCritical.NestRegularBoundary

/-! The literal regularity energies are invariant under lattice reflection. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

theorem latticeDistance_affineReflection {d : ℕ} (c x y : Vertex d) :
    latticeDistance (affineReflection c x) (affineReflection c y) = latticeDistance x y := by
  have he : vertexReal (affineReflection c x)-vertexReal (affineReflection c y) =
      -(vertexReal x-vertexReal y) := by
    ext j
    simp only [vertexReal,affineReflection,Equiv.coe_fn_mk,Pi.sub_apply,Pi.neg_apply,Int.cast_sub]
    ring
  simp only [latticeDistance,dist_eq_norm]
  rw [he,norm_neg]

theorem regularityEnergyOne_affineReflection {d : ℕ} (c : Vertex d)
    (F S : Finset (Vertex d)) (r : ℕ) (x : Vertex d) :
    regularityEnergyOne (F.image (affineReflection c)) (S.image (affineReflection c))
      r (affineReflection c x) = regularityEnergyOne F S r x := by
  simp only [regularityEnergyOne]
  rw [← Finset.image_sdiff F S (affineReflection c).injective,Finset.sum_image]
  · simp only [latticeDistance_affineReflection]
  · intro a _ b _ hab
    exact (affineReflection c).injective hab

theorem regularityEnergyTwo_affineReflection {d : ℕ} (c : Vertex d)
    (F boundary : Finset (Vertex d)) (r : ℕ) (x : Vertex d) :
    regularityEnergyTwo (F.image (affineReflection c)) (boundary.image (affineReflection c))
      r (affineReflection c x) = regularityEnergyTwo F boundary r x := by
  simp only [regularityEnergyTwo]
  rw [← Finset.image_inter F boundary (affineReflection c).injective,Finset.sum_image]
  · simp only [latticeDistance_affineReflection]
  · intro a _ b _ hab
    exact (affineReflection c).injective hab

/-- Full boundary membership and BOTH literal energies are transported. -/
theorem sourceRegularPoint_affineReflection {d : ℕ} (c : Vertex d)
    (F S boundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ) (x : Vertex d) :
    sourceRegularPoint (F.image (affineReflection c)) (S.image (affineReflection c))
      (boundary.image (affineReflection c)) r δ (affineReflection c x) ↔
        sourceRegularPoint F S boundary r δ x := by
  have hm : affineReflection c x ∈ F.image (affineReflection c) ∩ boundary.image (affineReflection c) ↔
      x ∈ F ∩ boundary := by
    rw [← Finset.image_inter F boundary (affineReflection c).injective]
    constructor
    · intro hx
      obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hx
      exact (affineReflection c).injective heq ▸ hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  simp only [sourceRegularPoint,regularityEnergyOne_affineReflection,
    regularityEnergyTwo_affineReflection,hm]

end NearCritical
