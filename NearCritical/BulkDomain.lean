module

public import NearCritical.WaterCube
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! The source bulk and its perturbed edge set in Section 5.1.
The energy uses E+(U), while the variable-parameter bonds are E(bulk):
both endpoints must belong to the bulk. Extrinsic distance is the sup metric
on Fin d → ℤ, not the Euclidean norm used in assumption (A). -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset

/-- Actual extrinsic distance to the union of the two source faces in U+. -/
def twoFaceDistance {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (x : Vertex d) : ℝ :=
  Metric.infDist x (Subtype.val '' twoFaceBoundary U i)

/-- Source eq.cube.delta with height h; its application to the water cube has
h=2r+1. The outer membership is in U, not the enlarged support U+. -/
def bulkVertices {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ) :
    Finset (Vertex d) := by
  classical
  exact U.filter (fun x => δ * h / 2 < twoFaceDistance U i x)

lemma mem_bulkVertices {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ)
    (x : Vertex d) : x ∈ bulkVertices U i h δ ↔
      x ∈ U ∧ δ * h / 2 < twoFaceDistance U i x := by
  classical
  simp [bulkVertices]

lemma bulkVertices_subset {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ) :
    bulkVertices U i h δ ⊆ U := by
  intro x hx
  exact (mem_bulkVertices U i h δ x).mp hx |>.1

/-- Source E(V), uniquely indexed by positive-coordinate bonds. -/
def internalBondSet {d : ℕ} (V : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact (issuedBondSet V).filter (fun e => bondTip e ∈ V)

lemma mem_internalBondSet {d : ℕ} (V : Finset (Vertex d)) (e : Bond d) :
    e ∈ internalBondSet V ↔ e.1 ∈ V ∧ bondTip e ∈ V := by
  classical
  simp [internalBondSet, issuedBondSet]

lemma internalBondSet_subset_issued {d : ℕ} {V U : Finset (Vertex d)} (hVU : V ⊆ U) :
    internalBondSet V ⊆ issuedBondSet U := by
  intro e he
  have hb := hVU ((mem_internalBondSet V e).mp he).1
  exact Finset.mem_product.mpr ⟨hb, Finset.mem_univ _⟩

/-- The variable-parameter mask inside the original finite energy coordinates. -/
def bulkBondMask {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ) :
    Finset (IssuedBond U) := by
  classical
  exact Finset.univ.filter (fun e => e.val ∈ internalBondSet (bulkVertices U i h δ))

lemma mem_bulkBondMask {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ)
    (e : IssuedBond U) : e ∈ bulkBondMask U i h δ ↔
      e.val.1 ∈ bulkVertices U i h δ ∧ bondTip e.val ∈ bulkVertices U i h δ := by
  classical
  simp [bulkBondMask, mem_internalBondSet]

/-- Source perturbation never changes a bond outside the energy coordinates. -/
lemma internal_bulk_subset_issued {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ) :
    internalBondSet (bulkVertices U i h δ) ⊆ issuedBondSet U :=
  internalBondSet_subset_issued (bulkVertices_subset U i h δ)

/-- Exact full-lattice perturbed bond set, not merely an inclusion. -/
lemma bulkBondMask_image {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ) :
    (bulkBondMask U i h δ).image Subtype.val = internalBondSet (bulkVertices U i h δ) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact (mem_internalBondSet _ _).mpr ((mem_bulkBondMask U i h δ j).mp hj)
  · intro he
    let j : IssuedBond U := ⟨e, internal_bulk_subset_issued U i h δ he⟩
    exact Finset.mem_image.mpr ⟨j, (mem_bulkBondMask U i h δ j).mpr
      ((mem_internalBondSet _ _).mp he), rfl⟩

end NearCritical
