module

public import NearCritical.FiniteClusterFamily
public import NearCritical.FiniteSlabPioneer
public import NearCritical.ThreePointDiagram

/-! Literal regular boundary from source def.regular and eq.def.regular_bd.
Regularity depends on the whole union of heart-touching clusters. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set
open scoped Classical

/-- Source fC: all cube clusters meeting the heart H. Roots outside Q contribute
nothing; in source geometry H is contained in Q. -/
def heartClusterUnion {d : ℕ} (ω : Configuration d) (Q H : Finset (Vertex d)) : Finset (Vertex d) :=
  H.biUnion (finiteBoxCluster ω Q)

lemma heartClusterUnion_subset {d : ℕ} (ω : Configuration d) (Q H : Finset (Vertex d)) :
    heartClusterUnion ω Q H ⊆ Q := by
  intro x hx
  obtain ⟨root,_,hr⟩ := Finset.mem_biUnion.mp hx
  exact finiteBoxCluster_subset ω Q root hr

lemma cluster_subset_heartClusterUnion {d : ℕ} (ω : Configuration d)
    (Q H : Finset (Vertex d)) {root : Vertex d} (hr : root ∈ H) :
    finiteBoxCluster ω Q root ⊆ heartClusterUnion ω Q H := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨root,hr,hx⟩

/-- Source ERE1 with |x-y| the supremum distance and exponent 2-d.
S is the geometrical excluded region from the source (Q,S,H,T)-structure. -/
def regularityEnergyOne {d : ℕ} (F S : Finset (Vertex d)) (r : ℕ) (x : Vertex d) : ℝ :=
  ∑ y ∈ F \ S, (max (r:ℝ) (latticeDistance x y)) ^ ((2:ℤ)-(d:ℤ))

/-- Source ERE2, summed over the FULL cube boundary, not one chosen subface. -/
def regularityEnergyTwo {d : ℕ} (F boundary : Finset (Vertex d)) (r : ℕ) (x : Vertex d) : ℝ :=
  ∑ y ∈ F ∩ boundary, (max (r:ℝ) (latticeDistance x y)) ^ ((4:ℤ)-(d:ℤ))

/-- Literal source regular point in F intersect boundary. -/
def sourceRegularPoint {d : ℕ} (F S boundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ)
    (x : Vertex d) : Prop :=
  x ∈ F ∩ boundary ∧ regularityEnergyOne F S r x ≤ δ ∧ regularityEnergyTwo F boundary r x ≤ δ

/-- A selected actual component's regular boundary, computed using the full
heart-cluster union for regularity. face may be a signed face or source subface. -/
def sourceRegularBoundary {d : ℕ} (ω : Configuration d)
    (Q H S boundary face : Finset (Vertex d)) (root : Vertex d) (r : ℕ) (δ : ℝ) : Finset (Vertex d) :=
  (finiteBoxCluster ω Q root ∩ face).filter
    (sourceRegularPoint (heartClusterUnion ω Q H) S boundary r δ)

lemma sourceRegularBoundary_subset_face {d : ℕ} (ω : Configuration d)
    (Q H S boundary face : Finset (Vertex d)) (root : Vertex d) (r : ℕ) (δ : ℝ) :
    sourceRegularBoundary ω Q H S boundary face root r δ ⊆ face := by
  intro x hx
  exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2

/-- Existing actual graph support gives component support for any root,
including the isolated-outside-root convention. No new independence premise. -/
lemma finiteBoxCluster_eq_of_internal_agree {d : ℕ} (U Q : Finset (Vertex d)) (hQU : Q ⊆ U)
    (ω η : Configuration d) (hagree : ∀ e ∈ internalBondSet U, ω e = η e) (root : Vertex d) :
    finiteBoxCluster ω Q root = finiteBoxCluster η Q root := by
  have hg := restrictedGraph_eq_of_internalBondSet_agree U (Q : Set (Vertex d)) hQU ω η hagree
  simp only [finiteBoxCluster,hg]

lemma heartClusterUnion_eq_of_internal_agree {d : ℕ} (U Q H : Finset (Vertex d)) (hQU : Q ⊆ U)
    (ω η : Configuration d) (hagree : ∀ e ∈ internalBondSet U, ω e = η e) :
    heartClusterUnion ω Q H = heartClusterUnion η Q H := by
  unfold heartClusterUnion
  apply Finset.biUnion_congr rfl
  intro root _hr
  exact finiteBoxCluster_eq_of_internal_agree U Q hQU ω η hagree root

/-- FULL regular-boundary invariance, including both analytic sums over fC.
It is not asserted to depend on the selected component alone. -/
theorem sourceRegularBoundary_eq_of_internal_agree {d : ℕ}
    (U Q H S boundary face : Finset (Vertex d)) (hQU : Q ⊆ U)
    (ω η : Configuration d) (hagree : ∀ e ∈ internalBondSet U, ω e = η e)
    (root : Vertex d) (r : ℕ) (δ : ℝ) :
    sourceRegularBoundary ω Q H S boundary face root r δ =
      sourceRegularBoundary η Q H S boundary face root r δ := by
  unfold sourceRegularBoundary
  rw [finiteBoxCluster_eq_of_internal_agree U Q hQU ω η hagree root,
    heartClusterUnion_eq_of_internal_agree U Q H hQU ω η hagree]

/-- Closed-outside reconstruction of the actual critical configuration from
its finitely many internal bits. -/
def reconstructInterior {d : ℕ} (U : Finset (Vertex d))
    (η : internalBondSet U → Bool) : Configuration d :=
  extendConfiguration (internalBondSet U) (fun _ => false) η

lemma reconstructInterior_restrict_agree {d : ℕ} (U : Finset (Vertex d)) (ω : Configuration d) :
    ∀ e ∈ internalBondSet U, ω e = reconstructInterior U ((internalBondSet U).restrict ω) e := by
  intro e he
  simp [reconstructInterior,extendConfiguration,he,Finset.restrict]

/-- Exact finite-history representation of the literal regular boundary. -/
theorem sourceRegularBoundary_reconstruct {d : ℕ}
    (U Q H S boundary face : Finset (Vertex d)) (hQU : Q ⊆ U)
    (ω : Configuration d) (root : Vertex d) (r : ℕ) (δ : ℝ) :
    sourceRegularBoundary ω Q H S boundary face root r δ =
      sourceRegularBoundary (reconstructInterior U ((internalBondSet U).restrict ω))
        Q H S boundary face root r δ :=
  sourceRegularBoundary_eq_of_internal_agree U Q H S boundary face hQU ω _
    (reconstructInterior_restrict_agree U ω) root r δ

end NearCritical
