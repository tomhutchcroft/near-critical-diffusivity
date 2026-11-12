module

public import NearCritical.LatticeDomain

/-! Exact issued-edge geometry and energy additivity. These identities are the
partition step of source `lem.subadditive`; minimizer gluing is separate. -/
@[expose] public section
namespace NearCritical
open Finset

lemma issuedBondSet_union {d : ℕ} (U W : Finset (Vertex d)) :
    issuedBondSet (U ∪ W) = issuedBondSet U ∪ issuedBondSet W := by
  classical
  ext e
  simp [issuedBondSet]

lemma issuedBondSet_disjoint {d : ℕ} {U W : Finset (Vertex d)}
    (h : Disjoint U W) : Disjoint (issuedBondSet U) (issuedBondSet W) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp h (mem_product.mp he).1 (mem_product.mp hf).1

lemma sitesPlus_union {d : ℕ} (U W : Finset (Vertex d)) :
    sitesPlus (U ∪ W) = sitesPlus U ∪ sitesPlus W := by
  classical
  ext x
  simp only [sitesPlus, mem_union, mem_biUnion, mem_image, mem_univ, true_and]
  aesop

/-- Energy of a global potential, counted on exactly the source issued bonds. -/
noncomputable def issuedEnergy {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (v : Vertex d → ℝ) : ℝ :=
  ∑ e ∈ issuedBondSet U, (if ω e then (1 : ℝ) else 0) * (v (bondTip e) - v e.1) ^ 2

lemma issuedEnergy_eq_network {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (v : Vertex d → ℝ) :
    issuedEnergy U ω v = (issuedNetwork U).energy (domainWeights ω) (fun x => v x.val) := by
  classical
  simp only [issuedEnergy, Network.energy, Network.gradient, issuedNetwork,
    domainWeights, issuedBond]
  exact (Finset.sum_attach (issuedBondSet U) _).symm

/-- Potentials agreeing on U+ have exactly the same issued energy. -/
lemma issuedEnergy_congr_on {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) {u v : Vertex d → ℝ}
    (h : ∀ x ∈ sitesPlus U, u x = v x) :
    issuedEnergy U ω u = issuedEnergy U ω v := by
  classical
  apply Finset.sum_congr rfl
  intro e he
  have hb := (Finset.mem_product.mp he).1
  rw [h e.1 (base_mem_sitesPlus hb), h (bondTip e) (tip_mem_sitesPlus hb e.2)]

lemma issuedEnergy_union {d : ℕ} {U W : Finset (Vertex d)}
    (h : Disjoint U W) (ω : Configuration d) (v : Vertex d → ℝ) :
    issuedEnergy (U ∪ W) ω v = issuedEnergy U ω v + issuedEnergy W ω v := by
  classical
  unfold issuedEnergy
  rw [issuedBondSet_union, Finset.sum_union (issuedBondSet_disjoint h)]

lemma issuedEnergy_biUnion {d : ℕ} {I : Type*} (s : Finset I)
    (U : I → Finset (Vertex d))
    (h : (s : Set I).PairwiseDisjoint U)
    (ω : Configuration d) (v : Vertex d → ℝ) :
    issuedEnergy (s.biUnion U) ω v = ∑ i ∈ s, issuedEnergy (U i) ω v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [issuedEnergy, issuedBondSet]
  | @insert a s ha ih =>
    have hd : Disjoint (U a) (s.biUnion U) := by
      apply Finset.disjoint_left.mpr
      intro x hxa hxs
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hxs
      exact Finset.disjoint_left.mp
        (h (by simp) (by simp [hb]) (by intro hab; subst b; exact ha hb)) hxa hxb
    rw [Finset.biUnion_insert, issuedEnergy_union hd,
      ih (fun i hi j hj hij => h (by simp [hi]) (by simp [hj]) hij), Finset.sum_insert ha]

end NearCritical
