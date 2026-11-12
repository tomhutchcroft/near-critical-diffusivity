module

public import NearCritical.Section10CoupledWeight

/-! Cube (site) weights `omega_Gamma` on the actual coupled law.

`u a` is the normalised indicator of site `a` (in the source,
`1{Q(a) pre-good} / q`), local on the layered bonds `E a` of its cube; distinct
cubes have disjoint bonds.

* `integral_finset_prod`: independence of local functions on disjoint blocks,
  `E[prod_a f_a] = prod_a E[f_a]`.
* `siteWeight_mean`: `E[omega_Gamma] = 1`.
* `siteWeight_pair_le`: `E[omega_Gamma omega_Gamma'] <= kappa ^ #(common sites)`
  when `E[u_a^2] <= kappa` (in the source `kappa = 1/q`). This is the
  cube-indicator step of the second moment in `prop.nw.main` (5772).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

variable {A : Type*}

lemma isLocal_finset_prod {d : ℕ} (E : A → Finset (LBond d))
    (f : A → Configuration d × Configuration d → ℝ) (hf : ∀ a, IsLocal (E a) (f a))
    (c : Finset A) : IsLocal (c.biUnion E) (fun z => ∏ a ∈ c, f a z) := by
  induction c using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact isLocal_const _ 1
  | insert a c ha ih =>
    simp only [Finset.prod_insert ha, Finset.biUnion_insert]
    exact (hf a).mul_union ih

/-- Independence of local functions on pairwise disjoint blocks. -/
theorem integral_finset_prod {d : ℕ} (p q : unitInterval) (E : A → Finset (LBond d))
    (hE : ∀ a b, a ≠ b → Disjoint (E a) (E b))
    (f : A → Configuration d × Configuration d → ℝ) (hf : ∀ a, IsLocal (E a) (f a))
    (c : Finset A) :
    (∫ z, ∏ a ∈ c, f a z ∂((percolation d p).prod (percolation d q))) =
      ∏ a ∈ c, ∫ z, f a z ∂((percolation d p).prod (percolation d q)) := by
  induction c using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, integral_const, probReal_univ, one_smul]
  | insert a c ha ih =>
    simp only [Finset.prod_insert ha]
    have hd : Disjoint (E a) (c.biUnion E) := by
      rw [Finset.disjoint_biUnion_right]
      intro b hb
      exact hE a b (fun h => ha (h ▸ hb))
    rw [IsLocal.integral_mul p q hd (hf a) (isLocal_finset_prod E f hf c), ih]

/-- `E[omega_Gamma] = 1`. -/
theorem siteWeight_mean {d : ℕ} (p q : unitInterval) (E : A → Finset (LBond d))
    (hE : ∀ a b, a ≠ b → Disjoint (E a) (E b))
    (u : A → Configuration d × Configuration d → ℝ) (hu : ∀ a, IsLocal (E a) (u a))
    (hmean : ∀ a, (∫ z, u a z ∂((percolation d p).prod (percolation d q))) = 1)
    (c : Finset A) :
    (∫ z, ∏ a ∈ c, u a z ∂((percolation d p).prod (percolation d q))) = 1 := by
  rw [integral_finset_prod p q E hE u hu c]
  exact Finset.prod_eq_one (fun a _ => hmean a)

/-- `E[omega_Gamma omega_Gamma'] <= kappa ^ #(common sites)`. -/
theorem siteWeight_pair_le {d : ℕ} (p q : unitInterval) (E : A → Finset (LBond d))
    (hE : ∀ a b, a ≠ b → Disjoint (E a) (E b))
    (u : A → Configuration d × Configuration d → ℝ) (hu : ∀ a, IsLocal (E a) (u a))
    (hu0 : ∀ a z, 0 ≤ u a z)
    (hmean : ∀ a, (∫ z, u a z ∂((percolation d p).prod (percolation d q))) = 1)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hsq : ∀ a, (∫ z, u a z * u a z ∂((percolation d p).prod (percolation d q))) ≤ κ)
    (c c' : Finset A) :
    (∫ z, (∏ a ∈ c, u a z) * (∏ a ∈ c', u a z)
      ∂((percolation d p).prod (percolation d q))) ≤ κ ^ (c ∩ c').card := by
  obtain ⟨v, hv⟩ : ∃ v : A → Configuration d × Configuration d → ℝ, v = fun a z =>
      (if a ∈ c then u a z else 1) * (if a ∈ c' then u a z else 1) := ⟨_, rfl⟩
  have hvloc : ∀ a, IsLocal (E a) (v a) := by
    intro a
    rw [hv]
    by_cases h1 : a ∈ c <;> by_cases h2 : a ∈ c' <;>
      simp only [h1, h2, if_true, if_false, mul_one, one_mul]
    · exact (hu a).mul (hu a)
    · exact hu a
    · exact hu a
    · exact isLocal_const _ 1
  have hvint : ∀ a, (∫ z, v a z ∂((percolation d p).prod (percolation d q))) ≤
      if a ∈ c ∩ c' then κ else 1 := by
    intro a
    rw [hv]
    by_cases h1 : a ∈ c <;> by_cases h2 : a ∈ c' <;>
      simp only [h1, h2, Finset.mem_inter, and_self, and_true, and_false, if_true, if_false,
        mul_one, one_mul]
    · exact hsq a
    · exact (hmean a).le
    · exact (hmean a).le
    · simp only [integral_const, probReal_univ, one_smul, le_refl]
  have hpt : ∀ z, (∏ a ∈ c, u a z) * (∏ a ∈ c', u a z) = ∏ a ∈ c ∪ c', v a z := by
    intro z
    rw [hv]
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem]
    rw [Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
  have hv0 : ∀ a, 0 ≤ ∫ z, v a z ∂((percolation d p).prod (percolation d q)) := by
    intro a
    refine integral_nonneg (fun z => ?_)
    rw [hv]
    exact mul_nonneg (by split_ifs <;> first | exact hu0 a z | exact zero_le_one)
      (by split_ifs <;> first | exact hu0 a z | exact zero_le_one)
  simp only [hpt]
  rw [integral_finset_prod p q E hE v hvloc (c ∪ c')]
  refine (Finset.prod_le_prod₀ (fun a _ => hv0 a) (fun a _ => hvint a) : _ ≤ ∏ a ∈ c ∪ c', (if a ∈ c ∩ c' then κ else 1)).trans (le_of_eq ?_)
  rw [Finset.prod_ite_mem, Finset.prod_const]
  congr 2
  ext a
  simp only [Finset.mem_inter, Finset.mem_union]
  tauto

end NearCritical.Section10
