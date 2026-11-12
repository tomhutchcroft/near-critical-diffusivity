module

public import NearCritical.Section10TubeBonds

/-! Section10 fresh-tube independence on a fixed reveal-coordinate atom.
Actual source exploration must still identify its random history with such an
atom and its sprinkling observables with the retained fresh coordinate masks. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
open MeasureTheory

/-- The actual Bernoulli law factors the past observable and all fresh tube
observables simultaneously; independence is a conclusion, not a premise. -/
theorem percolation_reveal_freshTube_product {d : ℕ} (p : unitInterval)
    {ell : ℝ} (hell : 0 < ell) (ambient revealed : Finset (Bond d))
    (s : Finset ((Fin d → ℤ) × Fin d)) (H : (revealed → Bool) → ℝ)
    (f : ∀ e : (Fin d → ℤ) × Fin d,
      (freshCoarseTubeBonds ell ambient revealed e.1 e.2 → Bool) → ℝ) :
    (∫ ω : Configuration d, H (revealed.restrict ω) *
      (∏ e ∈ s, f e ((freshCoarseTubeBonds ell ambient revealed e.1 e.2).restrict ω))
        ∂percolation d p) =
      (∫ ω : Configuration d, H (revealed.restrict ω) ∂percolation d p) *
        (∏ e ∈ s, ∫ ω : Configuration d,
          f e ((freshCoarseTubeBonds ell ambient revealed e.1 e.2).restrict ω) ∂percolation d p) := by
  let B : Option ((Fin d → ℤ) × Fin d) → Finset (Bond d)
    | none => revealed
    | some e => freshCoarseTubeBonds ell ambient revealed e.1 e.2
  let F : ∀ z : Option ((Fin d → ℤ) × Fin d), (B z → Bool) → ℝ := fun z =>
    match z with
    | none => H
    | some e => f e
  let t : Finset (Option ((Fin d → ℤ) × Fin d)) := insert none (s.image some)
  have hd : (t : Set _).PairwiseDisjoint B := by
    intro u _ v _ huv
    cases u with
    | none =>
      cases v with
      | none => exact (huv rfl).elim
      | some v => exact revealed_disjoint_freshCoarseTubeBonds ell ambient revealed v.1 v.2
    | some u =>
      cases v with
      | none => exact (revealed_disjoint_freshCoarseTubeBonds ell ambient revealed u.1 u.2).symm
      | some v =>
        exact freshCoarseTubeBonds_disjoint hell ambient revealed u.1 v.1 u.2 v.2
          (fun h => huv (congrArg some h))
  have hp (g : Option ((Fin d → ℤ) × Fin d) → ℝ) :
      (∏ z ∈ t, g z) = g none*(∏ e ∈ s, g (some e)) := by
    dsimp only [t]
    rw [Finset.prod_insert (by simp)]
    rw [Finset.prod_image (by intro a _ b _ hab; exact Option.some.inj hab)]
  have h := percolation_disjoint_block_product p t B hd F
  simp_rw [hp] at h
  exact h

/-- On a positive atom of the fixed revealed-coordinate restriction, the
normalized actual restricted expectation factors over the fresh source tubes.
No conditional-independence or product-law hypothesis is supplied. -/
theorem percolation_freshTube_product_on_reveal_atom {d : ℕ} (p : unitInterval)
    {ell : ℝ} (hell : 0 < ell) (ambient revealed : Finset (Bond d))
    (η : revealed → Bool) (s : Finset ((Fin d → ℤ) × Fin d))
    (f : ∀ e : (Fin d → ℤ) × Fin d,
      (freshCoarseTubeBonds ell ambient revealed e.1 e.2 → Bool) → ℝ)
    (hη : 0 < (percolation d p).real {ω | revealed.restrict ω = η}) :
    (∫ ω : Configuration d, if revealed.restrict ω = η then
      (∏ e ∈ s, f e ((freshCoarseTubeBonds ell ambient revealed e.1 e.2).restrict ω)) else 0
        ∂percolation d p) / (percolation d p).real {ω | revealed.restrict ω = η} =
      ∏ e ∈ s, ∫ ω : Configuration d,
        f e ((freshCoarseTubeBonds ell ambient revealed e.1 e.2).restrict ω) ∂percolation d p := by
  let H : (revealed → Bool) → ℝ := fun ξ => if ξ = η then 1 else 0
  have h := percolation_reveal_freshTube_product p hell ambient revealed s H f
  have hm : MeasurableSet {ω : Configuration d | revealed.restrict ω = η} := by
    change MeasurableSet ((revealed.restrict : Configuration d → (revealed → Bool)) ⁻¹' {η})
    exact (measurableSet_singleton η).preimage (Finset.measurable_restrict revealed)
  have hmass : (∫ ω : Configuration d, H (revealed.restrict ω) ∂percolation d p) =
      (percolation d p).real {ω | revealed.restrict ω = η} := by
    have he : (fun ω : Configuration d => H (revealed.restrict ω)) =
        ({ω : Configuration d | revealed.restrict ω = η} : Set (Configuration d)).indicator
          (fun _ => (1:ℝ)) := by
      funext ω
      simp [H,Set.indicator]
    rw [he,integral_indicator_const _ hm]
    simp
  rw [hmass] at h
  have hnum : (∫ ω : Configuration d, if revealed.restrict ω = η then
      (∏ e ∈ s, f e ((freshCoarseTubeBonds ell ambient revealed e.1 e.2).restrict ω)) else 0
        ∂percolation d p) =
      (percolation d p).real {ω | revealed.restrict ω = η} *
        (∏ e ∈ s, ∫ ω : Configuration d,
          f e ((freshCoarseTubeBonds ell ambient revealed e.1 e.2).restrict ω) ∂percolation d p) := by
    simpa only [H,ite_mul,one_mul,zero_mul] using h
  rw [hnum]
  field_simp [hη.ne']

end NearCritical.Section10
