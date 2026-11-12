module

public import NearCritical.Section10CoupledPairMass

/-! A prescribed member produced by a fresh tube can be tested after
an earlier arrival even when the incoming nest depends on the past. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- A uniform fresh-tube bound holds after an adaptive choice of incoming
state. The earlier weight or membership indicator can read the same past
as the state. This is the tower step for arrivals through different tubes. -/
theorem adaptive_fresh_occupation_integral_le {d : ℕ} {X : Type*} [Fintype X]
    (p q : unitInterval) (R T : Finset (LBond d)) (hd : Disjoint R T)
    (state : (R → Bool) → X) (G : Configuration d × Configuration d → ℝ)
    (hG : IsLocal R G) (hG₀ : ∀ z, 0 ≤ G z)
    (f : X → Configuration d × Configuration d → ℝ)
    (hf : ∀ x, IsLocal T (f x)) {c : ℝ}
    (hc : ∀ x, (∫ z, f x z ∂((percolation d p).prod (percolation d q))) ≤ c) :
    (∫ z, G z * f (state (R.restrict (layerVal z))) z
      ∂((percolation d p).prod (percolation d q))) ≤
      (∫ z, G z ∂((percolation d p).prod (percolation d q))) * c := by
  let μ := (percolation d p).prod (percolation d q)
  let H (x : X) (z : Configuration d × Configuration d) :=
    if state (R.restrict (layerVal z)) = x then G z else 0
  have hH (x : X) : IsLocal R (H x) := by
    obtain ⟨g, hg⟩ := hG
    exact ⟨fun a => if state a = x then g a else 0, fun z => by simp only [H, hg z]⟩
  have hH₀ (x : X) (z : Configuration d × Configuration d) : 0 ≤ H x z := by
    simp only [H]
    split_ifs
    · exact hG₀ z
    · exact le_rfl
  have hpart (z : Configuration d × Configuration d) (a : X → ℝ) :
      ∑ x, H x z * a x = G z * a (state (R.restrict (layerVal z))) := by
    rw [Finset.sum_eq_single (state (R.restrict (layerVal z)))]
    · simp [H]
    · intro x _ hx
      simp [H, Ne.symm hx]
    · simp
  have hsum : (∑ x, ∫ z, H x z ∂μ) = ∫ z, G z ∂μ := by
    rw [← integral_finsetSum _ (fun x _ => (hH x).integrable p q)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by simpa using hpart z (fun _ => 1)
  change (∫ z, _ ∂μ) ≤ _
  calc
    _ = ∫ z, ∑ x, H x z * f x z ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => (hpart z (fun x => f x z)).symm
    _ = ∑ x, ∫ z, H x z * f x z ∂μ :=
      integral_finsetSum _ (fun x _ => ((hH x).mul_union (hf x)).integrable p q)
    _ = ∑ x, (∫ z, H x z ∂μ) * (∫ z, f x z ∂μ) :=
      Finset.sum_congr rfl (fun x _ => IsLocal.integral_mul p q hd (hH x) (hf x))
    _ ≤ ∑ x, (∫ z, H x z ∂μ) * c :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hc x) (integral_nonneg (hH₀ x))
    _ = _ := by rw [← Finset.sum_mul, hsum]

end NearCritical.Section10
