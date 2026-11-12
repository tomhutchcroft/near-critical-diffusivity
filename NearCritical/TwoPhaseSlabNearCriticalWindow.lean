module

public import NearCritical.TwoPhaseSlabNearCritical

/-! Positive-height source window convention for the actual mixed-slab bound.
The robust (m+1)(n+1) window is explicitly shrunk by four, not identified with
mn at zero or claimed to have the same constant without a comparison. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped ENNReal

/-- The literal positive-natural-height source convention, with ONE pair of
positive constants before every rate and height, and the full lower-p range. -/
theorem twoPhaseSlabPioneerMass_nearCritical_source_window {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (q : unitInterval), q ≤ criticalPoint d →
        ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (p : unitInterval),
          (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/((m : ℝ)*(n : ℝ)) →
          ∀ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∀ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
            twoPhaseSlabPioneerMass i p q m n k j ≤ ENNReal.ofReal
              (C*((n : ℝ)+1-(j : ℝ))*Real.exp
                (-C⁻¹*twoPhaseSlabDistance m k j*
                  Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)))) := by
  obtain ⟨C,ε,hC,hε,hbound⟩ := twoPhaseSlabPioneerMass_nearCritical i hB hb hpc hpc1 pioneers
  refine ⟨C,ε/4,hC,by positivity,?_⟩
  intro q hq m n hm hn p hpwindow k hk j hj
  have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : (m+1 : ℝ)*(n+1 : ℝ) ≤ 4*(m : ℝ)*(n : ℝ) := by
    calc
      _ ≤ (2*(m : ℝ))*(2*(n : ℝ)) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hquot : (ε/4)/((m : ℝ)*(n : ℝ)) ≤ ε/((m+1 : ℝ)*(n+1 : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < (m : ℝ)*(n : ℝ))
      (by positivity : 0 < (m+1 : ℝ)*(n+1 : ℝ))).mpr
    convert mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ ε/4) using 1 <;> ring
  exact hbound q hq m n p (hpwindow.trans (add_le_add le_rfl hquot)) k hk j hj

end NearCritical
