module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Tactic

@[expose] public section
namespace NearCritical

/-- Reflection fixing coordinate `i` and reversing every other coordinate. -/
def coordinateReflection {d : ℕ} (i : Fin d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun j => if j = i then x j else -x j

/-- The deterministic content of source `prop.chem.alldir`. The existence of
 the chemical norm, its normalization, and reflection symmetry are inputs. -/
theorem chemicalNorm_comparison {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ))
    (hunit : ∀ i, N (Pi.single i 1) = 1)
    (hreflect : ∀ i x, N (coordinateReflection i x) = N x)
    (x : Fin d → ℝ) :
    (∀ i, |x i| ≤ N x) ∧ N x ≤ ∑ i, |x i| := by
  constructor
  · intro i
    have hid : x + coordinateReflection i x = (2 * x i) • Pi.single i (1 : ℝ) := by
      ext j
      by_cases h : j = i
      · subst j; simp [coordinateReflection]; ring
      · simp [coordinateReflection, h]
    have h := map_add_le_add N x (coordinateReflection i x)
    rw [hid, map_smul_eq_mul, hunit, hreflect] at h
    simp only [Real.norm_eq_abs, abs_mul, mul_one] at h
    norm_num at h
    linarith
  · have hid : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply, Finset.sum_apply]
    have hsum (s : Finset (Fin d)) :
        N (∑ i ∈ s, x i • Pi.single i (1 : ℝ)) ≤
          ∑ i ∈ s, N (x i • Pi.single i (1 : ℝ)) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (map_add_le_add N _ _).trans (add_le_add le_rfl ih)
    calc
      N x = N (∑ i, x i • Pi.single i (1 : ℝ)) := congrArg N hid
      _ ≤ ∑ i, N (x i • Pi.single i (1 : ℝ)) := by simpa using hsum Finset.univ
      _ = ∑ i, |x i| := by simp [map_smul_eq_mul, hunit, Real.norm_eq_abs]

end NearCritical
