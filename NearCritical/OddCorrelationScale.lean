module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-! Explicit odd correlation heights for the paper's new conductivity upper bound.
Rounding is proved, rather than identifying an even floor with an odd cube side. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- Largest odd integer at most t, when t>=1. -/
def oddCorrelationHeight (t : ℝ) : ℕ := 2*⌊(t-1)/2⌋₊+1

lemma oddCorrelationHeight_odd (t : ℝ) : Odd (oddCorrelationHeight t) := by
  refine ⟨⌊(t-1)/2⌋₊, ?_⟩
  unfold oddCorrelationHeight
  omega

lemma oddCorrelationHeight_pos (t : ℝ) : 0 < oddCorrelationHeight t := by
  unfold oddCorrelationHeight
  omega

lemma oddCorrelationHeight_bounds {t : ℝ} (ht : 4 ≤ t) :
    t/2 ≤ (oddCorrelationHeight t : ℝ) ∧ (oddCorrelationHeight t : ℝ) ≤ t := by
  have hlo := Nat.lt_floor_add_one ((t-1)/2)
  have hhi := Nat.floor_le (by linarith : 0 ≤ (t-1)/2)
  have he : (oddCorrelationHeight t : ℝ) = 2*(⌊(t-1)/2⌋₊ : ℝ)+1 := by
    simp [oddCorrelationHeight]
  rw [he]
  constructor <;> linarith

def correlationHeight (sharp gap : ℝ) : ℕ :=
  oddCorrelationHeight (Real.sqrt (sharp/gap))

lemma correlation_sqrt_ge_four {sharp gap : ℝ} (_hsharp : 0 < sharp) (hgap : 0 < gap)
    (hsmall : gap ≤ sharp/16) : 4 ≤ Real.sqrt (sharp/gap) := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hgap).mpr
  nlinarith

lemma correlationHeight_bounds {sharp gap : ℝ} (hsharp : 0 < sharp) (hgap : 0 < gap)
    (hsmall : gap ≤ sharp/16) :
    Real.sqrt (sharp/gap)/2 ≤ (correlationHeight sharp gap : ℝ) ∧
      (correlationHeight sharp gap : ℝ) ≤ Real.sqrt (sharp/gap) :=
  oddCorrelationHeight_bounds (correlation_sqrt_ge_four hsharp hgap hsmall)

/-- The rounded odd side remains INSIDE the allowed near-critical window. -/
theorem correlationHeight_window {sharp gap : ℝ} (hsharp : 0 < sharp) (hgap : 0 < gap)
    (hsmall : gap ≤ sharp/16) :
    gap ≤ sharp/(correlationHeight sharp gap : ℝ)^2 := by
  have hh : 0 < (correlationHeight sharp gap : ℝ) := by
    exact_mod_cast oddCorrelationHeight_pos (Real.sqrt (sharp/gap))
  have hb := (correlationHeight_bounds hsharp hgap hsmall).2
  have hsquare := (sq_le_sq₀ hh.le (Real.sqrt_nonneg _)).mpr hb
  have ht := Real.sq_sqrt (div_pos hsharp hgap).le
  apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
  calc
    _ ≤ gap*(Real.sqrt (sharp/gap))^2 := mul_le_mul_of_nonneg_left hsquare hgap.le
    _ = sharp := by rw [ht]; field_simp

/-- Source h^-6 becomes gap³ with an explicit constant, independent of gap. -/
theorem correlationHeight_inverse_six {sharp gap : ℝ} (hsharp : 0 < sharp)
    (hgap : 0 < gap) (hsmall : gap ≤ sharp/16) :
    1/(correlationHeight sharp gap : ℝ)^6 ≤ 64*gap^3/sharp^3 := by
  let t := Real.sqrt (sharp/gap)
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hsharp hgap)
  have hh : 0 < (correlationHeight sharp gap : ℝ) := by
    exact_mod_cast oddCorrelationHeight_pos (Real.sqrt (sharp/gap))
  have hb := (correlationHeight_bounds hsharp hgap hsmall).1
  have hinv : 1/(correlationHeight sharp gap : ℝ) ≤ 2/t := by
    apply (div_le_div_iff₀ hh ht).mpr
    change 1*t ≤ 2*(correlationHeight sharp gap : ℝ)
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1/(correlationHeight sharp gap : ℝ)) hinv 6
  have ht2 : t^2 = sharp/gap := Real.sq_sqrt (div_pos hsharp hgap).le
  have ht6 : t^6 = (sharp/gap)^3 := by calc
    _ = (t^2)^3 := by ring
    _ = _ := by rw [ht2]
  calc
    _ = (1/(correlationHeight sharp gap : ℝ))^6 := by rw [div_pow]; norm_num
    _ ≤ (2/t)^6 := hp
    _ = 64*gap^3/sharp^3 := by rw [div_pow, ht6]; norm_num; field_simp

/-- Any prescribed large-height cutoff is met by taking a sufficiently small
gap, with explicit constants; this is used for the shifted parameter window. -/
lemma correlationHeight_ge_of_gap_bound {sharp gap H : ℝ}
    (hsharp : 0 < sharp) (hgap : 0 < gap) (hsmall : gap ≤ sharp/16)
    (hH : 0 < H) (hcut : gap ≤ sharp/(4*H^2)) :
    H ≤ (correlationHeight sharp gap : ℝ) := by
  have hs : 2*H ≤ Real.sqrt (sharp/gap) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hgap).mpr
    have hc := (le_div_iff₀ (by positivity : 0 < 4*H^2)).mp hcut
    nlinarith
  have hh := (correlationHeight_bounds hsharp hgap hsmall).1
  linarith

end NearCritical
