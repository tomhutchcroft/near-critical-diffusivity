module

public import NearCritical.SubcriticalSeed
public import NearCritical.OddCorrelationScale
public import Mathlib.Analysis.Asymptotics.Lemmas

/-! The actual subcritical starting parameter lies in the permitted compact
window at large correlation height; this is proved, not assumed for all h. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Filter
open scoped Topology

lemma subcriticalSeedParameter_tendsto (pc c : ℝ) :
    Tendsto (subcriticalSeedParameter pc c) atTop (𝓝 pc) := by
  have hlog : Tendsto (fun h : ℝ ↦ Real.log h/h) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have H := ((hlog.const_mul (7/c)).pow 2).const_sub pc
  have he : subcriticalSeedParameter pc c =
      fun h ↦ pc-((7/c)*(Real.log h/h))^2 := by
    funext h
    unfold subcriticalSeedParameter
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  simpa using H

lemma subcriticalSeedParameter_eventually_window {pc : ℝ} (hpc : 0 < pc) (c : ℝ) :
    ∀ᶠ h : ℝ in atTop, pc/2 ≤ subcriticalSeedParameter pc c h ∧
      subcriticalSeedParameter pc c h ≤ pc := by
  have he := (subcriticalSeedParameter_tendsto pc c).eventually
    (lt_mem_nhds (by linarith : pc/2 < pc))
  filter_upwards [he] with h hh
  exact ⟨hh.le, subcriticalSeedParameter_le pc c h⟩

/-- A single positive gap cutoff makes the selected odd height large enough
for the source's subcritical endpoint to be in [pc/2,pc]. -/
theorem correlation_seed_window {pc sharp : ℝ} (hpc : 0 < pc) (hsharp : 0 < sharp)
    (c : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ∀ gap : ℝ, 0 < gap → gap ≤ ε →
      pc/2 ≤ subcriticalSeedParameter pc c (correlationHeight sharp gap : ℝ) ∧
        subcriticalSeedParameter pc c (correlationHeight sharp gap : ℝ) ≤ pc := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp (subcriticalSeedParameter_eventually_window hpc c)
  let R := max H 2
  have hR : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_right _ _)
  refine ⟨min (sharp/16) (sharp/(4*R^2)), lt_min (by positivity) (by positivity), ?_⟩
  intro gap hgap hsmall
  have hcut := correlationHeight_ge_of_gap_bound hsharp hgap
    (hsmall.trans (min_le_left _ _)) hR (hsmall.trans (min_le_right _ _))
  exact hH _ ((le_max_left H 2).trans hcut)

end NearCritical
