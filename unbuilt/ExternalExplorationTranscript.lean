module

public import NearCritical.ExternalFreshExploration
public import Essakine2026Tight.Mathlib.Probability.Process.SigmaPrefix

/-!
Combine the pinned Lattice-Probability fresh-read law with entropy-mdp's
measurable stopped-prefix machinery. Original licenses, notices, revisions
and source hashes are retained in third_party. Local native checks pending.

The transcript rule is a function of the observed Bool sequence, shared across
parameters when comparing laws. No graph-search construction, stopping-time
property, almost-sure finiteness or query-cost estimate is asserted here.
-/
@[expose] public section
namespace NearCritical.External
open MeasureTheory ProbabilityTheory

/-- The full observed sequence is measurable for any measurable bond-index rule. -/
theorem measurable_bond_read_path {d : ℕ}
    (idx : ℕ → Configuration d → Bond d) (hidx : ∀ n, Measurable (idx n)) :
    Measurable (fun ω n => ω (idx n ω)) := by
  exact measurable_pi_lambda _ (fun n =>
    LatticeProb.measurable_revealed hidx (fun _ => measurable_id) n)

/-- Any common measurable rule applied to fresh observed bits has its IID-input
law. In particular this transfers finite/stopped transcripts without comparing
KL divergences of the full infinite configuration laws. -/
theorem fresh_bond_transcript_law {d : ℕ} (p : unitInterval)
    (idx : ℕ → Configuration d → Bond d)
    (hidx : LatticeProb.IsExploration (X := fun _ : Bond d => Bool) idx)
    {T : Type*} [MeasurableSpace T] (F : (ℕ → Bool) → T) (hF : Measurable F) :
    (percolation d p).map (fun ω => F (fun n => ω (idx n ω))) =
      (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p)).map F := by
  rw [← fresh_bond_reads_law p idx hidx]
  exact (Measure.map_map hF (measurable_bond_read_path idx hidx.meas)).symm

/-- A measurable observation-sequence stopping rule gives the same stopped-prefix
law under the actual exploration and the corresponding IID observation input.
This law identity itself does not require the rule to be a stopping time. -/
theorem fresh_bond_stopped_prefix_law {d : ℕ} (p : unitInterval)
    (idx : ℕ → Configuration d → Bond d)
    (hidx : LatticeProb.IsExploration (X := fun _ : Bond d => Bool) idx)
    (τ : (ℕ → Bool) → WithTop ℕ) (hτ : Measurable τ) :
    (percolation d p).map (fun ω =>
      stoppedValue (sigmaPrefix (fun n (x : ℕ → Bool) => x n)) τ
        (fun n => ω (idx n ω))) =
      (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p)).map
        (stoppedValue (sigmaPrefix (fun n (x : ℕ → Bool) => x n)) τ) := by
  exact fresh_bond_transcript_law p idx hidx _
    (measurable_stoppedValue_sigmaPrefix (fun n => measurable_pi_apply n) hτ)

end NearCritical.External
