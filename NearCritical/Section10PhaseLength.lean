module

public import NearCritical.Section10TerminalPhase

/-! Section10 prop.nw.pair Step 5 (repaired): weighted phase length with the
2/3 contraction applied to NONTERMINAL shared steps only and one terminal
rho^2 factor.
Draft, not compiled. Scalar: a r = weighted mass that the phase is
still running after r nonterminal steps. Actual phase kernel remains OPEN. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped BigOperators

theorem phase_mass_geometric (a : ℕ → ℝ) {E : ℝ} (h0 : a 0 ≤ E)
    (hstep : ∀ r, a (r+1) ≤ (2/3:ℝ)*a r) (r : ℕ) : a r ≤ E*(2/3:ℝ)^r := by
  induction r with
  | zero => simpa using h0
  | succ r ih =>
    calc a (r+1) ≤ (2/3:ℝ)*a r := hstep r
      _ ≤ (2/3:ℝ)*(E*(2/3:ℝ)^r) := by gcongr
      _ = E*(2/3:ℝ)^(r+1) := by ring

/-- Repaired source bound: weighted phase length <= 4 * entry price. -/
theorem weighted_phase_length_le_four (a : ℕ → ℝ) {E ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4) (hE : 0 ≤ E) (h0 : a 0 ≤ E)
    (hstep : ∀ r, a (r+1) ≤ (2/3:ℝ)*a r) (n : ℕ) :
    (1+ε/2)^2*(∑ r ∈ Finset.range n, a r) ≤ 4*E := by
  have hsum : (∑ r ∈ Finset.range n, a r) ≤ E*(∑ r ∈ Finset.range n, (2/3:ℝ)^r) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => phase_mass_geometric a h0 hstep r)
  have hρ : 0 ≤ (1+ε/2)^2 := sq_nonneg _
  have hk := finite_phase_terminal_factor_le_four hε hsmall n
  calc (1+ε/2)^2*(∑ r ∈ Finset.range n, a r)
      ≤ (1+ε/2)^2*(E*(∑ r ∈ Finset.range n, (2/3:ℝ)^r)) := by gcongr
    _ = E*((1+ε/2)^2*(∑ r ∈ Finset.range n, (2/3:ℝ)^r)) := by ring
    _ ≤ E*4 := by gcongr
    _ = 4*E := by ring

/-- Summing over at most 4N+1 phase-start steps (source Step 5). -/
theorem phase_starts_total_le {ε E : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4) (hE : 0 ≤ E)
    (S : Finset ℕ) (N : ℕ) (hS : S.card ≤ 4*N+1) (a : ℕ → ℕ → ℝ)
    (h0 : ∀ u ∈ S, a u 0 ≤ E) (hstep : ∀ u ∈ S, ∀ r, a u (r+1) ≤ (2/3:ℝ)*a u r)
    (n : ℕ) :
    (∑ u ∈ S, (1+ε/2)^2*(∑ r ∈ Finset.range n, a u r)) ≤ 4*E*(4*N+1) := by
  calc (∑ u ∈ S, (1+ε/2)^2*(∑ r ∈ Finset.range n, a u r))
      ≤ ∑ _u ∈ S, 4*E :=
        Finset.sum_le_sum (fun u hu =>
          weighted_phase_length_le_four (a u) hε hsmall hE (h0 u hu) (hstep u hu) n)
    _ = S.card*(4*E) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((4*N+1:ℕ):ℝ)*(4*E) := by gcongr
    _ = 4*E*(4*N+1) := by push_cast; ring

end NearCritical.Section10
