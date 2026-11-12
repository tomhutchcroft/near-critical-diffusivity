module

public import NearCritical.Harmonic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Real

/-! Attainment of finite-network Dirichlet energies, including zero weights.
Clamping competitors to the range of the boundary data reduces the energy.
The extreme value theorem then supplies a minimizer on a compact box. -/
@[expose] public section
namespace NearCritical.Network
open Set
variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

noncomputable def clamp (lo hi : ℝ) (h : lo ≤ hi) (u : V → ℝ) (x : V) : ℝ :=
  Set.projIcc lo hi h (u x)

lemma clamp_mem (lo hi : ℝ) (h : lo ≤ hi) (u : V → ℝ) (x : V) :
    clamp lo hi h u x ∈ Icc lo hi := (Set.projIcc lo hi h (u x)).property

lemma clamp_eq {lo hi : ℝ} (h : lo ≤ hi) {u : V → ℝ} {x : V}
    (hx : u x ∈ Icc lo hi) : clamp lo hi h u x = u x := by
  exact congrArg Subtype.val (Set.projIcc_of_mem h hx)

lemma energy_clamp_le {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    {lo hi : ℝ} (h : lo ≤ hi) (u : V → ℝ) :
    G.energy a (clamp lo hi h u) ≤ G.energy a u := by
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (ha e)
  apply sq_le_sq.mpr
  have hc := (LipschitzWith.projIcc h).dist_le_mul (u (G.head e)) (u (G.tail e))
  simpa only [clamp, gradient, Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using hc

lemma continuous_energy (a : E → ℝ) : Continuous (G.energy a) := by
  unfold energy gradient
  apply continuous_finsetSum
  intro e _
  fun_prop

lemma isClosed_admissible (boundary : Set V) (data : V → ℝ) :
    IsClosed {u : V → ℝ | admissible boundary data u} := by
  simp only [admissible, Set.ofPred_forall]
  exact isClosed_iInter (fun x ↦ isClosed_iInter
    (fun _ ↦ isClosed_eq (continuous_apply x) continuous_const))

/-- A minimizer can be chosen within any interval containing the Dirichlet data.
The data outside the boundary need not lie in that interval. -/
theorem exists_minimizer_in_Icc [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) {lo hi : ℝ} (h : lo ≤ hi)
    (hdata : ∀ x ∈ boundary, data x ∈ Icc lo hi) :
    ∃ u, G.IsMinimizer a boundary data u ∧ ∀ x, u x ∈ Icc lo hi := by
  classical
  let K : Set (V → ℝ) := Icc (fun _ ↦ lo) (fun _ ↦ hi) ∩
    {u | admissible boundary data u}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_admissible boundary data)
  have hne : K.Nonempty := by
    refine ⟨clamp lo hi h data,
      ⟨fun x ↦ (clamp_mem _ _ _ _ x).1, fun x ↦ (clamp_mem _ _ _ _ x).2⟩, ?_⟩
    exact fun x hx ↦ clamp_eq h (hdata x hx)
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne (G.continuous_energy a).continuousOn
  refine ⟨u, ⟨hu.2, ?_⟩, fun x ↦ ⟨hu.1.1 x, hu.1.2 x⟩⟩
  intro v hv
  have hc : clamp lo hi h v ∈ K := by
    refine ⟨⟨fun x ↦ (clamp_mem _ _ _ _ x).1,
      fun x ↦ (clamp_mem _ _ _ _ x).2⟩, ?_⟩
    intro x hx
    rw [clamp_eq h (by rw [hv x hx]; exact hdata x hx)]
    exact hv x hx
  exact (hmin hc).trans (G.energy_clamp_le ha h v)

/-- Finite Dirichlet energies attain their minimum even when the network is
not connected or every conductance vanishes. -/
theorem exists_minimizer [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) : ∃ u, G.IsMinimizer a boundary data u := by
  classical
  let M : ℝ := ∑ x, |data x|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun x _ ↦ abs_nonneg _)
  have hMM : -M ≤ M := by linarith
  have hdata (x : V) (_ : x ∈ boundary) : data x ∈ Icc (-M) M := by
    have hx : |data x| ≤ M := Finset.single_le_sum
      (fun y _ ↦ abs_nonneg (data y)) (Finset.mem_univ x)
    exact abs_le.mp hx
  obtain ⟨u, hu, _⟩ := G.exists_minimizer_in_Icc ha boundary data hMM hdata
  exact ⟨u, hu⟩

/-- A selected minimizer, with no uniqueness claim on isolated components. -/
noncomputable def minimizer [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) : V → ℝ :=
  Classical.choose (G.exists_minimizer ha boundary data)

lemma minimizer_spec [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) :
    G.IsMinimizer a boundary data (G.minimizer ha boundary data) :=
  Classical.choose_spec (G.exists_minimizer ha boundary data)

lemma conductance_eq_energy_minimizer [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) :
    G.conductance a boundary data = G.energy a (G.minimizer ha boundary data) :=
  (G.minimizer_spec ha boundary data).conductance_eq G ha

/-- The comparison formula for the actual variational minima. Existence of
both minimizers is supplied internally, including for degenerate weights. -/
theorem conductance_comparison [Fintype V] {a b : E → ℝ}
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) (boundary : Set V) (data : V → ℝ) :
    G.energy (b - a) (G.minimizer hb boundary data) ≤
      G.conductance b boundary data - G.conductance a boundary data ∧
    G.conductance b boundary data - G.conductance a boundary data =
      G.pairing (b - a) (G.minimizer hb boundary data) (G.minimizer ha boundary data) ∧
    G.conductance b boundary data - G.conductance a boundary data ≤
      G.energy (b - a) (G.minimizer ha boundary data) := by
  rw [G.conductance_eq_energy_minimizer hb, G.conductance_eq_energy_minimizer ha]
  have hu := G.minimizer_spec ha boundary data
  have hv := G.minimizer_spec hb boundary data
  exact ⟨(G.minimizer_comparison hu hv).1, G.minimizer_mixed_identity hu hv,
    (G.minimizer_comparison hu hv).2⟩

omit [Fintype E] in
/-- The maximum-principle range bound gives the gradient estimate used in
`eq.def.aU`, without requiring strict positivity of the edge conductances. -/
lemma gradient_abs_le_of_range {lo hi : ℝ} {u : V → ℝ}
    (hu : ∀ x, u x ∈ Icc lo hi) (e : E) : |G.gradient u e| ≤ hi - lo := by
  apply abs_le.mpr
  constructor <;> dsimp [gradient] <;>
    linarith [(hu (G.head e)).1, (hu (G.head e)).2,
      (hu (G.tail e)).1, (hu (G.tail e)).2]

end NearCritical.Network
