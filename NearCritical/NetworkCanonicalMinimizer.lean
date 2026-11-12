module

public import NearCritical.Minimizer
public import NearCritical.NetworkVoltageUniqueness

/-! The source's canonical convention on boundary-free components. Keep the
unique harmonic values on boundary-connected components and use one prescribed
constant elsewhere. The source takes the literal average of boundary values;
the generic selector also permits any other prescribed constant. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open Set Finset
open scoped Classical
variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

def HasBoundaryAccess (a : E → ℝ) (boundary : Set V) (x : V) : Prop :=
  ∃ z ∈ boundary, (G.positiveGraph a Set.univ).Reachable x z

omit [Fintype E] in
lemma hasBoundaryAccess_of_mem {a : E → ℝ} {boundary : Set V} {x : V} (hx : x ∈ boundary) :
    G.HasBoundaryAccess a boundary x := ⟨x, hx, SimpleGraph.Reachable.refl x⟩

omit [Fintype E] in
lemma hasBoundaryAccess_edge_iff {a : E → ℝ} {boundary : Set V} (e : E) (he : 0 < a e) :
    G.HasBoundaryAccess a boundary (G.tail e) ↔ G.HasBoundaryAccess a boundary (G.head e) := by
  by_cases hne : G.tail e = G.head e
  · rw [hne]
  have hadj := G.positiveGraph_adj_of_edge (S := Set.univ) e he hne (Set.mem_univ _) (Set.mem_univ _)
  constructor
  · rintro ⟨z, hz, hpath⟩
    exact ⟨z, hz, hadj.symm.reachable.trans hpath⟩
  · rintro ⟨z, hz, hpath⟩
    exact ⟨z, hz, hadj.reachable.trans hpath⟩

def canonicalizePotential (a : E → ℝ) (boundary : Set V) (c : ℝ) (u : V → ℝ) (x : V) : ℝ :=
  if G.HasBoundaryAccess a boundary x then u x else c

omit [Fintype E] in
lemma gradient_canonicalize_of_positive {a : E → ℝ} (boundary : Set V) (c : ℝ)
    (u : V → ℝ) (e : E) (he : 0 < a e) :
    G.gradient (G.canonicalizePotential a boundary c u) e =
      if G.HasBoundaryAccess a boundary (G.tail e) then G.gradient u e else 0 := by
  have heq := G.hasBoundaryAccess_edge_iff (boundary := boundary) e he
  by_cases ht : G.HasBoundaryAccess a boundary (G.tail e)
  · have hh := heq.mp ht
    simp [gradient, canonicalizePotential, ht, hh]
  · have hh : ¬G.HasBoundaryAccess a boundary (G.head e) := fun h ↦ ht (heq.mpr h)
    simp [gradient, canonicalizePotential, ht, hh]

/-- Removing voltage fluctuations in components that miss the boundary cannot
increase energy. This holds even before assuming that u is a minimizer. -/
theorem energy_canonicalize_le {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (c : ℝ) (u : V → ℝ) :
    G.energy a (G.canonicalizePotential a boundary c u) ≤ G.energy a u := by
  apply Finset.sum_le_sum
  intro e _
  by_cases he : a e = 0
  · simp [he]
  have hpos : 0 < a e := lt_of_le_of_ne (ha e) (Ne.symm he)
  rw [G.gradient_canonicalize_of_positive boundary c u e hpos]
  by_cases ht : G.HasBoundaryAccess a boundary (G.tail e)
  · simp [ht]
  · simp only [ite_eq_right ht, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg (ha e) (sq_nonneg _)

def canonicalMinimizer [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) (c : ℝ) : V → ℝ :=
  G.canonicalizePotential a boundary c (G.minimizer ha boundary data)

/-- Canonicalizing the arbitrary selected minimizer realizes the same Dirichlet
minimum, and is constant c on every component not touching the boundary. -/
theorem canonicalMinimizer_spec [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) (c : ℝ) :
    G.IsMinimizer a boundary data (G.canonicalMinimizer ha boundary data c) := by
  have ho := G.minimizer_spec ha boundary data
  refine ⟨?_, ?_⟩
  · intro x hx
    have haccess := G.hasBoundaryAccess_of_mem (a := a) hx
    simpa only [canonicalMinimizer, canonicalizePotential, ite_eq_left haccess] using ho.1 x hx
  · intro v hv
    exact (G.energy_canonicalize_le ha boundary c (G.minimizer ha boundary data)).trans (ho.2 v hv)

lemma canonicalMinimizer_eq_constant [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) (c : ℝ) {x : V}
    (hx : ¬G.HasBoundaryAccess a boundary x) : G.canonicalMinimizer ha boundary data c x = c := by
  simp [canonicalMinimizer, canonicalizePotential, hx]

/-- Any source-prescribed minimizer with the same boundary-free constant equals
this canonical selector pointwise. No hidden choice of such constants remains. -/
theorem IsMinimizer.eq_canonicalMinimizer [Fintype V] {a : E → ℝ} {boundary : Set V}
    {data u : V → ℝ} (hu : G.IsMinimizer a boundary data u) (ha : ∀ e, 0 ≤ a e) (c : ℝ)
    (hc : ∀ x, ¬G.HasBoundaryAccess a boundary x → u x = c) :
    u = G.canonicalMinimizer ha boundary data c := by
  funext x
  by_cases hx : G.HasBoundaryAccess a boundary x
  · exact hu.eq_of_boundary_access G (G.canonicalMinimizer_spec ha boundary data c) ha hx
  · rw [hc x hx, G.canonicalMinimizer_eq_constant ha boundary data c hx]

/-- Canonical and arbitrary minimizers have identical positive-edge gradients. -/
theorem canonicalMinimizer_gradient_eq [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) (c : ℝ) (e : E) (he : 0 < a e) :
    G.gradient (G.canonicalMinimizer ha boundary data c) e =
      G.gradient (G.minimizer ha boundary data) e :=
  (G.canonicalMinimizer_spec ha boundary data c).gradient_eq_of_same_data G
    (G.minimizer_spec ha boundary data) ha e he

/-- The canonical convention preserves the maximum-principle range whenever
its boundary-free constant lies in the same interval as the Dirichlet data. -/
theorem canonicalMinimizer_mem_Icc [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) {c lo hi : ℝ} (hc : c ∈ Icc lo hi)
    (hdata : ∀ x ∈ boundary, data x ∈ Icc lo hi) (x : V) :
    G.canonicalMinimizer ha boundary data c x ∈ Icc lo hi := by
  obtain ⟨v, hv, hvrange⟩ := G.exists_minimizer_in_Icc ha boundary data (hc.1.trans hc.2) hdata
  by_cases hx : G.HasBoundaryAccess a boundary x
  · have heq := (G.canonicalMinimizer_spec ha boundary data c).eq_of_boundary_access G hv ha hx
    rw [heq]
    exact hvrange x
  · rw [G.canonicalMinimizer_eq_constant ha boundary data c hx]
    exact hc

/-- The source boundary-average convention therefore has the same uniform gradient
bound as a bounded minimizer, even across closed edges. -/
theorem canonicalMinimizer_gradient_abs_le [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) {c lo hi : ℝ} (hc : c ∈ Icc lo hi)
    (hdata : ∀ x ∈ boundary, data x ∈ Icc lo hi) (e : E) :
    |G.gradient (G.canonicalMinimizer ha boundary data c) e| ≤ hi - lo :=
  G.gradient_abs_le_of_range (G.canonicalMinimizer_mem_Icc ha boundary data hc hdata) e

lemma canonicalMinimizer_energy_eq_conductance [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) (c : ℝ) :
    G.energy a (G.canonicalMinimizer ha boundary data c) = G.conductance a boundary data :=
  ((G.canonicalMinimizer_spec ha boundary data c).conductance_eq G ha).symm

/-- Literal average of the boundary values. This keeps the source's convention
precise even if the two extreme faces have unequal numbers of vertices. -/
def boundaryDataAverage [Fintype V] (boundary : Set V) (data : V → ℝ) : ℝ :=
  (∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ boundary), data x) /
    ((Finset.univ.filter (fun x ↦ x ∈ boundary)).card : ℝ)

omit [Fintype E] in
lemma boundaryDataAverage_mem_Icc [Fintype V] {boundary : Set V} {data : V → ℝ}
    (hne : boundary.Nonempty) {lo hi : ℝ} (hdata : ∀ x ∈ boundary, data x ∈ Icc lo hi) :
    boundaryDataAverage boundary data ∈ Icc lo hi := by
  let S : Finset V := Finset.univ.filter (fun x ↦ x ∈ boundary)
  obtain ⟨x, hx⟩ := hne
  have hS : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hlo : ∑ x ∈ S, lo ≤ ∑ x ∈ S, data x :=
    Finset.sum_le_sum (fun x hx ↦ (hdata x (Finset.mem_filter.mp hx).2).1)
  have hhi : ∑ x ∈ S, data x ≤ ∑ x ∈ S, hi :=
    Finset.sum_le_sum (fun x hx ↦ (hdata x (Finset.mem_filter.mp hx).2).2)
  change (∑ x ∈ S, data x) / (S.card : ℝ) ∈ Icc lo hi
  constructor
  · apply (le_div_iff₀ hcard).mpr
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hlo
  · apply (div_le_iff₀ hcard).mpr
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hhi

/-- A canonical minimizer with the literal boundary-average convention of
`eq.def.aU`; its existence does not depend on how arbitrary minima were chosen. -/
def boundaryAverageMinimizer [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) : V → ℝ :=
  G.canonicalMinimizer ha boundary data (boundaryDataAverage boundary data)

lemma boundaryAverageMinimizer_spec [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) :
    G.IsMinimizer a boundary data (G.boundaryAverageMinimizer ha boundary data) :=
  G.canonicalMinimizer_spec ha boundary data _

lemma boundaryAverageMinimizer_eq_constant [Fintype V] {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) {x : V} (hx : ¬G.HasBoundaryAccess a boundary x) :
    G.boundaryAverageMinimizer ha boundary data x = boundaryDataAverage boundary data :=
  G.canonicalMinimizer_eq_constant ha boundary data _ hx

theorem boundaryAverageMinimizer_gradient_abs_le [Fintype V] {a : E → ℝ}
    (ha : ∀ e, 0 ≤ a e) (boundary : Set V) (data : V → ℝ) (hne : boundary.Nonempty)
    {lo hi : ℝ} (hdata : ∀ x ∈ boundary, data x ∈ Icc lo hi) (e : E) :
    |G.gradient (G.boundaryAverageMinimizer ha boundary data) e| ≤ hi - lo :=
  G.canonicalMinimizer_gradient_abs_le ha boundary data (boundaryDataAverage_mem_Icc hne hdata) hdata e

end NearCritical.Network
