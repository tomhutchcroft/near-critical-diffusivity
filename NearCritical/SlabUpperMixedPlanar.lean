module

public import NearCritical.ExplorationDomination
public import NearCritical.Bernoulli

/-! The grimmett1999 input of prop.slab.upper, stated in infinite volume on the
lattice, and the per-box `mixed_ge` field of `RenormalizedExploration` DERIVED
from it.

* `mixedLatticeGraph β`: mixed site–bond graph on `ℤ^d` (open sites joined by
  open lattice bonds), `β : Vertex d ⊕ Bond d → Bool`.
* `MixedSiteBondPercolationInput d κ θ`: with all sites and bonds i.i.d. `κ`, the
  origin is open and in an infinite cluster with probability at least `θ`.
  `Grimmett1999PlanarMixedInput` is the cited planar statement (high density
  percolates); it is the ONLY literature content here.
* For every finite box `Bx ∋ 0`: the finite box graph (`boxBonds`, `boxEnds`),
  the restriction law `map boxRestrict (infinitePi κ) = Measure.pi κ`, and
  `mixedValue_box_ge`: the infinite-volume probability is at most the finite
  mixed probability that the open root reaches the inner boundary of the box. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Finset
open scoped ENNReal Classical

variable {d : ℕ}

abbrev MixedIndex (d : ℕ) := Vertex d ⊕ Bond d

/-- Mixed site–bond graph on the lattice. -/
def mixedLatticeGraph (β : MixedIndex d → Bool) : SimpleGraph (Vertex d) where
  Adj x y := β (.inl x) = true ∧ β (.inl y) = true ∧ ∃ e : Bond d, β (.inr e) = true ∧
    ((x = e.1 ∧ y = bondTip e) ∨ (y = e.1 ∧ x = bondTip e))
  symm := ⟨by
    rintro x y ⟨hx, hy, e, he, h | h⟩
    · exact ⟨hy, hx, e, he, Or.inr h⟩
    · exact ⟨hy, hx, e, he, Or.inl h⟩⟩
  loopless := ⟨by
    rintro x ⟨-, -, e, -, h | h⟩ <;> exact bondTip_ne_base e (h.2.symm.trans h.1)⟩

/-- The origin is open and lies in an infinite mixed cluster. -/
def mixedPercolationEvent (d : ℕ) : Set (MixedIndex d → Bool) :=
  {β | β (.inl 0) = true ∧ {y | (mixedLatticeGraph β).Reachable 0 y}.Infinite}

/-- Mixed site–bond percolation at the fixed single-coordinate law `κ`. -/
def MixedSiteBondPercolationInput (d : ℕ) (κ : Measure Bool) [IsProbabilityMeasure κ]
    (θ : ℝ≥0∞) : Prop :=
  θ ≤ Measure.infinitePi (fun _ : MixedIndex d => κ) (mixedPercolationEvent d)

/-- CITED (grimmett1999): planar mixed site–bond percolation with sites and bonds
open with probability at least `1 - ε` has an infinite cluster with positive
probability. -/
def Grimmett1999PlanarMixedInput : Prop :=
  ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ (κ : Measure Bool) [IsProbabilityMeasure κ], 1 - ε ≤ κ {true} →
    ∃ θ : ℝ≥0∞, θ ≠ 0 ∧ MixedSiteBondPercolationInput 2 κ θ

/-! Finite box graph. -/

/-- Lattice bonds with both endpoints in `Bx`. -/
def boxBonds (Bx : Finset (Vertex d)) : Finset (Bond d) :=
  (Bx ×ˢ (univ : Finset (Fin d))).filter (fun e => bondTip e ∈ Bx)

lemma mem_boxBonds (Bx : Finset (Vertex d)) {e : Bond d} :
    e ∈ boxBonds Bx ↔ e.1 ∈ Bx ∧ bondTip e ∈ Bx := by
  simp [boxBonds]

def boxEnds (Bx : Finset (Vertex d)) (e : boxBonds Bx) : Bx × Bx :=
  (⟨e.1.1, ((mem_boxBonds Bx).1 e.2).1⟩, ⟨bondTip e.1, ((mem_boxBonds Bx).1 e.2).2⟩)

/-- Box vertices with a lattice neighbour outside the box. -/
def boxInnerBoundary (Bx : Finset (Vertex d)) : Finset Bx :=
  univ.filter (fun v => ∃ y, y ∉ Bx ∧ (openGraph (fun _ => true)).Adj v.1 y)

/-- Restriction of a lattice mixed configuration to the box coordinates. -/
def boxRestrict (Bx : Finset (Vertex d)) (β : MixedIndex d → Bool) :
    Bx ⊕ boxBonds Bx → Bool
  | .inl v => β (.inl v.1)
  | .inr e => β (.inr e.1)

lemma measurable_boxRestrict (Bx : Finset (Vertex d)) : Measurable (boxRestrict Bx) := by
  refine measurable_pi_iff.2 fun j => ?_
  cases j with
  | inl v => exact measurable_pi_apply _
  | inr e => exact measurable_pi_apply _

/-- Box coordinates as a subset of lattice coordinates. -/
def boxIndexEquiv (Bx : Finset (Vertex d)) :
    (Bx ⊕ boxBonds Bx) ≃ (Bx.disjSum (boxBonds Bx)) :=
  Equiv.ofBijective
    (fun j => match j with
      | .inl v => ⟨.inl v.1, inl_mem_disjSum.2 v.2⟩
      | .inr e => ⟨.inr e.1, inr_mem_disjSum.2 e.2⟩) <| by
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Subtype.mk.injEq, Sum.inl.injEq,
        Sum.inr.injEq, reduceCtorEq] at h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact congrArg Sum.inr (Subtype.ext h)
    · rintro ⟨x | x, hx⟩
      · exact ⟨.inl ⟨x, inl_mem_disjSum.1 hx⟩, rfl⟩
      · exact ⟨.inr ⟨x, inr_mem_disjSum.1 hx⟩, rfl⟩

lemma boxRestrict_eq (Bx : Finset (Vertex d)) (β : MixedIndex d → Bool)
    (j : Bx ⊕ boxBonds Bx) : boxRestrict Bx β j = β (boxIndexEquiv Bx j : MixedIndex d) := by
  cases j <;> rfl

theorem map_boxRestrict (Bx : Finset (Vertex d)) (κ : Measure Bool) [IsProbabilityMeasure κ] :
    Measure.map (boxRestrict Bx) (Measure.infinitePi (fun _ : MixedIndex d => κ)) =
      Measure.pi (fun _ : Bx ⊕ boxBonds Bx => κ) := by
  set I := Bx.disjSum (boxBonds Bx)
  set E := boxIndexEquiv Bx
  apply Measure.ext_of_singleton
  intro x
  let η₀ : I → Bool := fun u => x (E.symm u)
  have hpre : boxRestrict Bx ⁻¹' {x} =
      (I.restrict : (MixedIndex d → Bool) → (I → Bool)) ⁻¹' {η₀} := by
    ext β
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext u
      show β u.1 = x (E.symm u)
      rw [← h, boxRestrict_eq, Equiv.apply_symm_apply]
    · intro h
      funext j
      rw [boxRestrict_eq]
      have := congrFun h (E j)
      change β (E j).1 = x (E.symm (E j)) at this
      rw [Equiv.symm_apply_apply] at this
      exact this
  have hm : (Measure.infinitePi (fun _ : MixedIndex d => κ)).map I.restrict =
      Measure.pi (fun _ : I => κ) :=
    Measure.infinitePi_map_restrict _
  rw [Measure.map_apply (measurable_boxRestrict Bx) (MeasurableSet.singleton x), hpre,
    ← Measure.map_apply (Finset.measurable_restrict _) (MeasurableSet.singleton η₀), hm]
  simp only [Measure.pi_singleton]
  exact (Fintype.prod_equiv E _ _ (fun j => by
    show _ = κ {x (E.symm (E j))}
    rw [Equiv.symm_apply_apply])).symm

/-- Deterministic exit argument: an open origin in an infinite lattice cluster
reaches the inner boundary of the box inside the box. -/
theorem boxRestrict_mem_mixedEvent (Bx : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Bx)
    {β : MixedIndex d → Bool} (hβ : β ∈ mixedPercolationEvent d) :
    boxRestrict Bx β ∈ mixedEvent (boxEnds Bx) (⟨0, h0⟩ : Bx) (boxInnerBoundary Bx)
      (⟨∅, ∅, ∅, ∅, ∅⟩ : ExploreState Bx (boxBonds Bx)) := by
  obtain ⟨h0open, hinf⟩ := hβ
  set σ : ExploreState Bx (boxBonds Bx) := ⟨∅, ∅, ∅, ∅, ∅⟩
  set G := mixedGraph (boxEnds Bx) σ (boxRestrict Bx β)
  have hsite : ∀ v : Bx, β (.inl v.1) = true → mixedSiteOK σ (boxRestrict Bx β) v := by
    intro v hv
    exact Or.inr ⟨Finset.notMem_empty _, hv⟩
  have hadj : ∀ u v : Bx, (mixedLatticeGraph β).Adj u.1 v.1 → G.Adj u v := by
    intro u v hA
    have hne : u ≠ v := fun h => hA.ne (congrArg Subtype.val h)
    obtain ⟨hu, hv, e, he, hev⟩ := hA
    rcases hev with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hb : e ∈ boxBonds Bx := (mem_boxBonds Bx).2
        ⟨by rw [← h1]; exact u.2, by rw [← h2]; exact v.2⟩
      refine ⟨hne, hsite u hu, hsite v hv, ⟨e, hb⟩, Or.inr ⟨Finset.notMem_empty _, he⟩, ?_⟩
      left
      exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)
    · have hb : e ∈ boxBonds Bx := (mem_boxBonds Bx).2
        ⟨by rw [← h1]; exact v.2, by rw [← h2]; exact u.2⟩
      refine ⟨hne, hsite u hu, hsite v hv, ⟨e, hb⟩, Or.inr ⟨Finset.notMem_empty _, he⟩, ?_⟩
      right
      exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)
  obtain ⟨y, hy, hyB⟩ := hinf.exists_notMem_finset Bx
  obtain ⟨w⟩ := (show (mixedLatticeGraph β).Reachable 0 y from hy)
  let S : Set (Vertex d) := {z | ∃ hz : z ∈ Bx, G.Reachable ⟨0, h0⟩ ⟨z, hz⟩}
  have h0S : (0 : Vertex d) ∈ S := ⟨h0, SimpleGraph.Reachable.refl _⟩
  have hyS : y ∉ S := by
    rintro ⟨hz, -⟩
    exact hyB hz
  obtain ⟨dt, -, hfst, hsnd⟩ := w.exists_boundary_dart S h0S hyS
  obtain ⟨hu, hreach⟩ := hfst
  have hA := dt.adj
  by_cases hv : dt.snd ∈ Bx
  · exact (hsnd ⟨hv, hreach.trans (hadj ⟨dt.fst, hu⟩ ⟨dt.snd, hv⟩ hA).reachable⟩).elim
  · refine ⟨hsite _ h0open, ⟨dt.fst, hu⟩, ?_, hreach⟩
    simp only [boxInnerBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨-, -, e, -, hev⟩ := hA
    exact ⟨dt.snd, hv, e, rfl, hev⟩

/-- The per-box `mixed_ge` field from the infinite-volume input. -/
theorem mixedValue_box_ge (Bx : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Bx)
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞}
    (hθ : MixedSiteBondPercolationInput d κ θ) :
    θ ≤ mixedValue (boxEnds Bx) (⟨0, h0⟩ : Bx) (boxInnerBoundary Bx) κ
      (⟨∅, ∅, ∅, ∅, ∅⟩ : ExploreState Bx (boxBonds Bx)) := by
  refine hθ.trans ?_
  unfold mixedValue
  rw [← map_boxRestrict Bx κ,
    Measure.map_apply (measurable_boxRestrict Bx) (Set.toFinite _).measurableSet]
  exact measure_mono fun β hβ => boxRestrict_mem_mixedEvent Bx h0 hβ

end NearCritical
