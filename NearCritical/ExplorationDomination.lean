module

public import NearCritical.AdaptiveDomination
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Exploration versus mixed site–bond percolation on a finite graph: the
stochastic domination step of source prop.slab.upper (source 6094–6097).

Vertices `Vx` (renormalised sites, i.e. cubes), edges `Ed` with endpoints `ends`
(tubes), root `o`, target set `D`. Slots `Vx ⊕ Ed`: a site slot carries the cube
data (regularity), an edge slot the tube data. The exploration of the source:
* reveal the root's regularity; a regular root is explored;
* while some untried edge joins an explored site to an unexplored site not known
  irregular: if the far site's regularity is unknown, reveal it; otherwise try the
  tube, and on success explore the far site.
Each site is revealed once and each tube tried once. The real success bit `succ`
is arbitrary, subject to the source requirement: conditional success probability
at least `q = κ{true}` given everything revealed (`hprob`), depending only on
revealed slots and the queried one (`hlocal`).

Conclusion (`exploration_dominates_mixed`): the probability that the explored set
meets `D` is at least the probability, in independent mixed site–bond
percolation with open probability `q` for every site and bond, that the root is
open and joined to `D` by an open path. The value function is the mixed
percolation probability from each partial state, and the comparison is
`adaptive_domination`. Pure Mathlib + `AdaptiveDomination`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Function Finset
open scoped ENNReal Classical

section PiUpdate
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)]

/-- Resampling one coordinate of a product of probability measures. -/
theorem lintegral_pi_update (κ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (κ i)]
    [∀ i, Nonempty (Ω i)] {f : (∀ i, Ω i) → ℝ≥0∞} (hf : Measurable f) (i : ι) :
    ∫⁻ β, f β ∂Measure.pi κ = ∫⁻ y, ∫⁻ β, f (update β i y) ∂Measure.pi κ ∂κ i := by
  have x : ∀ i, Ω i := fun i ↦ Classical.arbitrary (Ω i)
  have hi : i ∈ (univ : Finset ι) := mem_univ i
  rw [lintegral_eq_lmarginal_univ x, lmarginal_erase f hf hi x]
  refine lintegral_congr fun y ↦ ?_
  have hfy : Measurable (fun β : ∀ i, Ω i ↦ f (update β i y)) :=
    hf.comp measurable_update_left
  rw [lintegral_eq_lmarginal_univ x, lmarginal_erase _ hfy hi x]
  have hcomp : ∀ y' : Ω i, (fun β : ∀ i, Ω i ↦ f (update β i y)) ∘ (update · i y') =
      f ∘ (update · i y) := by
    intro y'
    funext β
    simp [update_idem]
  have hconst : ∀ y' : Ω i,
      lmarginal κ (univ.erase i) (fun β ↦ f (update β i y)) (update x i y') =
        lmarginal κ (univ.erase i) f (update x i y) := by
    intro y'
    rw [lmarginal_update_of_notMem hfy (notMem_erase i univ) x y',
      lmarginal_update_of_notMem hf (notMem_erase i univ) x y, hcomp y']
  simp_rw [hconst]
  rw [lintegral_const, measure_univ, mul_one]

end PiUpdate

/-- Integral against an arbitrary probability measure on `Bool`. -/
lemma lintegral_bool_prob (κ : Measure Bool) [IsProbabilityMeasure κ] (g : Bool → ℝ≥0∞) :
    ∫⁻ b, g b ∂κ = κ {true} * g true + (1 - κ {true}) * g false := by
  have hsum : κ {false} + κ {true} = 1 := by
    rw [← measure_union (by simp) (measurableSet_singleton true)]
    have hu : ({false} ∪ {true} : Set Bool) = Set.univ := by
      ext b
      cases b <;> simp
    rw [hu, measure_univ]
  have hf : κ {false} = 1 - κ {true} := ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hsum
  rw [lintegral_fintype, Fintype.sum_bool, hf]
  ring

/-- One fresh coin in a Boolean product, against deterministic inclusions of the
two resampled events. -/
lemma pi_bool_step (κ : Measure Bool) [IsProbabilityMeasure κ] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) {M MT MF : Set (ι → Bool)}
    (hT : ∀ β, update β i true ∈ M → β ∈ MT) (hF : ∀ β, update β i false ∈ M → β ∈ MF) :
    Measure.pi (fun _ : ι ↦ κ) M ≤
      κ {true} * Measure.pi (fun _ : ι ↦ κ) MT +
        (1 - κ {true}) * Measure.pi (fun _ : ι ↦ κ) MF := by
  have hmeas : ∀ s : Set (ι → Bool), MeasurableSet s := fun s ↦ (Set.toFinite s).measurableSet
  rw [← lintegral_indicator_one (hmeas M),
    lintegral_pi_update (fun _ : ι ↦ κ) (measurable_of_countable _) i, lintegral_bool_prob]
  try beta_reduce
  gcongr
  · rw [← lintegral_indicator_one (hmeas MT)]
    refine lintegral_mono fun β ↦ ?_
    by_cases h : update β i true ∈ M
    · simp [Set.indicator, h, hT β h]
    · simp [Set.indicator, h]
  · rw [← lintegral_indicator_one (hmeas MF)]
    refine lintegral_mono fun β ↦ ?_
    by_cases h : update β i false ∈ M
    · simp [Set.indicator, h, hF β h]
    · simp [Set.indicator, h]

/-- Partial exploration state: explored sites `A`, revealed regular `Reg`,
revealed irregular `Irr`, failed tubes `Tr`, successful tubes `Op`. -/
structure ExploreState (Vx Ed : Type*) where
  A : Finset Vx
  Reg : Finset Vx
  Irr : Finset Vx
  Tr : Finset Ed
  Op : Finset Ed

/-- The next move: reveal the root, reveal a far site, or try a tube. -/
inductive ExploreMove (Vx Ed : Type*) where
  | root : ExploreMove Vx Ed
  | site : Vx → ExploreMove Vx Ed
  | edge : Ed → Vx → ExploreMove Vx Ed

/-- The slot queried by a move. -/
def ExploreMove.slot {Vx Ed : Type*} (r : Vx) : ExploreMove Vx Ed → Vx ⊕ Ed
  | .root => .inl r
  | .site z => .inl z
  | .edge e _ => .inr e

section Explore
variable {Vx Ed : Type*} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
variable (ends : Ed → Vx × Vx) (o : Vx) (D : Finset Vx)

/-- The endpoint of `e` that is not explored (when exactly one is). -/
def exploreFar (σ : ExploreState Vx Ed) (e : Ed) : Vx :=
  if (ends e).1 ∈ σ.A then (ends e).2 else (ends e).1

/-- An untried tube from an explored site to an unexplored, not-irregular site. -/
def exploreCand (σ : ExploreState Vx Ed) (e : Ed) : Prop :=
  e ∉ σ.Tr ∧ e ∉ σ.Op ∧ ((ends e).1 ∈ σ.A ∨ (ends e).2 ∈ σ.A) ∧
    exploreFar ends σ e ∉ σ.A ∧ exploreFar ends σ e ∉ σ.Irr

def exploreMove (σ : ExploreState Vx Ed) : Option (ExploreMove Vx Ed) :=
  if σ.A = ∅ then (if o ∉ σ.Reg ∧ o ∉ σ.Irr then some .root else none)
  else if h : ∃ e, exploreCand ends σ e then
    (if exploreFar ends σ (Classical.choose h) ∈ σ.Reg then
      some (.edge (Classical.choose h) (exploreFar ends σ (Classical.choose h)))
    else some (.site (exploreFar ends σ (Classical.choose h))))
  else none

def exploreQuery (σ : ExploreState Vx Ed) : Option (Vx ⊕ Ed) :=
  (exploreMove ends o σ).map (ExploreMove.slot o)

def exploreNext (σ : ExploreState Vx Ed) (b : Bool) : ExploreState Vx Ed :=
  match exploreMove ends o σ, b with
  | none, _ => σ
  | some .root, true => { σ with A := insert o σ.A, Reg := insert o σ.Reg }
  | some .root, false => { σ with Irr := insert o σ.Irr }
  | some (.site z), true => { σ with Reg := insert z σ.Reg }
  | some (.site z), false => { σ with Irr := insert z σ.Irr }
  | some (.edge e z), true => { σ with A := insert z σ.A, Op := insert e σ.Op }
  | some (.edge e _), false => { σ with Tr := insert e σ.Tr }

def exploreRevealed (σ : ExploreState Vx Ed) : Finset (Vx ⊕ Ed) :=
  (σ.Reg ∪ σ.Irr).disjSum (σ.Tr ∪ σ.Op)

def ExploreInv (σ : ExploreState Vx Ed) : Prop :=
  σ.A ⊆ σ.Reg ∧ Disjoint σ.Reg σ.Irr ∧ (∀ e ∈ σ.Op, (ends e).1 ∈ σ.A ∧ (ends e).2 ∈ σ.A) ∧
    (σ.A = ∅ → σ.Reg = ∅) ∧ (σ.A ≠ ∅ → o ∈ σ.A)

def explorePayoff (σ : ExploreState Vx Ed) : ℝ≥0∞ :=
  if (σ.A ∩ D).Nonempty then 1 else 0

lemma exploreMove_cases (σ : ExploreState Vx Ed) :
    (σ.A = ∅ ∧ o ∉ σ.Reg ∧ o ∉ σ.Irr ∧ exploreMove ends o σ = some .root) ∨
    (σ.A = ∅ ∧ ¬(o ∉ σ.Reg ∧ o ∉ σ.Irr) ∧ exploreMove ends o σ = none) ∨
    (σ.A ≠ ∅ ∧ ∃ e, exploreCand ends σ e ∧ exploreFar ends σ e ∈ σ.Reg ∧
      exploreMove ends o σ = some (.edge e (exploreFar ends σ e))) ∨
    (σ.A ≠ ∅ ∧ ∃ e, exploreCand ends σ e ∧ exploreFar ends σ e ∉ σ.Reg ∧
      exploreMove ends o σ = some (.site (exploreFar ends σ e))) ∨
    (σ.A ≠ ∅ ∧ (¬∃ e, exploreCand ends σ e) ∧ exploreMove ends o σ = none) := by
  by_cases hA : σ.A = ∅
  · by_cases hr : o ∉ σ.Reg ∧ o ∉ σ.Irr
    · exact Or.inl ⟨hA, hr.1, hr.2, by rw [exploreMove, if_pos hA, if_pos hr]⟩
    · exact Or.inr (Or.inl ⟨hA, hr, by rw [exploreMove, if_pos hA, if_neg hr]⟩)
  · by_cases hex : ∃ e, exploreCand ends σ e
    · by_cases hreg : exploreFar ends σ (Classical.choose hex) ∈ σ.Reg
      · exact Or.inr (Or.inr (Or.inl ⟨hA, _, Classical.choose_spec hex, hreg,
          by rw [exploreMove, if_neg hA, dif_pos hex, if_pos hreg]⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hA, _, Classical.choose_spec hex, hreg,
          by rw [exploreMove, if_neg hA, dif_pos hex, if_neg hreg]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hA, hex,
        by rw [exploreMove, if_neg hA, dif_neg hex]⟩)))

lemma exploreMove_root {σ : ExploreState Vx Ed} (hm : exploreMove ends o σ = some .root) :
    σ.A = ∅ ∧ o ∉ σ.Reg ∧ o ∉ σ.Irr := by
  rcases exploreMove_cases ends o σ with ⟨hA, h1, h2, -⟩ | ⟨-, -, h⟩ | ⟨-, e, -, -, h⟩ |
      ⟨-, e, -, -, h⟩ | ⟨-, -, h⟩
  · exact ⟨hA, h1, h2⟩
  all_goals (rw [h] at hm; cases hm)

lemma exploreMove_site {σ : ExploreState Vx Ed} {z : Vx}
    (hm : exploreMove ends o σ = some (.site z)) :
    σ.A ≠ ∅ ∧ z ∉ σ.Reg ∧ ∃ e, exploreCand ends σ e ∧ exploreFar ends σ e = z := by
  rcases exploreMove_cases ends o σ with ⟨-, -, -, h⟩ | ⟨-, -, h⟩ | ⟨-, e, -, -, h⟩ |
      ⟨hA, e, hc, hr, h⟩ | ⟨-, -, h⟩
  · rw [h] at hm; cases hm
  · rw [h] at hm; cases hm
  · rw [h] at hm; cases hm
  · rw [h] at hm
    cases hm
    exact ⟨hA, hr, e, hc, rfl⟩
  · rw [h] at hm; cases hm

lemma exploreMove_edge {σ : ExploreState Vx Ed} {e : Ed} {z : Vx}
    (hm : exploreMove ends o σ = some (.edge e z)) :
    σ.A ≠ ∅ ∧ z ∈ σ.Reg ∧ exploreCand ends σ e ∧ exploreFar ends σ e = z := by
  rcases exploreMove_cases ends o σ with ⟨-, -, -, h⟩ | ⟨-, -, h⟩ | ⟨hA, e', hc, hr, h⟩ |
      ⟨-, e', -, -, h⟩ | ⟨-, -, h⟩
  · rw [h] at hm; cases hm
  · rw [h] at hm; cases hm
  · rw [h] at hm
    cases hm
    exact ⟨hA, hr, hc, rfl⟩
  · rw [h] at hm; cases hm
  · rw [h] at hm; cases hm

lemma exploreQuery_eq_some {σ : ExploreState Vx Ed} {i : Vx ⊕ Ed}
    (h : exploreQuery ends o σ = some i) :
    ∃ m, exploreMove ends o σ = some m ∧ ExploreMove.slot o m = i := by
  unfold exploreQuery at h
  cases hm : exploreMove ends o σ with
  | none => simp [hm] at h
  | some m => exact ⟨m, rfl, by simpa [hm] using h⟩

lemma exploreCand_ends {σ : ExploreState Vx Ed} {e : Ed} (hc : exploreCand ends σ e) :
    ((ends e).1 ∈ σ.A ∧ exploreFar ends σ e = (ends e).2) ∨
      ((ends e).2 ∈ σ.A ∧ exploreFar ends σ e = (ends e).1) := by
  by_cases h1 : (ends e).1 ∈ σ.A
  · exact Or.inl ⟨h1, if_pos h1⟩
  · exact Or.inr ⟨hc.2.2.1.resolve_left h1, if_neg h1⟩

/-! Structural hypotheses of `adaptive_domination` for the exploration. -/

lemma exploreQuery_notMem {σ : ExploreState Vx Ed} {i : Vx ⊕ Ed}
    (h : exploreQuery ends o σ = some i) : i ∉ exploreRevealed σ := by
  obtain ⟨m, hm, rfl⟩ := exploreQuery_eq_some ends o h
  cases m with
  | root =>
    obtain ⟨-, h1, h2⟩ := exploreMove_root ends o hm
    simp [ExploreMove.slot, exploreRevealed, h1, h2]
  | site z =>
    obtain ⟨-, hr, e, hc, rfl⟩ := exploreMove_site ends o hm
    simp [ExploreMove.slot, exploreRevealed, hr, hc.2.2.2.2]
  | edge e z =>
    obtain ⟨-, -, hc, -⟩ := exploreMove_edge ends o hm
    simp [ExploreMove.slot, exploreRevealed, hc.1, hc.2.1]

lemma exploreRevealed_next {σ : ExploreState Vx Ed} {i : Vx ⊕ Ed}
    (h : exploreQuery ends o σ = some i) (b : Bool) :
    exploreRevealed (exploreNext ends o σ b) = insert i (exploreRevealed σ) := by
  obtain ⟨m, hm, rfl⟩ := exploreQuery_eq_some ends o h
  ext x
  cases m <;> cases b <;> rcases x with v | f <;>
    simp [exploreNext, hm, exploreRevealed, ExploreMove.slot] <;> tauto

lemma exploreInv_next {σ : ExploreState Vx Ed} {i : Vx ⊕ Ed} (hσ : ExploreInv ends o σ)
    (h : exploreQuery ends o σ = some i) (b : Bool) :
    ExploreInv ends o (exploreNext ends o σ b) := by
  obtain ⟨hAR, hdis, hop, hempty, hroot⟩ := hσ
  obtain ⟨m, hm, -⟩ := exploreQuery_eq_some ends o h
  cases m with
  | root =>
    obtain ⟨hA, hoR, hoI⟩ := exploreMove_root ends o hm
    cases b
    · simp only [exploreNext, hm]
      refine ⟨hAR, ?_, hop, hempty, hroot⟩
      exact Finset.disjoint_insert_right.mpr ⟨hoR, hdis⟩
    · simp only [exploreNext, hm]
      refine ⟨Finset.insert_subset_insert o hAR,
        Finset.disjoint_insert_left.mpr ⟨hoI, hdis⟩, ?_, ?_, ?_⟩
      · intro e he
        obtain ⟨h1, h2⟩ := hop e he
        exact ⟨mem_insert_of_mem h1, mem_insert_of_mem h2⟩
      · intro h0
        exact absurd h0 (Finset.insert_ne_empty o σ.A)
      · intro _
        exact mem_insert_self o σ.A
  | site z =>
    obtain ⟨hA, hzR, e, hc, rfl⟩ := exploreMove_site ends o hm
    cases b
    · simp only [exploreNext, hm]
      exact ⟨hAR, Finset.disjoint_insert_right.mpr ⟨hzR, hdis⟩, hop,
        fun h0 ↦ absurd h0 hA, hroot⟩
    · simp only [exploreNext, hm]
      exact ⟨hAR.trans (subset_insert _ _),
        Finset.disjoint_insert_left.mpr ⟨hc.2.2.2.2, hdis⟩, hop,
        fun h0 ↦ absurd h0 hA, hroot⟩
  | edge e z =>
    obtain ⟨hA, hzR, hc, rfl⟩ := exploreMove_edge ends o hm
    cases b
    · simp only [exploreNext, hm]
      exact ⟨hAR, hdis, hop, hempty, hroot⟩
    · simp only [exploreNext, hm]
      refine ⟨Finset.insert_subset hzR hAR, hdis, ?_, ?_, ?_⟩
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · rcases exploreCand_ends ends hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · refine ⟨mem_insert_of_mem h1, ?_⟩
            rw [← h2]
            exact mem_insert_self _ _
          · refine ⟨?_, mem_insert_of_mem h1⟩
            rw [← h2]
            exact mem_insert_self _ _
        · obtain ⟨h1, h2⟩ := hop f hf
          exact ⟨mem_insert_of_mem h1, mem_insert_of_mem h2⟩
      · intro h0
        exact absurd h0 (Finset.insert_ne_empty _ σ.A)
      · intro _
        exact mem_insert_of_mem (hroot hA)

/-! The mixed site–bond comparison model, from a partial state. -/

/-- A site is open in the comparison model from state `σ`. -/
def mixedSiteOK (σ : ExploreState Vx Ed) (β : Vx ⊕ Ed → Bool) (v : Vx) : Prop :=
  v ∈ σ.Reg ∨ (v ∉ σ.Irr ∧ β (.inl v) = true)

/-- A bond is open in the comparison model from state `σ`. -/
def mixedEdgeOK (σ : ExploreState Vx Ed) (β : Vx ⊕ Ed → Bool) (e : Ed) : Prop :=
  e ∈ σ.Op ∨ (e ∉ σ.Tr ∧ β (.inr e) = true)

/-- Open sites joined by open bonds. -/
def mixedGraph (σ : ExploreState Vx Ed) (β : Vx ⊕ Ed → Bool) : SimpleGraph Vx where
  Adj u v := u ≠ v ∧ mixedSiteOK σ β u ∧ mixedSiteOK σ β v ∧
    ∃ e, mixedEdgeOK σ β e ∧ (ends e = (u, v) ∨ ends e = (v, u))
  symm := ⟨by
    rintro u v ⟨huv, hu, hv, e, he, h | h⟩
    · exact ⟨huv.symm, hv, hu, e, he, Or.inr h⟩
    · exact ⟨huv.symm, hv, hu, e, he, Or.inl h⟩⟩
  loopless := ⟨by rintro u ⟨h, _⟩; exact h rfl⟩

/-- The root is open and joined to `D` in the comparison model from `σ`. -/
def mixedEvent (σ : ExploreState Vx Ed) : Set (Vx ⊕ Ed → Bool) :=
  {β | mixedSiteOK σ β o ∧ ∃ d ∈ D, (mixedGraph ends σ β).Reachable o d}

/-- Comparison value: mixed site–bond probability from `σ`, every unrevealed site
and bond open independently with law `κ`. -/
def mixedValue (κ : Measure Bool) (σ : ExploreState Vx Ed) : ℝ≥0∞ :=
  Measure.pi (fun _ : Vx ⊕ Ed ↦ κ) (mixedEvent ends o D σ)

lemma mixedEvent_transfer {σ σ' : ExploreState Vx Ed} {β β' : Vx ⊕ Ed → Bool}
    (hs : ∀ v, mixedSiteOK σ β' v → mixedSiteOK σ' β v)
    (he : ∀ e, mixedEdgeOK σ β' e → mixedEdgeOK σ' β e)
    (h : β' ∈ mixedEvent ends o D σ) : β ∈ mixedEvent ends o D σ' := by
  obtain ⟨ho, d, hd, hr⟩ := h
  refine ⟨hs o ho, d, hd, hr.mono ?_⟩
  rintro u v ⟨huv, hu, hv, e, hee, hends⟩
  exact ⟨huv, hs u hu, hs v hv, e, he e hee, hends⟩

/-- Revealing the queried slot with value `b` and moving to `next σ b` can only
enlarge the comparison event. -/
lemma mixedEvent_step {σ : ExploreState Vx Ed} {m : ExploreMove Vx Ed}
    (hm : exploreMove ends o σ = some m) (b : Bool) (β : Vx ⊕ Ed → Bool)
    (h : update β (ExploreMove.slot o m) b ∈ mixedEvent ends o D σ) :
    β ∈ mixedEvent ends o D (exploreNext ends o σ b) := by
  refine mixedEvent_transfer ends o D (fun v hv ↦ ?_) (fun f hf ↦ ?_) h
  · cases m with
    | root =>
      obtain ⟨-, hoR, -⟩ := exploreMove_root ends o hm
      by_cases hvo : v = o
      · rw [hvo] at hv ⊢
        cases b <;> simp [mixedSiteOK, exploreNext, hm, ExploreMove.slot, hoR] at hv ⊢ <;>
          tauto
      · cases b <;>
          simp [mixedSiteOK, exploreNext, hm, ExploreMove.slot, update_apply, hvo] at hv ⊢ <;>
          tauto
    | site z =>
      obtain ⟨-, hzR, -⟩ := exploreMove_site ends o hm
      by_cases hvz : v = z
      · rw [hvz] at hv ⊢
        cases b <;> simp [mixedSiteOK, exploreNext, hm, ExploreMove.slot, hzR] at hv ⊢ <;>
          tauto
      · cases b <;>
          simp [mixedSiteOK, exploreNext, hm, ExploreMove.slot, update_apply, hvz] at hv ⊢ <;>
          tauto
    | edge e z =>
      cases b <;> simp [mixedSiteOK, exploreNext, hm, ExploreMove.slot, update_apply] at hv ⊢ <;>
        tauto
  · cases m with
    | root =>
      cases b <;> simp [mixedEdgeOK, exploreNext, hm, ExploreMove.slot, update_apply] at hf ⊢ <;>
        tauto
    | site z =>
      cases b <;> simp [mixedEdgeOK, exploreNext, hm, ExploreMove.slot, update_apply] at hf ⊢ <;>
        tauto
    | edge e z =>
      obtain ⟨-, -, ⟨-, heOp, -⟩, -⟩ := exploreMove_edge ends o hm
      by_cases hfe : f = e
      · rw [hfe] at hf ⊢
        cases b <;> simp [mixedEdgeOK, exploreNext, hm, ExploreMove.slot, heOp] at hf ⊢ <;>
          tauto
      · cases b <;>
          simp [mixedEdgeOK, exploreNext, hm, ExploreMove.slot, update_apply, hfe] at hf ⊢ <;>
          tauto

/-- The failure branch is a sub-event of the success branch. -/
lemma mixedEvent_next_mono {σ : ExploreState Vx Ed} {m : ExploreMove Vx Ed}
    (hm : exploreMove ends o σ = some m) :
    mixedEvent ends o D (exploreNext ends o σ false) ⊆
      mixedEvent ends o D (exploreNext ends o σ true) := by
  intro β h
  refine mixedEvent_transfer ends o D (fun v hv ↦ ?_) (fun f hf ↦ ?_) h
  · cases m <;> simp [mixedSiteOK, exploreNext, hm] at hv ⊢ <;> tauto
  · cases m <;> simp [mixedEdgeOK, exploreNext, hm] at hf ⊢ <;> tauto

/-- At a stopping state the comparison event is contained in the explored event. -/
lemma mixedValue_le_payoff (κ : Measure Bool) [IsProbabilityMeasure κ]
    {σ : ExploreState Vx Ed} (hσ : ExploreInv ends o σ)
    (hq : exploreQuery ends o σ = none) :
    mixedValue ends o D κ σ ≤ explorePayoff D σ := by
  obtain ⟨hAR, hdis, hop, hempty, hroot⟩ := hσ
  unfold explorePayoff
  split_ifs with hAD
  · unfold mixedValue
    exact prob_le_one
  · have hnone : exploreMove ends o σ = none := by
      unfold exploreQuery at hq
      cases hm : exploreMove ends o σ with
      | none => rfl
      | some m => simp [hm] at hq
    have hzero : mixedEvent ends o D σ = ∅ := by
      ext β
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨ho, d, hd, hr⟩
      rcases exploreMove_cases ends o σ with ⟨-, -, -, h⟩ | ⟨hA, hor, -⟩ |
          ⟨-, e₁, -, -, h⟩ | ⟨-, e₁, -, -, h⟩ | ⟨hA, hex, -⟩
      · rw [h] at hnone; cases hnone
      · have hR := hempty hA
        rcases ho with ho | ⟨hoI, -⟩
        · simp [hR] at ho
        · exact hor ⟨by simp [hR], hoI⟩
      · rw [h] at hnone; cases hnone
      · rw [h] at hnone; cases hnone
      · have hoA : o ∈ σ.A := hroot hA
        have hdA : d ∉ σ.A := fun hdA ↦ hAD ⟨d, mem_inter.mpr ⟨hdA, hd⟩⟩
        obtain ⟨p⟩ := hr
        obtain ⟨dt, -, hfst, hsnd⟩ := p.exists_boundary_dart (σ.A : Set Vx) hoA hdA
        obtain ⟨-, -, hv, e, hee, hends⟩ := dt.adj
        apply hex
        refine ⟨e, ?_⟩
        have hnotOp : e ∉ σ.Op := by
          intro heOp
          obtain ⟨h1, h2⟩ := hop e heOp
          rcases hends with h | h <;> rw [h] at h1 h2 <;> simp_all
        have hnotTr : e ∉ σ.Tr := by
          rcases hee with h | ⟨h, -⟩
          · exact absurd h hnotOp
          · exact h
        have hfar : exploreFar ends σ e = dt.snd := by
          unfold exploreFar
          rcases hends with h | h <;> rw [h]
          · simp [show dt.fst ∈ σ.A from hfst]
          · simp [show dt.snd ∉ σ.A from hsnd]
        have hnotIrr : dt.snd ∉ σ.Irr := by
          rcases hv with hv | ⟨hv, -⟩
          · exact Finset.disjoint_left.mp hdis hv
          · exact hv
        refine ⟨hnotTr, hnotOp, ?_, ?_, ?_⟩
        · rcases hends with h | h <;> rw [h]
          · exact Or.inl hfst
          · exact Or.inr hfst
        · rw [hfar]; exact hsnd
        · rw [hfar]; exact hnotIrr
    unfold mixedValue
    simp [hzero]

/-- Stochastic domination of mixed site–bond percolation by the exploration. -/
theorem exploration_dominates_mixed {Ω : Vx ⊕ Ed → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)] [∀ i, Nonempty (Ω i)]
    (κ : Measure Bool) [IsProbabilityMeasure κ]
    (succ : ExploreState Vx Ed → (∀ i, Ω i) → Bool)
    (hlocal : ∀ σ i (x x' : ∀ j, Ω j), ExploreInv ends o σ → exploreQuery ends o σ = some i →
      (∀ j ∈ insert i (exploreRevealed σ), x j = x' j) → succ σ x = succ σ x')
    (hmeas : ∀ σ, Measurable (succ σ))
    (hprob : ∀ σ i (x : ∀ j, Ω j), ExploreInv ends o σ → exploreQuery ends o σ = some i →
      κ {true} ≤ ν i {y | succ σ (update x i y) = true}) :
    mixedValue ends o D κ ⟨∅, ∅, ∅, ∅, ∅⟩ ≤
      ∫⁻ x, explorePayoff D (adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ
        (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ x) ∂Measure.pi ν := by
  refine adaptive_domination ν exploreRevealed (exploreQuery ends o) (exploreNext ends o) succ
    (ExploreInv ends o) (mixedValue ends o D κ) (explorePayoff D) (q := κ {true}) prob_le_one
    (fun σ i _ h ↦ exploreQuery_notMem ends o h)
    (fun σ i b _ h ↦ exploreRevealed_next ends o h b)
    (fun σ i b hσ h ↦ exploreInv_next ends o hσ h b)
    hlocal hmeas hprob ?_ ?_
    (fun σ hσ h ↦ mixedValue_le_payoff ends o D κ hσ h)
    ⟨∅, ∅, ∅, ∅, ∅⟩ ?_ (by ext x; cases x <;> simp [exploreRevealed])
  · intro σ i _ h
    obtain ⟨m, hm, rfl⟩ := exploreQuery_eq_some ends o h
    exact pi_bool_step κ (ExploreMove.slot o m)
      (fun β hβ ↦ mixedEvent_step ends o D hm true β hβ)
      (fun β hβ ↦ mixedEvent_step ends o D hm false β hβ)
  · intro σ i _ h
    obtain ⟨m, hm, -⟩ := exploreQuery_eq_some ends o h
    exact measure_mono (mixedEvent_next_mono ends o D hm)
  · refine ⟨by simp, by simp, by simp, fun _ ↦ rfl, fun h ↦ absurd rfl h⟩

end Explore

end NearCritical
