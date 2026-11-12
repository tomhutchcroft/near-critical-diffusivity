module

public import NearCritical.ExplorationDominationAux

/-! A history-based NEST RULE for the exploration with memory.

The memory is the ordered history `Hist` of (move, outcome); it is updated by
`nextHist` from the state and the outcome bit only. A `NestRule` gives
* `rootNest x`: the nest of the root cube (reads the root's block);
* `siteOK z x`: whether the cube of `z` is acceptable (reads the block of `z`);
* `childNest e z ℓ x`: the nest of `z` produced from the parent nest `ℓ` through
  the tube `e` (reads the blocks of `e` and of `z`).
`nestsOf h x` recomputes the current nests by a fold over the history, reading
the sample only on slots recorded in the history. `nestSucc` is the success
rule: root/site steps test `rootNest`/`siteOK`; an edge step succeeds iff the
recomputed parent nest is absent (total rule) or `childNest` exists.

Proved: `nestsOf_congr`, `nestSucc_local` (the rule reads only the fresh slot
and revealed slots), `histOK_next` (the sample-free invariant "slots of the
history are revealed" is preserved), `nestSucc_measurable`.

No probability here. Source: main.tex 6091-6099 (state = current k-nest).
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Function
open scoped ENNReal Classical

section
variable {Vx Ed : Type} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
variable (ends : Ed → Vx × Vx) (o : Vx)
variable {Ω : Vx ⊕ Ed → Type} {L : Type}

/-- The endpoint of `e` other than `z`. -/
def otherEnd (e : Ed) (z : Vx) : Vx := if (ends e).1 = z then (ends e).2 else (ends e).1

/-- Local nest data. -/
structure NestRule (Vx Ed : Type) (o : Vx) (Ω : Vx ⊕ Ed → Type) (L : Type) where
  rootNest : (∀ i, Ω i) → Option L
  siteOK : Vx → (∀ i, Ω i) → Bool
  childNest : Ed → Vx → L → (∀ i, Ω i) → Option L
  root_local : ∀ x x' : ∀ i, Ω i, x (.inl o) = x' (.inl o) → rootNest x = rootNest x'
  site_local : ∀ z (x x' : ∀ i, Ω i), x (.inl z) = x' (.inl z) → siteOK z x = siteOK z x'
  child_local : ∀ e z ℓ (x x' : ∀ i, Ω i), x (.inr e) = x' (.inr e) →
    x (.inl z) = x' (.inl z) → childNest e z ℓ x = childNest e z ℓ x'

/-- Ordered history, newest first. -/
abbrev Hist (Vx Ed : Type) := List (ExploreMove Vx Ed × Bool)

/-- Memory update: record the move and its outcome. -/
def nextHist (σ : ExploreState Vx Ed) (h : Hist Vx Ed) (b : Bool) : Hist Vx Ed :=
  match exploreMove ends o σ with
  | some m => (m, b) :: h
  | none => h

/-- One history entry applied to a nest assignment. -/
def nestStep (Ru : NestRule Vx Ed o Ω L) (x : ∀ i, Ω i) (N : Vx → Option L) :
    ExploreMove Vx Ed × Bool → Vx → Option L
  | (.root, true) => Function.update N o (Ru.rootNest x)
  | (.edge e z, true) =>
      Function.update N z ((N (otherEnd ends e z)).bind fun ℓ => Ru.childNest e z ℓ x)
  | _ => N

/-- Current nests, recomputed from the history. -/
def nestsOf (Ru : NestRule Vx Ed o Ω L) : Hist Vx Ed → (∀ i, Ω i) → Vx → Option L
  | [], _ => fun _ => none
  | mb :: h, x => nestStep ends o Ru x (nestsOf Ru h x) mb

/-- The success rule. -/
def nestSucc (Ru : NestRule Vx Ed o Ω L) (s : ExploreState Vx Ed × Hist Vx Ed)
    (x : ∀ i, Ω i) : Bool :=
  match exploreMove ends o s.1 with
  | some .root => (Ru.rootNest x).isSome
  | some (.site z) => Ru.siteOK z x
  | some (.edge e z) =>
      match nestsOf ends o Ru s.2 x (otherEnd ends e z) with
      | none => true
      | some ℓ => (Ru.childNest e z ℓ x).isSome
  | none => false

/-- The slots a recorded move has read lie in `R`. -/
def moveSlotsOK (R : Finset (Vx ⊕ Ed)) : ExploreMove Vx Ed → Prop
  | .root => Sum.inl o ∈ R
  | .site _ => True
  | .edge e z => Sum.inr e ∈ R ∧ Sum.inl z ∈ R

lemma moveSlotsOK_mono {R R' : Finset (Vx ⊕ Ed)} (hR : R ⊆ R') (m : ExploreMove Vx Ed)
    (h : moveSlotsOK o R m) : moveSlotsOK o R' m := by
  cases m with
  | root => exact hR h
  | site z => trivial
  | edge e z => exact ⟨hR h.1, hR h.2⟩

/-- Sample-free invariant: every slot read by the history is revealed. -/
def histOK (s : ExploreState Vx Ed × Hist Vx Ed) : Prop :=
  ∀ mb ∈ s.2, moveSlotsOK o (exploreRevealed s.1) mb.1

lemma histOK_nil : histOK o ((⟨∅, ∅, ∅, ∅, ∅⟩ : ExploreState Vx Ed), ([] : Hist Vx Ed)) := by
  intro mb hmb
  simp at hmb

theorem nestStep_congr (Ru : NestRule Vx Ed o Ω L) {R : Finset (Vx ⊕ Ed)}
    (x x' : ∀ i, Ω i) (hx : ∀ j ∈ R, x j = x' j) (N : Vx → Option L)
    (mb : ExploreMove Vx Ed × Bool) (hm : moveSlotsOK o R mb.1) :
    nestStep ends o Ru x N mb = nestStep ends o Ru x' N mb := by
  obtain ⟨m, b⟩ := mb
  cases m with
  | root =>
    cases b
    · rfl
    · change Function.update N o (Ru.rootNest x) = Function.update N o (Ru.rootNest x')
      rw [Ru.root_local x x' (hx _ hm)]
  | site z => cases b <;> rfl
  | edge e z =>
    cases b
    · rfl
    · change Function.update N z ((N (otherEnd ends e z)).bind fun ℓ => Ru.childNest e z ℓ x) =
        Function.update N z ((N (otherEnd ends e z)).bind fun ℓ => Ru.childNest e z ℓ x')
      have hc : (fun ℓ => Ru.childNest e z ℓ x) = (fun ℓ => Ru.childNest e z ℓ x') :=
        funext fun ℓ => Ru.child_local e z ℓ x x' (hx _ hm.1) (hx _ hm.2)
      rw [hc]

theorem nestsOf_congr (Ru : NestRule Vx Ed o Ω L) (σ : ExploreState Vx Ed)
    (x x' : ∀ i, Ω i) (hx : ∀ j ∈ exploreRevealed σ, x j = x' j) :
    ∀ h : Hist Vx Ed, histOK o (σ, h) → nestsOf ends o Ru h x = nestsOf ends o Ru h x' := by
  intro h
  induction h with
  | nil => intro _; rfl
  | cons mb h ih =>
    intro hok
    have hok' : histOK o (σ, h) := fun mb' hmb' => hok mb' (List.mem_cons_of_mem _ hmb')
    change nestStep ends o Ru x (nestsOf ends o Ru h x) mb =
      nestStep ends o Ru x' (nestsOf ends o Ru h x') mb
    rw [ih hok']
    exact nestStep_congr ends o Ru x x' hx _ mb (hok mb List.mem_cons_self)

theorem nestSucc_local (Ru : NestRule Vx Ed o Ω L) (σ : ExploreState Vx Ed) (h : Hist Vx Ed)
    (i : Vx ⊕ Ed) (x x' : ∀ j, Ω j) (hI : histOK o (σ, h))
    (hq : exploreQuery ends o σ = some i)
    (hx : ∀ j ∈ insert i (exploreRevealed σ), x j = x' j) :
    nestSucc ends o Ru (σ, h) x = nestSucc ends o Ru (σ, h) x' := by
  obtain ⟨m, hm, rfl⟩ := exploreQuery_eq_some ends o hq
  have hrev : ∀ j ∈ exploreRevealed σ, x j = x' j :=
    fun j hj => hx j (Finset.mem_insert_of_mem hj)
  have hN := nestsOf_congr ends o Ru σ x x' hrev h hI
  unfold nestSucc
  simp only [hm]
  cases m with
  | root =>
    simp only
    rw [Ru.root_local x x' (hx _ (Finset.mem_insert_self _ _))]
  | site z =>
    exact Ru.site_local z x x' (hx _ (Finset.mem_insert_self _ _))
  | edge e z =>
    have hz : Sum.inl z ∈ exploreRevealed σ := by
      unfold exploreRevealed
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_union_left _ (exploreMove_edge ends o hm).2.1)
    simp only
    rw [hN]
    cases nestsOf ends o Ru h x' (otherEnd ends e z) with
    | none => rfl
    | some ℓ =>
      simp only
      rw [Ru.child_local e z ℓ x x' (hx _ (Finset.mem_insert_self _ _)) (hrev _ hz)]

theorem histOK_next (σ : ExploreState Vx Ed) (h : Hist Vx Ed) (i : Vx ⊕ Ed) (b : Bool)
    (hI : histOK o (σ, h)) (hq : exploreQuery ends o σ = some i) :
    histOK o (exploreNext ends o σ b, nextHist ends o σ h b) := by
  have hrev := exploreRevealed_next ends o hq b
  obtain ⟨m, hm, rfl⟩ := exploreQuery_eq_some ends o hq
  intro mb hmb
  change mb ∈ nextHist ends o σ h b at hmb
  unfold nextHist at hmb
  rw [hm] at hmb
  change moveSlotsOK o (exploreRevealed (exploreNext ends o σ b)) mb.1
  rw [hrev]
  rcases List.mem_cons.mp hmb with rfl | hold
  · cases m with
    | root => exact Finset.mem_insert_self _ _
    | site z => trivial
    | edge e z =>
      refine ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
      unfold exploreRevealed
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_union_left _ (exploreMove_edge ends o hm).2.1)
  · exact moveSlotsOK_mono o (Finset.subset_insert _ _) _ (hI mb hold)

theorem nestSucc_measurable [∀ i, MeasurableSpace (Ω i)] [∀ i, Countable (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (Ru : NestRule Vx Ed o Ω L)
    (s : ExploreState Vx Ed × Hist Vx Ed) : Measurable (nestSucc ends o Ru s) :=
  Measurable.of_discrete

end

end NearCritical
