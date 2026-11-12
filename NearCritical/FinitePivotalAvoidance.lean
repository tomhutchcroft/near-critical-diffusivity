module

public import NearCritical.HalfSpaceArmGeometry
public import NearCritical.HalfSpaceTranslation
public import NearCritical.DifferentialInequality
public import NearCritical.BKAllParameters

/-! Finite pivotal avoidance for the paper's slab Russo argument. Witnesses
avoid the tested coordinate, hence their occurrence is invariant under opening
that coordinate and the closed-edge factor cancels by actual finite Mecke. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset BernoulliCalculus MeasureTheory ProbabilityTheory
open scoped Classical

/-- Standard finite forcing with disjoint witnesses not using coordinate e. -/
def AvoidingDisjointOccurrence {E : Type*} (e : E) (A B : Set (E → Bool)) (ω : E → Bool) : Prop :=
  ∃ F H : Set E, F.Finite ∧ H.Finite ∧ Disjoint F H ∧ e ∉ F ∪ H ∧
    ForcesOn A ω F ∧ ForcesOn B ω H

lemma AvoidingDisjointOccurrence.to_disjointOccurrence {E : Type*} {e : E}
    {A B : Set (E → Bool)} {ω : E → Bool} (h : AvoidingDisjointOccurrence e A B ω) :
    DisjointOccurrence A B ω := by
  obtain ⟨F, H, hF, hH, hdis, _, hFA, hHB⟩ := h
  exact ⟨F, H, hF, hH, hdis, hFA, hHB⟩

lemma forcesOn_forceOpen_iff {E : Type*} (e : E) (ω : E → Bool) (F : Set E)
    (he : e ∉ F) (A : Set (E → Bool)) :
    ForcesOn A (forceOpen e ω) F ↔ ForcesOn A ω F := by
  have hv : ∀ f ∈ F, forceOpen e ω f = ω f := by
    intro f hf
    have hfe : f ≠ e := fun h ↦ he (h ▸ hf)
    simp [forceOpen, hfe]
  constructor
  · intro h θ hagree
    exact h θ (fun f hf ↦ (hagree f hf).trans (hv f hf).symm)
  · intro h θ hagree
    exact h θ (fun f hf ↦ (hagree f hf).trans (hv f hf))

/-- No increasingness is required: all witness values are literally unchanged. -/
theorem avoidingDisjointOccurrence_forceOpen_iff {E : Type*} (e : E)
    (A B : Set (E → Bool)) (ω : E → Bool) :
    AvoidingDisjointOccurrence e A B (forceOpen e ω) ↔ AvoidingDisjointOccurrence e A B ω := by
  constructor
  · rintro ⟨F, H, hF, hH, hdis, hav, hFA, hHB⟩
    exact ⟨F, H, hF, hH, hdis, hav,
      (forcesOn_forceOpen_iff e ω F (fun he ↦ hav (Or.inl he)) A).mp hFA,
      (forcesOn_forceOpen_iff e ω H (fun he ↦ hav (Or.inr he)) B).mp hHB⟩
  · rintro ⟨F, H, hF, hH, hdis, hav, hFA, hHB⟩
    exact ⟨F, H, hF, hH, hdis, hav,
      (forcesOn_forceOpen_iff e ω F (fun he ↦ hav (Or.inl he)) A).mpr hFA,
      (forcesOn_forceOpen_iff e ω H (fun he ↦ hav (Or.inr he)) B).mpr hHB⟩

/-- Avoiding occurrence is identical in local and full coordinates for cylinders,
provided the tested coordinate belongs to the chosen finite support. -/
theorem avoidingDisjointOccurrence_restrict_iff {E : Type*} (s : Finset E) (e : s)
    (A B : Set ((j : s) → Bool)) (ω : E → Bool) :
    AvoidingDisjointOccurrence e A B (s.restrict ω) ↔
      AvoidingDisjointOccurrence e.val ((s.restrict) ⁻¹' A) ((s.restrict) ⁻¹' B) ω := by
  constructor
  · rintro ⟨F, H, hFinF, hFinH, hdis, hav, hF, hH⟩
    refine ⟨Subtype.val '' F, Subtype.val '' H, hFinF.image _, hFinH.image _, ?_, ?_, ?_, ?_⟩
    · apply Set.disjoint_left.mpr
      rintro j ⟨f, hf, rfl⟩ ⟨h, hh, heq⟩
      have heq' : h = f := Subtype.ext heq
      subst h
      exact Set.disjoint_left.mp hdis hf hh
    · rintro (heF | heH)
      · obtain ⟨f, hf, hfe⟩ := heF
        have heq : f = e := Subtype.ext hfe
        exact hav (Or.inl (heq ▸ hf))
      · obtain ⟨h, hh, hhe⟩ := heH
        have heq : h = e := Subtype.ext hhe
        exact hav (Or.inr (heq ▸ hh))
    · intro θ hθ
      exact hF (s.restrict θ) (fun j hj ↦ hθ j.val ⟨j, hj, rfl⟩)
    · intro θ hθ
      exact hH (s.restrict θ) (fun j hj ↦ hθ j.val ⟨j, hj, rfl⟩)
  · rintro ⟨F, H, _, _, hdis, hav, hF, hH⟩
    let f : Set s := {j | j.val ∈ F}
    let h : Set s := {j | j.val ∈ H}
    refine ⟨f, h, Set.toFinite _, Set.toFinite _, ?_, ?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr (fun j hf hh ↦ Set.disjoint_left.mp hdis hf hh)
    · exact fun he ↦ hav he
    · intro θ hθ
      have hagree : ∀ j ∈ F, extendConfiguration s ω θ j = ω j := by
        intro j hj
        by_cases hs : j ∈ s
        · simp only [extendConfiguration, dite_eq_left hs]
          exact hθ ⟨j, hs⟩ hj
        · simp [extendConfiguration, hs]
      have hA := hF (extendConfiguration s ω θ) hagree
      change s.restrict (extendConfiguration s ω θ) ∈ A at hA
      rw [restrict_extendConfiguration] at hA
      exact hA
    · intro θ hθ
      have hagree : ∀ j ∈ H, extendConfiguration s ω θ j = ω j := by
        intro j hj
        by_cases hs : j ∈ s
        · simp only [extendConfiguration, dite_eq_left hs]
          exact hθ ⟨j, hs⟩ hj
        · simp [extendConfiguration, hs]
      have hB := hH (extendConfiguration s ω θ) hagree
      change s.restrict (extendConfiguration s ω θ) ∈ B at hB
      rw [restrict_extendConfiguration] at hB
      exact hB

/-- Mecke removes the closed-coordinate factor for any forceOpen-invariant
finite observable. This is an algebraic identity for every real p. -/
theorem finiteExpectation_forceOpen_invariant_closed {E : Type*} [Fintype E]
    (p : ℝ) (e : E) (g : (E → Bool) → ℝ)
    (hinv : ∀ ω, g (forceOpen e ω) = g ω) :
    finiteExpectation p (fun ω ↦ (if ω e then 0 else 1) * g ω) =
      (1-p) * finiteExpectation p g := by
  have hs : finiteExpectation p (fun ω ↦ (if ω e then 0 else 1) * g ω) =
      finiteExpectation p g - finiteExpectation p (fun ω ↦ g ω * (if ω e then 1 else 0)) := by
    unfold finiteExpectation
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    cases h : ω e <;> simp [h]
  rw [hs, finiteExpectation_mecke]
  have hfun : (fun ω ↦ g (forceOpen e ω)) = g := funext hinv
  rw [hfun]
  ring

theorem finiteExpectation_avoiding_closed_factor {E : Type*} [Fintype E]
    (p : ℝ) (e : E) (A B : Set (E → Bool)) :
    finiteExpectation p (fun ω ↦ (if ω e then 0 else 1) *
      (if AvoidingDisjointOccurrence e A B ω then 1 else 0)) =
        (1-p) * BK.eventProbability p {ω | AvoidingDisjointOccurrence e A B ω} := by
  apply finiteExpectation_forceOpen_invariant_closed
  intro ω
  rw [avoidingDisjointOccurrence_forceOpen_iff]

/-- The reciprocal Russo factor cancels exactly; no conditional product-law
hypothesis or desired probability estimate is assumed. -/
theorem finiteExpectation_avoiding_russo_cancel {E : Type*} [Fintype E]
    (p : ℝ) (hp : p ≠ 1) (e : E) (A B : Set (E → Bool)) :
    (1-p)⁻¹ * finiteExpectation p (fun ω ↦ (if ω e then 0 else 1) *
      (if AvoidingDisjointOccurrence e A B ω then 1 else 0)) =
        BK.eventProbability p {ω | AvoidingDisjointOccurrence e A B ω} := by
  rw [finiteExpectation_avoiding_closed_factor, ← mul_assoc,
    inv_mul_cancel₀ (sub_ne_zero.mpr hp.symm), one_mul]

/-- Avoiding witnesses are ordinary disjoint witnesses, so existing all-p BK
applies after the exact closed-edge cancellation. -/
theorem finite_avoiding_russo_bk {E : Type*} [Fintype E]
    (p : unitInterval) (hp : (p : ℝ) ≠ 1) (e : E)
    (A B : Set (E → Bool)) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    (1-(p:ℝ))⁻¹ * finiteExpectation (p:ℝ) (fun ω ↦ (if ω e then 0 else 1) *
      (if AvoidingDisjointOccurrence e A B ω then 1 else 0)) ≤
        BK.eventProbability (p:ℝ) A * BK.eventProbability (p:ℝ) B := by
  rw [finiteExpectation_avoiding_russo_cancel (p:ℝ) hp]
  exact (BK.eventProbability_mono p.property.1 p.property.2
    (show {ω | AvoidingDisjointOccurrence e A B ω} ⊆ BK.occurrenceEvent A B from
      fun _ h ↦ h.to_disjointOccurrence)).trans (BK.bk_eventProbability p A B hA hB)

private lemma walk_single_edge_extension {V : Type*} {G H : SimpleGraph V}
    (a b : V)
    (hstep : ∀ u v, H.Adj u v → G.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    {x y : V} (w : H.Walk x y) :
    G.Reachable x y ∨ (G.Reachable x a ∧ G.Reachable b y) ∨
      (G.Reachable x b ∧ G.Reachable a y) := by
  induction w with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons x z y hadj w ih =>
    rcases hstep x z hadj with hOld | hNew | hNew
    · rcases ih with hzy | ⟨hza, hby⟩ | ⟨hzb, hay⟩
      · exact Or.inl (hOld.reachable.trans hzy)
      · exact Or.inr (Or.inl ⟨hOld.reachable.trans hza, hby⟩)
      · exact Or.inr (Or.inr ⟨hOld.reachable.trans hzb, hay⟩)
    · obtain ⟨hxa, hzb⟩ := hNew
      subst x
      subst z
      rcases ih with hby | ⟨_, hby⟩ | ⟨_, hay⟩
      · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, hby⟩)
      · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, hby⟩)
      · exact Or.inl hay
    · obtain ⟨hxb, hza⟩ := hNew
      subst x
      subst z
      rcases ih with hay | ⟨_, hby⟩ | ⟨_, hay⟩
      · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, hay⟩)
      · exact Or.inl hby
      · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, hay⟩)

private lemma opened_restricted_adj {d : ℕ} (S : Set (Vertex d))
    (ω : Configuration d) (e : Bond d) (x y : Vertex d)
    (h : (restrictedGraph (forceOpen e ω) S).Adj x y) :
    (restrictedGraph ω S).Adj x y ∨
      (x = e.1 ∧ y = bondTip e) ∨ (x = bondTip e ∧ y = e.1) := by
  obtain ⟨⟨f, hf, hends⟩, hxS, hyS⟩ := h
  by_cases hfe : f = e
  · subst f
    rcases hends with hends | hends
    · exact Or.inr (Or.inl hends)
    · exact Or.inr (Or.inr ⟨hends.2, hends.1⟩)
  · exact Or.inl ⟨⟨f, by simpa [forceOpen, hfe] using hf, hends⟩, hxS, hyS⟩

/-- Old components of x and y are disjoint when they are not connected. Finite
old walks within them give disjoint positive certificates, automatically avoiding
an old-closed tested bond. No assumed disjoint-path conclusion is used. -/
private lemma old_connections_avoiding {d : ℕ} (S : Set (Vertex d))
    (ω : Configuration d) (e : Bond d) (he : ω e = false)
    (x y a b : Vertex d) (hxS : x ∈ S) (hyS : y ∈ S)
    (hxy : ¬ (restrictedGraph ω S).Reachable x y)
    (hxa : (restrictedGraph ω S).Reachable x a)
    (hyb : (restrictedGraph ω S).Reachable y b) :
    AvoidingDisjointOccurrence e (connectionToSetEvent S x {a}) (connectionToSetEvent S b {y}) ω := by
  obtain ⟨p⟩ := hxa
  obtain ⟨q⟩ := hyb
  have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h ↦ h.1
  let p' : (openGraph ω).Walk x a := p.mapLe hle
  let q' : (openGraph ω).Walk y b := q.mapLe hle
  have hpS : ∀ z ∈ p'.support, z ∈ S := by
    simpa only [p', SimpleGraph.Walk.support_mapLe_eq_support] using restrictedWalk_support p hxS
  have hqS : ∀ z ∈ q'.support, z ∈ S := by
    simpa only [q', SimpleGraph.Walk.support_mapLe_eq_support] using restrictedWalk_support q hyS
  obtain ⟨F, hopenF, hedgeF, hforceF⟩ := openWalk_certificate p' S hpS
  obtain ⟨H, hopenH, hedgeH, hforceH⟩ := openWalk_certificate q' S hqS
  refine ⟨F, H, F.finite_toSet, H.finite_toSet, ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro f hfF hfH
    have hpz : f.1 ∈ p.support := by
      simpa only [p', SimpleGraph.Walk.support_mapLe_eq_support] using
        p'.fst_mem_support_of_mem_edges (hedgeF f hfF)
    have hqz : f.1 ∈ q.support := by
      simpa only [q', SimpleGraph.Walk.support_mapLe_eq_support] using
        q'.fst_mem_support_of_mem_edges (hedgeH f hfH)
    exact hxy ((p.takeUntil f.1 hpz).reachable.trans (q.takeUntil f.1 hqz).reachable.symm)
  · rintro (heF | heH)
    · have hfalse : (false : Bool) = true := he.symm.trans (hopenF e heF)
      cases hfalse
    · have hfalse : (false : Bool) = true := he.symm.trans (hopenH e heH)
      cases hfalse
  · intro θ hagree
    exact hforceF θ (fun f hf ↦ (hagree f hf).trans (hopenF f hf))
  · intro θ hagree
    rw [connectionToSetEvent_singleton_symm S b y]
    exact hforceH θ (fun f hf ↦ (hagree f hf).trans (hopenH f hf))

/-- Actual opening/new-connection support. The tested bond was closed, and the
OLD configuration has disjoint finite forcing certificates avoiding it, in one
of the two physical orientations. The result applies in particular to S∩U,
without constructing a different finite graph or assuming pivotal support. -/
theorem opening_connection_avoiding_support {d : ℕ} (S : Set (Vertex d))
    (x y : Vertex d) (e : Bond d) (ω : Configuration d)
    (hnew : forceOpen e ω ∈ connectionToSetEvent S x {y})
    (hold : ω ∉ connectionToSetEvent S x {y}) :
    ω e = false ∧
      (AvoidingDisjointOccurrence e (connectionToSetEvent S x {e.1})
        (connectionToSetEvent S (bondTip e) {y}) ω ∨
       AvoidingDisjointOccurrence e (connectionToSetEvent S x {bondTip e})
        (connectionToSetEvent S e.1 {y}) ω) := by
  have hclosed : ω e = false := by
    cases hval : ω e
    · rfl
    · have heq : forceOpen e ω = ω := by
        ext f
        by_cases hfe : f = e
        · subst f; simp [forceOpen, hval]
        · simp [forceOpen, hfe]
      exact False.elim (hold (heq ▸ hnew))
  obtain ⟨hxS, z, hz, hzS, hw⟩ := hnew
  have hzy : z = y := hz
  subst z
  have hxy : ¬ (restrictedGraph ω S).Reachable x y := by
    intro hp
    exact hold ⟨hxS, y, rfl, hzS, hp⟩
  obtain ⟨w⟩ := hw
  have hsplit := walk_single_edge_extension e.1 (bondTip e)
    (opened_restricted_adj S ω e) w
  refine ⟨hclosed, ?_⟩
  rcases hsplit with hOld | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
  · exact False.elim (hxy hOld)
  · exact Or.inl (old_connections_avoiding S ω e hclosed x y e.1 (bondTip e)
      hxS hzS hxy hxa hby.symm)
  · exact Or.inr (old_connections_avoiding S ω e hclosed x y (bondTip e) e.1
      hxS hzS hxy hxb hay.symm)

/-- Literal finite independent-product probability form of the closed-factor
identity. The explicit finite sums are the actual Bernoulli law, not a proxy. -/
theorem finite_avoiding_closed_probability {E : Type*} [Fintype E]
    (p : unitInterval) (e : E) (A B : Set (E → Bool)) :
    (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real
        {ω | ω e = false ∧ AvoidingDisjointOccurrence e A B ω} =
      (1-(p:ℝ)) * (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real
        {ω | AvoidingDisjointOccurrence e A B ω} := by
  have h := finiteExpectation_avoiding_closed_factor (p:ℝ) e A B
  have hE : finiteExpectation (p:ℝ) (fun ω ↦ (if ω e then 0 else 1) *
      (if AvoidingDisjointOccurrence e A B ω then 1 else 0)) =
        BK.eventProbability (p:ℝ) {ω | ω e = false ∧ AvoidingDisjointOccurrence e A B ω} := by
    unfold BK.eventProbability
    congr 1
    funext ω
    cases hv : ω e <;> by_cases ha : AvoidingDisjointOccurrence e A B ω <;> simp [hv, ha]
  rw [hE, BK.eventProbability_eq_measureReal p, BK.eventProbability_eq_measureReal p] at h
  exact h

end NearCritical
