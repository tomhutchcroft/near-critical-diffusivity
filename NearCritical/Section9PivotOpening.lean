module
public import NearCritical.Section9CoalescenceOpenedSum
public import NearCritical.Section9SprinklingConnection
public import NearCritical.NestExitLaw

/-! Actual physical-bond openings and their monotone sprinkled connection. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

/-- Independent enrichment at the configuration level. No conditional p-law
identification is included in this definition. -/
def sprinkleOrConfiguration {d : ℕ} (ω ζ : Configuration d) : Configuration d :=
  fun b => ω b || ζ b

/-- Any finite physical bond pool has the exact independent opening law,
including the empty pool and q=0,1. -/
theorem section9_physical_bonds_open_probability {d : ℕ} (q : unitInterval)
    (H : Finset (Bond d)) :
    (percolation d q).real {ζ | ∃ b ∈ H, ζ b = true} = 1-(1-(q : ℝ))^H.card := by
  have hm : (percolation d q).map H.restrict =
      Measure.pi (fun _ : H => bernoulliMeasure true false q) :=
    Measure.infinitePi_map_restrict _
  have h := finite_bernoulli_exists_open (E := H) q
  rw [← hm,map_measureReal_apply (Finset.measurable_restrict H) (Set.toFinite _).measurableSet] at h
  have he : (H.restrict : Configuration d → (H → Bool)) ⁻¹' {η | ∃ b, η b = true} =
      {ζ : Configuration d | ∃ b ∈ H, ζ b = true} := by
    ext ζ
    simp only [Set.mem_preimage,Set.mem_setOf_eq,Finset.restrict]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨b.val,b.property,hb⟩
    · rintro ⟨b,hb,hopen⟩
      exact ⟨⟨b,hb⟩,hopen⟩
  rw [he] at h
  simpa only [Fintype.card_coe] using h

/-- A physical bond can label at most its two endpoint orientations.
The global oriented pivotal family need not project injectively. -/
theorem section9_oriented_physical_image_card_le {d : ℕ}
    (P : Finset (Vertex d × Vertex d)) (bond : (Vertex d × Vertex d) → Bond d)
    (hends : ∀ e ∈ P, s((bond e).1,bondTip (bond e)) = s(e.1,e.2)) :
    P.card ≤ 2*(P.image bond).card := by
  let H := P.image bond
  let ends := fun b : Bond d => ({(b.1,bondTip b),(bondTip b,b.1)} : Finset (Vertex d × Vertex d))
  have hsub : P ⊆ H.biUnion ends := by
    intro e he
    apply Finset.mem_biUnion.mpr
    refine ⟨bond e,Finset.mem_image.mpr ⟨e,he,rfl⟩,?_⟩
    have hor : e = ((bond e).1,bondTip (bond e)) ∨ e = (bondTip (bond e),(bond e).1) := by
      rcases Sym2.eq_iff.mp (hends e he) with ⟨hb,ht⟩ | ⟨hb,ht⟩
      · exact Or.inl (Prod.ext hb.symm ht.symm)
      · exact Or.inr (Prod.ext ht.symm hb.symm)
    simpa only [ends,Finset.mem_insert,Finset.mem_singleton] using hor
  calc
    _ ≤ (H.biUnion ends).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ H, (ends b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ H, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
    _ = _ := by simp [H,Nat.mul_comm]

/-- For every fixed actual critical configuration, an independent opening
of a physical pivot supplies an actual OR-configuration A-to-B connection.
The physical map is selected from the actual canonical middle geometry.
This is not a statement about a p-level conditioned reveal law. -/
theorem section9_fixed_pivot_opening_connection {d : ℕ} (i : Fin d) (n : ℕ)
    (hn : 0 < n) (F₁ F₃ A B : Finset (Vertex d)) :
    ∃ bond : (Vertex d × Vertex d) → Bond d,
      (∀ e ∈ orientedLatticePairs (section9FiniteMiddle i n),
        s((bond e).1,bondTip (bond e)) = s(e.1,e.2)) ∧
      ∀ (ω : Configuration d) (q : unitInterval),
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      let P := sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A B
      1-(1-(q : ℝ))^(P.image bond).card ≤
        (percolation d q).real {ζ | ∃ a ∈ A,
          sprinkleOrConfiguration ω ζ ∈ connectionToSetEvent
            ((L : Set (Vertex d)) ∪ (R : Set (Vertex d))) a (B : Set (Vertex d))} := by
  obtain ⟨bond,hbond⟩ := section9_middle_candidate_bond_map i n
  refine ⟨bond,hbond,?_⟩
  intro ω q L R Q₁ Q₃ E P
  rw [← section9_physical_bonds_open_probability q (P.image bond)]
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro ζ ⟨b,hbH,hζ⟩
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hbH
  have heE := (Finset.mem_filter.mp he).1
  have hends := hbond e heE
  have hopen : (openGraph (sprinkleOrConfiguration ω ζ)).Adj e.1 e.2 := by
    refine ⟨bond e,by simp only [sprinkleOrConfiguration,hζ,Bool.or_true],?_⟩
    rcases Sym2.eq_iff.mp hends with ⟨hb,ht⟩ | ⟨hb,ht⟩
    · exact Or.inl ⟨hb.symm,ht.symm⟩
    · exact Or.inr ⟨hb.symm,ht.symm⟩
  have hmono : ∀ b, ω b = true → sprinkleOrConfiguration ω ζ b = true := by
    intro b hb
    simp only [sprinkleOrConfiguration,hb,Bool.true_or]
  exact sprinkledPivotalPairs_nonempty_connection hmono E L R Q₁ F₁ Q₃ F₃ A B
    ⟨e,Finset.mem_filter.mpr ⟨he,hopen⟩⟩

end NearCritical
