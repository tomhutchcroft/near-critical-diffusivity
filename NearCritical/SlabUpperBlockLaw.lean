module

public import NearCritical.Bernoulli

/-! Block law for the renormalisation of prop.slab.upper: restricting the
percolation configuration to finitely many PAIRWISE DISJOINT finite bond blocks
(cubes and tubes) yields independent blocks, each with its finite Bernoulli
product law. This discharges the shape of the `map_Φ` field of
`RenormalizedExploration` once the cube/tube bond sets are shown disjoint. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory ProbabilityTheory Finset

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Block restriction map. -/
def blockRestrict (B : ι → Finset (Bond d)) (ω : Configuration d) : ∀ i, B i → Bool :=
  fun i e => ω e

lemma measurable_blockRestrict (B : ι → Finset (Bond d)) : Measurable (blockRestrict B) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun e => measurable_pi_apply _

/-- Disjoint blocks, as a sigma type, are in bijection with their union. -/
def blockSigmaEquiv (B : ι → Finset (Bond d)) (hB : Pairwise fun i j => Disjoint (B i) (B j)) :
    (Σ i, B i) ≃ (univ.biUnion B) :=
  Equiv.ofBijective (fun s => ⟨s.2.1, mem_biUnion.2 ⟨s.1, mem_univ _, s.2.2⟩⟩) <| by
    constructor
    · rintro ⟨i, e, he⟩ ⟨j, e', he'⟩ h
      simp only [Subtype.mk.injEq] at h
      subst h
      by_cases hij : i = j
      · subst hij; rfl
      · exact absurd he' (Finset.disjoint_left.1 (hB hij) he)
    · rintro ⟨e, he⟩
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 he
      exact ⟨⟨i, e, hi⟩, rfl⟩

theorem percolation_map_blockRestrict (p : unitInterval) (B : ι → Finset (Bond d))
    (hB : Pairwise fun i j => Disjoint (B i) (B j)) :
    Measure.map (blockRestrict B) (percolation d p) =
      Measure.pi (fun i => Measure.pi (fun _ : B i => bernoulliMeasure true false p)) := by
  set U := univ.biUnion B
  set E := blockSigmaEquiv B hB
  apply Measure.ext_of_singleton
  intro x
  let η₀ : U → Bool := fun u => x (E.symm u).1 (E.symm u).2
  have hpre : blockRestrict B ⁻¹' {x} = (U.restrict : Configuration d → (U → Bool)) ⁻¹' {η₀} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext u
      show ω u.1 = x (E.symm u).1 (E.symm u).2
      rw [← h]
      exact congrArg ω (congrArg Subtype.val (E.apply_symm_apply u)).symm
    · intro h
      funext i e
      have := congrFun h (E ⟨i, e⟩)
      change U.restrict ω (E ⟨i, e⟩) = x (E.symm (E ⟨i, e⟩)).1 (E.symm (E ⟨i, e⟩)).2 at this
      rw [Equiv.symm_apply_apply] at this
      exact this
  have hm : (percolation d p).map U.restrict =
      Measure.pi (fun _ : U => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  rw [Measure.map_apply (measurable_blockRestrict B) (MeasurableSet.singleton x), hpre,
    ← Measure.map_apply (Finset.measurable_restrict _) (MeasurableSet.singleton η₀), hm]
  simp only [Measure.pi_singleton]
  calc ∏ u : U, bernoulliMeasure true false p {η₀ u}
      = ∏ s : (Σ i, B i), bernoulliMeasure true false p {x s.1 s.2} :=
        (Fintype.prod_equiv E _ _ (fun s => by
          show _ = bernoulliMeasure true false p {x (E.symm (E s)).1 (E.symm (E s)).2}
          rw [Equiv.symm_apply_apply])).symm
    _ = ∏ i, ∏ e : B i, bernoulliMeasure true false p {x i e} := Fintype.prod_sigma _

end NearCritical
