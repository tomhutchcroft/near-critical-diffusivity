module
public import NearCritical.Section9SprinkleOrLaw
public import NearCritical.SlabUpperLabelCoupling

/-! The genuine joint enrichment law and FIRST critical-reveal conditioning. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Set
open scoped Classical

private def coupledBits {E : Type*} (z : (E → Bool) × (E → Bool)) : E → Bool × Bool :=
  fun e => (z.1 e,z.1 e || z.2 e)

private theorem measurable_coupledBits {E : Type*} : Measurable (coupledBits (E := E)) := by
  apply measurable_pi_iff.mpr
  intro e
  exact (measurable_of_finite (fun z : Bool × Bool => (z.1,z.1 || z.2))).comp
    ((measurable_pi_apply e |>.comp (measurable_fst : Measurable (Prod.fst : (E → Bool) × (E → Bool) → _))).prodMk
      (measurable_pi_apply e |>.comp (measurable_snd : Measurable (Prod.snd : (E → Bool) × (E → Bool) → _))))

private theorem coupled_pair_sigmaFinite (p q : unitInterval) :
    SigmaFinite (((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool => (z.1, z.1 || z.2))) := by
  let μ : Measure (Bool × Bool) :=
    (bernoulliMeasure true false p).prod (bernoulliMeasure true false q)
  let f : Bool × Bool → Bool × Bool := fun z => (z.1, z.1 || z.2)
  change SigmaFinite (μ.map f)
  letI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  exact @IsFiniteMeasure.toSigmaFinite (Bool × Bool) _ (μ.map f)
    (μ.isFiniteMeasure_map f)

private theorem threshold_pair_map (p q : unitInterval) :
    (volume : Measure unitInterval).map
      (fun u => (labelThreshold p u,labelThreshold (orParameter p q) u)) =
    ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool => (z.1,z.1 || z.2)) := by
  let r := orParameter p q
  have hpr : p ≤ r := by
    change (p : ℝ) ≤ (p : ℝ)+(1-(p : ℝ))*(q : ℝ)
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr p.property.2) q.property.1)
  have hle (t : unitInterval) : (volume : Measure unitInterval).real (Set.Iic t) = (t : ℝ) := by
    have hh : ((volume : Measure unitInterval).map (labelThreshold t)).real {true} = (t : ℝ) := by
      rw [map_labelThreshold]
      simp
    rw [map_measureReal_apply (measurable_labelThreshold t) (measurableSet_singleton true),
      labelThreshold_preimage_true] at hh
    exact hh
  have hgt (t : unitInterval) : (volume : Measure unitInterval).real (Set.Ioi t) = 1-(t : ℝ) := by
    have hh : ((volume : Measure unitInterval).map (labelThreshold t)).real {false} = 1-(t : ℝ) := by
      rw [map_labelThreshold]
      simp
    rw [map_measureReal_apply (measurable_labelThreshold t) (measurableSet_singleton false),
      labelThreshold_preimage_false] at hh
    exact hh
  have hFF : (fun u => (labelThreshold p u,labelThreshold r u)) ⁻¹' {(false,false)} = Set.Ioi r := by
    ext u
    by_cases hu : u ≤ r
    · simp [labelThreshold,hu,not_lt.mpr hu]
    · have hup : ¬ u ≤ p := fun hp => hu (hp.trans hpr)
      simp [labelThreshold,hu,hup,lt_of_not_ge hu]
  have hFT : (fun u => (labelThreshold p u,labelThreshold r u)) ⁻¹' {(false,true)} = Set.Ioc p r := by
    ext u
    simp [labelThreshold,Set.mem_Ioc,not_le]
  have hTF : (fun u => (labelThreshold p u,labelThreshold r u)) ⁻¹' {(true,false)} = ∅ := by
    ext u
    change (decide (u ≤ p),decide (u ≤ r)) = (true,false) ↔ False
    simp only [Prod.mk.injEq,decide_eq_true_eq,decide_eq_false_iff_not]
    exact ⟨fun h => h.2 (h.1.trans hpr),False.elim⟩
  have hTT : (fun u => (labelThreshold p u,labelThreshold r u)) ⁻¹' {(true,true)} = Set.Iic p := by
    ext u
    change (decide (u ≤ p),decide (u ≤ r)) = (true,true) ↔ u ≤ p
    simp only [Prod.mk.injEq,decide_eq_true_eq]
    exact ⟨And.left,fun h => ⟨h,h.trans hpr⟩⟩
  have hoFF : (fun z : Bool × Bool => (z.1,z.1 || z.2)) ⁻¹' {(false,false)} =
      ({false} : Set Bool) ×ˢ {false} := by ext ⟨a,b⟩; cases a <;> cases b <;> simp
  have hoFT : (fun z : Bool × Bool => (z.1,z.1 || z.2)) ⁻¹' {(false,true)} =
      ({false} : Set Bool) ×ˢ {true} := by ext ⟨a,b⟩; cases a <;> cases b <;> simp
  have hoTF : (fun z : Bool × Bool => (z.1,z.1 || z.2)) ⁻¹' {(true,false)} = ∅ := by
    ext ⟨a,b⟩; cases a <;> cases b <;> simp
  have hoTT : (fun z : Bool × Bool => (z.1,z.1 || z.2)) ⁻¹' {(true,true)} =
      ({true} : Set Bool) ×ˢ Set.univ := by ext ⟨a,b⟩; cases a <;> cases b <;> simp
  letI := coupled_pair_sigmaFinite p q
  refine (MeasureTheory.ext_iff_measureReal_singleton
    (μ1 := (volume : Measure unitInterval).map
      (fun u => (labelThreshold p u, labelThreshold r u)))
    (μ2 := ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool => (z.1, z.1 || z.2)))).mpr ?_
  rintro ⟨a,b⟩
  rw [map_measureReal_apply ((measurable_labelThreshold p).prodMk (measurable_labelThreshold r))
    (measurableSet_singleton (a,b)),map_measureReal_apply (measurable_of_finite _)
      (measurableSet_singleton (a,b))]
  cases a <;> cases b
  · rw [hFF,hoFF,hgt r,measureReal_prod_prod]
    have hp : (bernoulliMeasure true false p).real {false} = 1-(p : ℝ) := by simp
    have hq : (bernoulliMeasure true false q).real {false} = 1-(q : ℝ) := by simp
    rw [hp,hq]
    change 1-((p : ℝ)+(1-(p : ℝ))*(q : ℝ)) = (1-(p : ℝ))*(1-(q : ℝ))
    ring
  · rw [hFT,hoFT,measureReal_prod_prod]
    have hv : (volume : Measure unitInterval).real (Set.Ioc p r) = (r : ℝ)-(p : ℝ) := by
      rw [measureReal_def,unitInterval.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hpr)]
    rw [hv]
    have hp : (bernoulliMeasure true false p).real {false} = 1-(p : ℝ) := by simp
    have hq : (bernoulliMeasure true false q).real {true} = (q : ℝ) := by simp
    rw [hp,hq]
    change ((p : ℝ)+(1-(p : ℝ))*(q : ℝ))-(p : ℝ) = _
    ring
  · simp only [hTF,hoTF,measureReal_empty]
  · rw [hTT,hoTT,hle p,measureReal_prod_prod]
    simp

private theorem finite_coupledBits_map {E : Type*} [Fintype E] (p q : unitInterval) :
    ((Measure.pi fun _ : E => bernoulliMeasure true false p).prod
      (Measure.pi fun _ : E => bernoulliMeasure true false q)).map coupledBits =
      Measure.pi fun _ : E => ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
        (fun z : Bool × Bool => (z.1,z.1 || z.2)) := by
  let equiv := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool E
  have he := (measurePreserving_arrowProdEquivProdArrow Bool Bool E
    (fun _ => bernoulliMeasure true false p) (fun _ => bernoulliMeasure true false q)).map_eq
  rw [← he,Measure.map_map measurable_coupledBits equiv.measurable]
  change (Measure.pi fun _ : E => (bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
    (fun z e => ((z e).1,(z e).1 || (z e).2)) = _
  exact Measure.pi_map_pi (f := fun _ (z : Bool × Bool) => (z.1, z.1 || z.2))
    (hμ := fun _ => coupled_pair_sigmaFinite p q)
    (fun _ => (measurable_of_finite _).aemeasurable)

private theorem infinite_coupledBits_map (d : ℕ) (p q : unitInterval) :
    ((percolation d p).prod (percolation d q)).map (coupledBits (E := Bond d)) =
      Measure.infinitePi fun _ : Bond d =>
        ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
          (fun z : Bool × Bool => (z.1,z.1 || z.2)) := by
  refine (Measure.isProjectiveLimit_infinitePi
    (fun _ : Bond d => ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool => (z.1,z.1 || z.2)))).unique ?_ |>.symm
  intro s
  have hs : Measurable (s.restrict : Configuration d → (s → Bool)) := Finset.measurable_restrict s
  have hsp : Measurable (s.restrict : (Bond d → Bool × Bool) → (s → Bool × Bool)) :=
    Finset.measurable_restrict s
  have hprod : ((percolation d p).prod (percolation d q)).map (Prod.map s.restrict s.restrict) =
      (Measure.pi fun _ : s => bernoulliMeasure true false p).prod
        (Measure.pi fun _ : s => bernoulliMeasure true false q) := by
    rw [← Measure.map_prod_map _ _ hs hs]
    simp only [percolation,Measure.infinitePi_map_restrict]
  rw [Measure.map_map hsp measurable_coupledBits]
  calc
    _ = (((percolation d p).prod (percolation d q)).map
        (Prod.map s.restrict s.restrict)).map coupledBits := by
      rw [Measure.map_map measurable_coupledBits (hs.prodMap hs)]
      rfl
    _ = _ := by rw [hprod,finite_coupledBits_map p q]

/-- The full JOINT critical/enriched pair law equals the common-label
nested-threshold law. Matching only the enriched marginal would not suffice. -/
theorem section9_sprinkle_or_joint_label_law (d : ℕ) (p q : unitInterval) :
    let Λ := Measure.infinitePi fun _ : Bond d => (volume : Measure unitInterval)
    ((percolation d p).prod (percolation d q)).map
      (fun z => (z.1,sprinkleOrConfiguration z.1 z.2)) =
    Λ.map (fun u => (labelConfiguration p u,labelConfiguration (orParameter p q) u)) := by
  intro Λ
  let F := fun u : Bond d → unitInterval => fun b =>
    (labelThreshold p (u b),labelThreshold (orParameter p q) (u b))
  have hF : Measurable F := measurable_pi_iff.mpr fun b =>
    ((measurable_labelThreshold p).prodMk (measurable_labelThreshold (orParameter p q))).comp
      (measurable_pi_apply b)
  have hlabel : Λ.map F = Measure.infinitePi fun _ : Bond d =>
      ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
        (fun z : Bool × Bool => (z.1,z.1 || z.2)) := by
    rw [show F = (fun u b => (labelThreshold p (u b),labelThreshold (orParameter p q) (u b))) from rfl,
      Measure.infinitePi_map_pi _ (fun _ =>
        (measurable_labelThreshold p).prodMk (measurable_labelThreshold (orParameter p q)))]
    simp only [threshold_pair_map]
  let equiv := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Bond d)
  have hfield := (infinite_coupledBits_map d p q).trans hlabel.symm
  have h := congrArg (fun ρ : Measure (Bond d → Bool × Bool) => ρ.map equiv) hfield
  rw [Measure.map_map equiv.measurable measurable_coupledBits,Measure.map_map equiv.measurable hF] at h
  exact h

private theorem joint_cond_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (S : Set β) (hS : MeasurableSet S) :
    (ProbabilityTheory.cond μ (f ⁻¹' S)).map f = ProbabilityTheory.cond (μ.map f) S := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul _ hf.aemeasurable,← Measure.restrict_map hf hS,Measure.map_apply hf hS]

/-- The same JOINT law after conditioning the FIRST actual critical reveal.
The enriched configuration's own heart clusters are not the conditioning data.
Zero atoms are included as equality of conditional measures. -/
theorem section9_sprinkle_or_joint_reveal_label_law {d : ℕ} (p q : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) :
    let Λ := Measure.infinitePi fun _ : Bond d => (volume : Measure unitInterval)
    let E := section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).map
      (fun z => (z.1,sprinkleOrConfiguration z.1 z.2)) =
    (ProbabilityTheory.cond Λ ((labelConfiguration p) ⁻¹' E)).map
      (fun u => (labelConfiguration p u,labelConfiguration (orParameter p q) u)) := by
  intro Λ E
  let O := fun z : Configuration d × Configuration d => (z.1,sprinkleOrConfiguration z.1 z.2)
  let T := fun u : Bond d → unitInterval =>
    (labelConfiguration p u,labelConfiguration (orParameter p q) u)
  let S : Set (Configuration d × Configuration d) := Prod.fst ⁻¹' E
  have hO : Measurable O := measurable_fst.prodMk measurable_sprinkleOrConfiguration
  have hT : Measurable T := (measurable_labelConfiguration p).prodMk
    (measurable_labelConfiguration (orParameter p q))
  have hS : MeasurableSet S :=
    (measurableSet_section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃).preimage measurable_fst
  have hpreO : O ⁻¹' S = E ×ˢ Set.univ := by
    ext z
    simp only [O,S,Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
  have hpreT : T ⁻¹' S = (labelConfiguration p) ⁻¹' E := rfl
  have hprod : (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q) =
      ProbabilityTheory.cond ((percolation d p).prod (percolation d q)) (E ×ˢ Set.univ) := by
    unfold section9RevealedLaw ProbabilityTheory.cond
    rw [Measure.prod_smul_left,Measure.restrict_prod_eq_prod_univ]
    simp only [E,Measure.prod_prod,measure_univ,mul_one]
  have hjoint : ((percolation d p).prod (percolation d q)).map O = Λ.map T :=
    section9_sprinkle_or_joint_label_law d p q
  calc
    _ = (ProbabilityTheory.cond ((percolation d p).prod (percolation d q)) (O ⁻¹' S)).map O := by
      rw [hpreO,← hprod]
    _ = ProbabilityTheory.cond (((percolation d p).prod (percolation d q)).map O) S :=
      joint_cond_map _ O hO S hS
    _ = ProbabilityTheory.cond (Λ.map T) S := by rw [hjoint]
    _ = (ProbabilityTheory.cond Λ (T ⁻¹' S)).map T := (joint_cond_map Λ T hT S hS).symm
    _ = _ := by rw [hpreT]

end NearCritical
