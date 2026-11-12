module

public import NearCritical.Section10CoupledReveal

/-! Full paired fresh law for the actual thinning coupling. Both fresh open
and retention bits may be used, hence also their critical AND configuration.
The critical past event is arbitrary on a fixed finite mask: no monotonicity
or supplied conditional-independence assumption is used. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical

private theorem disjoint_restriction_pair_map {d : ℕ} (p : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T) :
    (percolation d p).map (fun ω => (S.restrict ω,T.restrict ω)) =
      (Measure.pi (fun _ : S => bernoulliMeasure true false p)).prod
        (Measure.pi (fun _ : T => bernoulliMeasure true false p)) := by
  have hi : IndepFun (S.restrict : Configuration d → (S → Bool))
      (T.restrict : Configuration d → (T → Bool)) (percolation d p) :=
    iIndepFun.indepFun_finset S T hd
      (iIndepFun_infinitePi (fun _ : Bond d => (measurable_id : Measurable (id : Bool → Bool))))
      (fun e => measurable_pi_apply e)
  have hm := hi.map_prod_eq_prod_map_map (Finset.measurable_restrict S).aemeasurable
    (Finset.measurable_restrict T).aemeasurable
  have hS : (percolation d p).map S.restrict =
      Measure.pi (fun _ : S => bernoulliMeasure true false p) := Measure.infinitePi_map_restrict _
  have hT : (percolation d p).map T.restrict =
      Measure.pi (fun _ : T => bernoulliMeasure true false p) := Measure.infinitePi_map_restrict _
  rwa [hS,hT] at hm

/-- Exact four-block integral under the actual two independent infinite
samples, with the finite order past-p, past-q, fresh-p, fresh-q. -/
theorem coupled_four_block_integral {d : ℕ} (p q : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T)
    (f : (S → Bool) → (S → Bool) → (T → Bool) → (T → Bool) → ℝ) :
    (∫ z : Configuration d × Configuration d,
      f (S.restrict z.1) (S.restrict z.2) (T.restrict z.1) (T.restrict z.2)
        ∂((percolation d p).prod (percolation d q))) =
      ∫ η, ∫ ζ, ∫ ξ, ∫ χ, f η ζ ξ χ
        ∂(Measure.pi (fun _ : T => bernoulliMeasure true false q))
        ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p))
        ∂(Measure.pi (fun _ : S => bernoulliMeasure true false q))
        ∂(Measure.pi (fun _ : S => bernoulliMeasure true false p)) := by
  let a := fun ω : Configuration d => (S.restrict ω,T.restrict ω)
  have ha : Measurable a := (Finset.measurable_restrict S).prodMk (Finset.measurable_restrict T)
  have hm := Measure.map_prod_map (percolation d p) (percolation d q) ha ha
  rw [disjoint_restriction_pair_map p S T hd,disjoint_restriction_pair_map q S T hd] at hm
  let g := fun z : ((S → Bool) × (T → Bool)) × ((S → Bool) × (T → Bool)) =>
    f z.1.1 z.2.1 z.1.2 z.2.2
  calc
    _ = ∫ z, g z ∂(((percolation d p).prod (percolation d q)).map (Prod.map a a)) :=
      (integral_map (ha.prodMap ha).aemeasurable
        (Integrable.of_finite : Integrable g _).aestronglyMeasurable).symm
    _ = _ := by
      rw [← hm]
      rw [integral_prod g Integrable.of_finite,integral_prod _ Integrable.of_finite]
      apply integral_congr_ae
      filter_upwards [] with η
      have hinner (ξ : T → Bool) :
          (∫ z : (S → Bool) × (T → Bool), f η z.1 ξ z.2
            ∂((Measure.pi (fun _ : S => bernoulliMeasure true false q)).prod
              (Measure.pi (fun _ : T => bernoulliMeasure true false q)))) =
          ∫ ζ, ∫ χ, f η ζ ξ χ
            ∂(Measure.pi (fun _ : T => bernoulliMeasure true false q))
            ∂(Measure.pi (fun _ : S => bernoulliMeasure true false q)) :=
        integral_prod _ Integrable.of_finite
      change (∫ ξ, ∫ z : (S → Bool) × (T → Bool), f η z.1 ξ z.2
          ∂((Measure.pi (fun _ : S => bernoulliMeasure true false q)).prod
            (Measure.pi (fun _ : T => bernoulliMeasure true false q)))
          ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p))) = _
      simp_rw [hinner]
      exact integral_integral_swap (Integrable.of_finite : Integrable
        (fun z : (T → Bool) × (S → Bool) => ∫ χ, f η z.2 z.1 χ
          ∂(Measure.pi (fun _ : T => bernoulliMeasure true false q))) _)

/-- The paired fresh sample is independent of both finite past samples under
the actual product measure, derived from the four-block law. -/
theorem coupled_past_fresh_pair_integral {d : ℕ} (p q : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T)
    (H : (S → Bool) × (S → Bool) → ℝ) (g : (T → Bool) × (T → Bool) → ℝ) :
    (∫ z : Configuration d × Configuration d,
      H (S.restrict z.1,S.restrict z.2)*g (T.restrict z.1,T.restrict z.2)
        ∂((percolation d p).prod (percolation d q))) =
      (∫ z : Configuration d × Configuration d, H (S.restrict z.1,S.restrict z.2)
        ∂((percolation d p).prod (percolation d q))) *
      (∫ z : Configuration d × Configuration d, g (T.restrict z.1,T.restrict z.2)
        ∂((percolation d p).prod (percolation d q))) := by
  have hf := coupled_four_block_integral p q S T hd (fun η ζ ξ χ => H (η,ζ)*g (ξ,χ))
  simp_rw [integral_const_mul,integral_mul_const] at hf
  have hS := percolation_coupled_block_integral p q S S ∅ (by simp) (fun η ζ _ => H (η,ζ))
  have hT := percolation_coupled_block_integral p q T T ∅ (by simp) (fun ξ χ _ => g (ξ,χ))
  simp only [integral_const,probReal_univ,one_smul] at hS hT
  rwa [← hS,← hT] at hf

/-- Conditioning on a positive-weight finite history of both configurations
leaves a disjoint paired sample fresh. The next observable may depend on the
observed history, which is fixed on the conditioning atom. -/
theorem coupled_past_atom_fresh_pair_mean {d : ℕ} (p q : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T)
    (history : (S → Bool) × (S → Bool))
    (g : ((S → Bool) × (S → Bool)) → ((T → Bool) × (T → Bool)) → ℝ)
    (hprob : 0 < ∫ z : Configuration d × Configuration d,
      ({history} : Set ((S → Bool) × (S → Bool))).indicator (fun _ => (1 : ℝ))
        (S.restrict z.1, S.restrict z.2) ∂((percolation d p).prod (percolation d q))) :
    (∫ z : Configuration d × Configuration d,
      ({history} : Set ((S → Bool) × (S → Bool))).indicator (fun _ => (1 : ℝ))
        (S.restrict z.1, S.restrict z.2) *
        g (S.restrict z.1, S.restrict z.2) (T.restrict z.1, T.restrict z.2)
          ∂((percolation d p).prod (percolation d q))) /
      (∫ z : Configuration d × Configuration d,
        ({history} : Set ((S → Bool) × (S → Bool))).indicator (fun _ => (1 : ℝ))
          (S.restrict z.1, S.restrict z.2) ∂((percolation d p).prod (percolation d q))) =
    ∫ z : Configuration d × Configuration d,
      g history (T.restrict z.1, T.restrict z.2)
        ∂((percolation d p).prod (percolation d q)) := by
  let H := ({history} : Set ((S → Bool) × (S → Bool))).indicator (fun _ => (1 : ℝ))
  have he (a : (S → Bool) × (S → Bool)) (b : (T → Bool) × (T → Bool)) :
      H a * g a b = H a * g history b := by
    by_cases ha : a = history
    · rw [ha]
    · simp [H, ha]
  change 0 < ∫ z : Configuration d × Configuration d, H (S.restrict z.1, S.restrict z.2)
    ∂((percolation d p).prod (percolation d q)) at hprob
  change (∫ z : Configuration d × Configuration d,
    H (S.restrict z.1, S.restrict z.2) *
      g (S.restrict z.1, S.restrict z.2) (T.restrict z.1, T.restrict z.2)
      ∂((percolation d p).prod (percolation d q))) /
    (∫ z : Configuration d × Configuration d, H (S.restrict z.1, S.restrict z.2)
      ∂((percolation d p).prod (percolation d q))) = _
  simp_rw [he]
  rw [coupled_past_fresh_pair_integral p q S T hd H (g history)]
  field_simp [hprob.ne']

def criticalBlockEvent {d : ℕ} (S : Finset (Bond d)) (A : Set (S → Bool)) : Set (Configuration d) :=
  S.restrict ⁻¹' A

/-- Arbitrary finite critical-cylinder conditioning preserves the entire
fresh paired law. A may include mask-local cluster graph decorations. -/
theorem coupled_criticalBlock_fresh_pair_factorization {d : ℕ}
    (p q pc : unitInterval) (hpc : (pc:ℝ) = (p:ℝ)*(q:ℝ))
    (S T : Finset (Bond d)) (hd : Disjoint S T) (A : Set (S → Bool))
    (g : (T → Bool) × (T → Bool) → ℝ) :
    (∫ z : Configuration d × Configuration d,
      (criticalBlockEvent S A).indicator (fun _ => (1:ℝ)) (thinConfiguration z) *
        g (T.restrict z.1,T.restrict z.2) ∂((percolation d p).prod (percolation d q))) =
      (percolation d pc).real (criticalBlockEvent S A) *
        (∫ z : Configuration d × Configuration d, g (T.restrict z.1,T.restrict z.2)
          ∂((percolation d p).prod (percolation d q))) := by
  let K : (S → Bool) × (S → Bool) → ℝ := fun η =>
    A.indicator (fun _ => (1:ℝ)) (fun e => η.1 e && η.2 e)
  have he (z : Configuration d × Configuration d) :
      K (S.restrict z.1,S.restrict z.2) =
        (criticalBlockEvent S A).indicator (fun _ => (1:ℝ)) (thinConfiguration z) := by
    rfl
  have hf := coupled_past_fresh_pair_integral p q S T hd K g
  simp_rw [he] at hf
  have hA : MeasurableSet (criticalBlockEvent S A) :=
    (Set.to_countable A).measurableSet.preimage (Finset.measurable_restrict S)
  have hm : (∫ z : Configuration d × Configuration d,
      (criticalBlockEvent S A).indicator (fun _ => (1:ℝ)) (thinConfiguration z)
        ∂((percolation d p).prod (percolation d q))) =
      (percolation d pc).real (criticalBlockEvent S A) := by
    calc
      _ = ∫ ω : Configuration d, (criticalBlockEvent S A).indicator (fun _ => (1:ℝ)) ω
          ∂(((percolation d p).prod (percolation d q)).map thinConfiguration) :=
        (integral_map measurable_thinConfiguration.aemeasurable
          (measurable_const.indicator hA).aestronglyMeasurable).symm
      _ = _ := by
        rw [percolation_thin_map d p q pc hpc]
        exact integral_indicator_one hA
  rwa [hm] at hf

theorem coupled_criticalBlock_conditional_fresh_pair_mean {d : ℕ}
    (p q pc : unitInterval) (hpc : (pc:ℝ) = (p:ℝ)*(q:ℝ))
    (S T : Finset (Bond d)) (hd : Disjoint S T) (A : Set (S → Bool))
    (g : (T → Bool) × (T → Bool) → ℝ)
    (hprob : 0 < (percolation d pc).real (criticalBlockEvent S A)) :
    (∫ z : Configuration d × Configuration d,
      (criticalBlockEvent S A).indicator (fun _ => (1:ℝ)) (thinConfiguration z) *
        g (T.restrict z.1,T.restrict z.2) ∂((percolation d p).prod (percolation d q))) /
          (percolation d pc).real (criticalBlockEvent S A) =
      ∫ z : Configuration d × Configuration d, g (T.restrict z.1,T.restrict z.2)
        ∂((percolation d p).prod (percolation d q)) := by
  rw [coupled_criticalBlock_fresh_pair_factorization p q pc hpc S T hd A g]
  field_simp [hprob.ne']

end NearCritical.Section10
