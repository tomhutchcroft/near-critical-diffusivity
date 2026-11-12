module

public import NearCritical.NestAdaptiveExit
public import NearCritical.ChemicalThinning

/-! Fresh terminal exit under the actual independent thinning coupling.
Both open and retention bits may be used in the finite revealed history. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- The actual joint law of open past, retention past and fresh open bits.
The retention block need not be disjoint from either open block: it belongs to
an independent sample. -/
theorem percolation_coupled_block_integral {d : ℕ} (p q : unitInterval)
    (S R T : Finset (Bond d)) (hd : Disjoint S T)
    (f : (S → Bool) → (R → Bool) → (T → Bool) → ℝ) :
    (∫ z : Configuration d × Configuration d,
      f (S.restrict z.1) (R.restrict z.2) (T.restrict z.1)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ η, ∫ ζ, ∫ ξ, f η ζ ξ
        ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p))
        ∂(Measure.pi (fun _ : R => bernoulliMeasure true false q))
        ∂(Measure.pi (fun _ : S => bernoulliMeasure true false p)) := by
  let a := fun ω : Configuration d => (S.restrict ω,T.restrict ω)
  have ha : Measurable a := (Finset.measurable_restrict S).prodMk (Finset.measurable_restrict T)
  have hi : IndepFun (S.restrict : Configuration d → (S → Bool))
      (T.restrict : Configuration d → (T → Bool)) (percolation d p) :=
    iIndepFun.indepFun_finset S T hd
      (iIndepFun_infinitePi (fun _ : Bond d => (measurable_id : Measurable (id : Bool → Bool))))
      (fun e => measurable_pi_apply e)
  have hmap := hi.map_prod_eq_prod_map_map (Finset.measurable_restrict S).aemeasurable
    (Finset.measurable_restrict T).aemeasurable
  have hS : (percolation d p).map S.restrict = Measure.pi (fun _ : S => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  have hT : (percolation d p).map T.restrict = Measure.pi (fun _ : T => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  have hR : (percolation d q).map R.restrict = Measure.pi (fun _ : R => bernoulliMeasure true false q) :=
    Measure.infinitePi_map_restrict _
  rw [hS,hT] at hmap
  have hm := Measure.map_prod_map (percolation d p) (percolation d q) ha (Finset.measurable_restrict R)
  rw [hmap,hR] at hm
  let g := fun z : ((S → Bool) × (T → Bool)) × (R → Bool) => f z.1.1 z.2 z.1.2
  calc
    _ = ∫ z, g z ∂(((percolation d p).prod (percolation d q)).map
        (Prod.map a R.restrict)) :=
      (integral_map (ha.prodMap (Finset.measurable_restrict R)).aemeasurable
        (Integrable.of_finite : Integrable g _).aestronglyMeasurable).symm
    _ = _ := by
      rw [← hm]
      rw [integral_prod g Integrable.of_finite]
      rw [integral_prod _ Integrable.of_finite]
      apply integral_congr_ae
      filter_upwards [] with η
      exact integral_integral_swap (Integrable.of_finite : Integrable (fun z : (T → Bool) × (R → Bool) => f η z.2 z.1) _)

/-- Adaptive exit choices may depend on BOTH finite open and retention histories.
The pool is constructed from all possible history pairs. Empty choices are
allowed on zero-weight histories. -/
theorem percolation_coupled_exit_weighted_mean {d : ℕ} (p q : unitInterval)
    (hp : 0 < (p:ℝ)) (i : Fin d) (U : Finset (Vertex d)) {hi : ℤ}
    (hU : ∀ x ∈ U, x i ≤ hi) (S R : Finset (Bond d)) (hS : S ⊆ internalBondSet U)
    (choose : (S → Bool) × (R → Bool) → Finset (Vertex d))
    (hface : ∀ η, ∀ x ∈ choose η, x i = hi)
    (H : (S → Bool) × (R → Bool) → ℝ)
    (hlive : ∀ η, H η ≠ 0 → (choose η).Nonempty) :
    (∫ z : Configuration d × Configuration d,
      H (S.restrict z.1,R.restrict z.2) *
      (if ∃ x ∈ choose (S.restrict z.1,R.restrict z.2), z.1 (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict z.1,R.restrict z.2)).card)⁻¹ else 0)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z : Configuration d × Configuration d, H (S.restrict z.1,R.restrict z.2)
        ∂((percolation d p).prod (percolation d q)) := by
  let W := (Finset.univ : Finset ((S → Bool) × (R → Bool))).biUnion choose
  let T := nestExitBondSet i W
  have hW : ∀ x ∈ W, x i = hi := by
    intro x hx
    obtain ⟨η,_,hη⟩ := Finset.mem_biUnion.mp hx
    exact hface η x hη
  have hchoose : ∀ η, choose η ⊆ W := by
    intro η x hx
    exact Finset.mem_biUnion.mpr ⟨η,Finset.mem_univ _,hx⟩
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro e heS heT
    exact Finset.disjoint_left.mp (nestExitBondSet_disjoint_internal i U W hU hW)
      heT (hS heS)
  let weight := fun η ξ => if selectedExitSuccess i W (choose η) ξ
    then (1-(1-(p:ℝ))^(choose η).card)⁻¹ else (0:ℝ)
  have he (z : Configuration d × Configuration d) :
      weight (S.restrict z.1,R.restrict z.2) (T.restrict z.1) =
      (if ∃ x ∈ choose (S.restrict z.1,R.restrict z.2), z.1 (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict z.1,R.restrict z.2)).card)⁻¹ else 0) := by
    simp only [weight,T,selectedExitSuccess_restrict i W _ (hchoose _) z.1]
  have hmean (η : (S → Bool) × (R → Bool)) :
      (∫ ξ, H η * weight η ξ ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p))) = H η := by
    rw [integral_const_mul]
    by_cases hη : H η = 0
    · simp [hη]
    · have hq : 0 < freshTubeSuccessProbability p S T
          (fun _ ξ => selectedExitSuccess i W (choose η) ξ) (fun _ => false) := by
        change 0 < (Measure.pi (fun _ : T => bernoulliMeasure true false p)).real _
        rw [selectedExitSuccess_probability p i W _ (hchoose η)]
        exact exit_success_probability_pos p hp _ (hlive η hη)
      have hf := freshTubeSuccessWeight_integral p S T
        (fun _ ξ => selectedExitSuccess i W (choose η) ξ) (fun _ => false) hq
      have hweight : weight η = freshTubeSuccessWeight p S T
          (fun _ ξ => selectedExitSuccess i W (choose η) ξ) (fun _ => false) := by
        funext ξ
        simp only [weight,freshTubeSuccessWeight,freshTubeSuccessProbability,T,
          selectedExitSuccess_probability p i W _ (hchoose η)]
      rw [hweight,hf,mul_one]
  have hw := percolation_coupled_block_integral p q S R T hd
    (fun η ζ ξ => H (η,ζ) * weight (η,ζ) ξ)
  simp_rw [he,hmean] at hw
  have hbase := percolation_coupled_block_integral p q S R T hd (fun η ζ _ => H (η,ζ))
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hbase
  exact hw.trans hbase.symm

/-- The history is now literally the retained (critical) and open restrictions.
Together with percolation_thin_map this applies when the retained parameter
pc satisfies pc=p*q. No independence between critical and open histories is
assumed: they are coupled through the same open bits. -/
theorem percolation_thinned_exit_weighted_mean {d : ℕ} (p q : unitInterval)
    (hp : 0 < (p:ℝ)) (i : Fin d) (U : Finset (Vertex d)) {hi : ℤ}
    (hU : ∀ x ∈ U, x i ≤ hi) (S : Finset (Bond d)) (hS : S ⊆ internalBondSet U)
    (choose : (S → Bool) × (S → Bool) → Finset (Vertex d))
    (hface : ∀ η, ∀ x ∈ choose η, x i = hi)
    (H : (S → Bool) × (S → Bool) → ℝ)
    (hlive : ∀ η, H η ≠ 0 → (choose η).Nonempty) :
    (∫ z : Configuration d × Configuration d,
      H (S.restrict (thinConfiguration z),S.restrict z.1) *
      (if ∃ x ∈ choose (S.restrict (thinConfiguration z),S.restrict z.1), z.1 (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict (thinConfiguration z),S.restrict z.1)).card)⁻¹ else 0)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z : Configuration d × Configuration d, H (S.restrict (thinConfiguration z),S.restrict z.1)
        ∂((percolation d p).prod (percolation d q)) := by
  exact percolation_coupled_exit_weighted_mean p q hp i U hU S S hS
    (fun η => choose (thinConfiguration η,η.1)) (fun η => hface (thinConfiguration η,η.1))
    (fun η => H (thinConfiguration η,η.1)) (fun η => hlive (thinConfiguration η,η.1))

end NearCritical
