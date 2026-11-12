module
public import NearCritical.Section9PhysicalOpeningCovariance
public import NearCritical.Section9FiniteLocalIntegrability

/-! Actual fresh target-success variance with shared physical pools. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem target_opening_event_measurable {d : ℕ} (H : Finset (Bond d)) :
    MeasurableSet {ζ : Configuration d | ∃ b ∈ H, ζ b = true} := by
  have he : {ζ : Configuration d | ∃ b ∈ H, ζ b = true} =
      ⋃ b : H, {ζ : Configuration d | ζ b.val = true} := by
    ext ζ
    constructor
    · rintro ⟨b,hb,hζ⟩
      exact Set.mem_iUnion.mpr ⟨⟨b,hb⟩,hζ⟩
    · intro hζ
      obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hζ
      exact ⟨b.val,b.property,hb⟩
  rw [he]
  exact MeasurableSet.iUnion fun b =>
    (measurableSet_singleton true).preimage (measurable_pi_apply b.val)

/-- The actual number of target pools receiving a fresh open bond has
variance at most its actual mean plus q times ordered physical overlaps.
Target events may overlap and no independence premise is imposed. -/
theorem section9_physical_target_success_variance_le {d : ℕ} {ι : Type*}
    (q : unitInterval) (I : Finset ι) (pools : ι → Finset (Bond d)) :
    let Y := fun ζ : Configuration d =>
      ∑ i ∈ I, if ∃ b ∈ pools i, ζ b = true then (1 : ℝ) else 0
    let m := ∫ ζ, Y ζ ∂percolation d q
    (∫ ζ, (Y ζ-m)^2 ∂percolation d q) ≤
      m+(q : ℝ)*(∑ i ∈ I, ∑ j ∈ I.erase i, ((pools i ∩ pools j).card : ℝ)) := by
  intro Y m
  let μ := percolation d q
  let E := fun i => {ζ : Configuration d | ∃ b ∈ pools i, ζ b = true}
  let Yi := fun i (ζ : Configuration d) => if ∃ b ∈ pools i, ζ b = true then (1 : ℝ) else 0
  let p := fun i => μ.real (E i)
  let cov := fun i j => μ.real (E i ∩ E j)-p i*p j
  have hE (i : ι) : MeasurableSet (E i) := target_opening_event_measurable (pools i)
  have hind (i : ι) : Yi i = (E i).indicator (fun _ => (1 : ℝ)) := by
    funext ζ
    simp only [Yi,Set.indicator_apply,E,Set.mem_setOf_eq]
  have hi (i : ι) : Integrable (Yi i) μ := by
    rw [hind]
    exact (integrable_const (1 : ℝ)).indicator (hE i)
  have hiY : Integrable Y μ := integrable_finsetSum I (fun i _ => hi i)
  have hprod (i j : ι) (ζ : Configuration d) :
      Yi i ζ*Yi j ζ = (E i ∩ E j).indicator (fun _ => (1 : ℝ)) ζ := by
    by_cases hi : ζ ∈ E i <;> by_cases hj : ζ ∈ E j <;>
      simp only [hind,Set.indicator_apply,Set.mem_inter_iff,hi,hj,true_and,false_and,
        and_true,and_false,if_true,if_false,mul_zero,zero_mul,mul_one]
  have hYsq (ζ : Configuration d) : (Y ζ)^2 =
      ∑ i ∈ I, ∑ j ∈ I, (E i ∩ E j).indicator (fun _ => (1 : ℝ)) ζ := by
    change (∑ i ∈ I, Yi i ζ)^2 = _
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hprod i j ζ)
  have hiYsq : Integrable (fun ζ => (Y ζ)^2) μ := by
    simp_rw [hYsq]
    exact integrable_finsetSum I (fun i _ => integrable_finsetSum I
      (fun j _ => (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j))))
  have hmean : m = ∑ i ∈ I, p i := by
    change (∫ ζ, ∑ i ∈ I, Yi i ζ ∂μ) = _
    rw [integral_finsetSum I (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hind]
    exact integral_indicator_one (hE i)
  have hsecond : (∫ ζ, (Y ζ)^2 ∂μ) = ∑ i ∈ I, ∑ j ∈ I, μ.real (E i ∩ E j) := by
    simp_rw [hYsq]
    rw [integral_finsetSum I (fun i _ => integrable_finsetSum I
      (fun j _ => (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j))))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum I (fun j _ => (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j)))]
    exact Finset.sum_congr rfl (fun j _ => integral_indicator_one ((hE i).inter (hE j)))
  have hcenter : (∫ ζ, (Y ζ-m)^2 ∂μ) = (∫ ζ, (Y ζ)^2 ∂μ)-m^2 := by
    have hpoly (ζ : Configuration d) : (Y ζ-m)^2 = (Y ζ)^2-(2*m)*Y ζ+m^2 := by ring
    simp_rw [hpoly]
    have hadd := integral_add (hiYsq.sub (hiY.const_mul (2*m))) (integrable_const (μ := μ) (m^2))
    have hsub := integral_sub hiYsq (hiY.const_mul (2*m))
    dsimp only [Pi.sub_apply,Pi.add_apply] at hadd hsub
    rw [hadd,hsub,integral_const_mul]
    have hc : (∫ _ζ : Configuration d, m^2 ∂μ) = m^2 := by simp [μ]
    rw [hc]
    change (∫ ζ, (Y ζ)^2 ∂μ)-(2*m)*m+m^2 = _
    ring
  have hpp : (∑ i ∈ I, ∑ j ∈ I, p i*p j) = (∑ i ∈ I, p i)^2 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hvariance : (∫ ζ, (Y ζ-m)^2 ∂μ) = ∑ i ∈ I, ∑ j ∈ I, cov i j := by
    rw [hcenter,hsecond]
    simp only [cov,Finset.sum_sub_distrib]
    rw [hpp,← hmean]
  have hdiag (i : ι) : cov i i ≤ p i := by
    have heq : cov i i = p i-(p i)^2 := by simp only [cov,Set.inter_self,p,pow_two]
    rw [heq]
    nlinarith only [sq_nonneg (p i)]
  have hoff (i j : ι) : cov i j ≤ (q : ℝ)*((pools i ∩ pools j).card : ℝ) :=
    section9_physical_opening_covariance_le q (pools i) (pools j)
  have hrow (i : ι) (hiI : i ∈ I) :
      (∑ j ∈ I, cov i j) ≤ p i+(q : ℝ)*(∑ j ∈ I.erase i, ((pools i ∩ pools j).card : ℝ)) := by
    calc
      _ = (∑ j ∈ I.erase i, cov i j)+cov i i := (Finset.sum_erase_add _ _ hiI).symm
      _ ≤ (∑ j ∈ I.erase i, (q : ℝ)*((pools i ∩ pools j).card : ℝ))+p i :=
        add_le_add (Finset.sum_le_sum fun j _ => hoff i j) (hdiag i)
      _ = _ := by rw [Finset.mul_sum]; ring
  rw [hvariance]
  calc
    _ ≤ ∑ i ∈ I, (p i+(q : ℝ)*(∑ j ∈ I.erase i, ((pools i ∩ pools j).card : ℝ))) :=
      Finset.sum_le_sum hrow
    _ = _ := by rw [Finset.sum_add_distrib,← hmean,Finset.mul_sum]

end NearCritical
