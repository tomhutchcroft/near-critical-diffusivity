module

public import NearCritical.MaskedArmNegativeReflection
public import NearCritical.MaskedArmMidpoint

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- The negative-face estimate has the same constants and parameter window as
the positive-face estimate. Its opposite depth is the reflected starting height. -/
theorem maskedWaterCube_negative_face_exponential_midpoint {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (r R : ℕ) (p q : unitInterval) (x : DomainVertex (waterCube d i r R)),
      let H : ℕ := 2*r+1
      let k : ℤ := x.val i+(r : ℤ)
      let depth : ℤ := (H : ℤ)-k
      x.val ∈ waterCube d i r R → 0 < k → 2*depth ≤ (H : ℤ)+1 →
      q ≤ p → q ≤ criticalPoint d →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(H : ℝ)^2 →
      (bulkPercolation (waterCube d i r R) i (H : ℝ) δ p q).real
        (waterCubeFaceConnectionEvent i r R false x) ≤
          C*((depth : ℝ)+1)/(H : ℝ)^3 *
            Real.exp (-(H : ℝ)*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))/C) := by
  obtain ⟨C, ε, hC, hε, hpositive⟩ :=
    maskedWaterCube_positive_face_exponential_midpoint i hB hb hCo hpc hpc1
      pioneers ordinary δ hδ hδ1
  refine ⟨C, ε, hC, hε, ?_⟩
  intro r R p q x
  dsimp only
  intro hx hk hdepth hqp hq hp
  have hxlo : -(r : ℤ) < x.val i := by omega
  let a : Vertex d := Pi.single i (1 : ℤ)
  have hx' : a-x.val ∈ waterCube d i r R := waterCube_reflect_base i r R hx hxlo
  let x' : DomainVertex (waterCube d i r R) := ⟨a-x.val, base_mem_sitesPlus hx'⟩
  have hreflect : x'.val i+(r : ℤ) =
      ((2*r+1 : ℕ) : ℤ)-(x.val i+(r : ℤ)) := by
    change (a-x.val) i+(r : ℤ) = _
    simp only [a, Pi.sub_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    omega
  have hhalf : 2*(x'.val i+(r : ℤ)) ≤ ((2*r+1 : ℕ) : ℤ)+1 := by
    rw [hreflect]
    exact hdepth
  have hfar := hpositive r R p q x' hx' hhalf hqp hq hp
  rw [hreflect] at hfar
  have hcomparison := maskedWaterCube_negativeFace_probability_le_reflected
    i r R δ hδ.le p q x hx hxlo
  dsimp only at hcomparison
  exact (show
    (bulkPercolation (waterCube d i r R) i ((2*r+1 : ℕ) : ℝ) δ p q).real
        (waterCubeFaceConnectionEvent i r R false x) ≤
      (bulkPercolation (waterCube d i r R) i ((2*r+1 : ℕ) : ℝ) δ p q).real
        (waterCubeFaceConnectionEvent i r R true x') from by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      waterCubeFaceConnectionEvent, Bool.false_eq_true, ite_false, ite_true, x', a]
      using hcomparison).trans hfar

end NearCritical
