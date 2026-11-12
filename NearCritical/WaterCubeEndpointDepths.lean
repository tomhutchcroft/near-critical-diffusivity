module
public import NearCritical.WaterCubeOrdinaryArms
public import NearCritical.WaterCubeLayerSum

/-! Actual endpoint bookkeeping for eq.aa_bound_step2. Distinguished-coordinate
bonds shift the layer by one; transverse bonds do not. Middle-layer bonds are
kept separate rather than silently applying a failed half-space depth condition. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

def waterCubeDirectionStep {d : ℕ} (i : Fin d) {r R : ℕ}
    (e : IssuedBond (waterCube d i r R)) : ℕ := if e.val.2 = i then 1 else 0

lemma waterCubeDirectionStep_le_one {d : ℕ} (i : Fin d) {r R : ℕ}
    (e : IssuedBond (waterCube d i r R)) : waterCubeDirectionStep i e ≤ 1 := by
  unfold waterCubeDirectionStep
  split <;> omega

/-- Coordinates of both actual endpoints, with the zero-based base layer. -/
theorem waterCube_endpoint_coordinates {d : ℕ} (i : Fin d) (r R : ℕ)
    (e : IssuedBond (waterCube d i r R)) :
    (((issuedNetwork (waterCube d i r R)).tail e).val i =
      (waterCubeLayer i r e.val.1 : ℤ) - (r : ℤ)) ∧
    (((issuedNetwork (waterCube d i r R)).head e).val i =
      (waterCubeLayer i r e.val.1 : ℤ) - (r : ℤ) + waterCubeDirectionStep i e) := by
  have hx : e.val.1 ∈ waterCube d i r R := (Finset.mem_product.mp e.property).1
  have hi := (mem_rectangularBox.mp hx) i
  simp only [ite_true] at hi
  have hk : ((waterCubeLayer i r e.val.1 : ℕ) : ℤ) = e.val.1 i + (r : ℤ) := by
    unfold waterCubeLayer
    omega
  constructor
  · change e.val.1 i = _
    omega
  · change bondTip e.val i = _
    by_cases he : e.val.2 = i
    · have ht : bondTip e.val i = e.val.1 i + 1 := by simp [bondTip, ← he]
      rw [ht]
      simp only [waterCubeDirectionStep, he, ite_true]
      omega
    · simp only [bondTip, Function.update_of_ne (Ne.symm he)]
      simp only [waterCubeDirectionStep, he, ite_false]
      omega

/-- Exact depths for BOTH product orientations. -/
theorem waterCube_endpoint_depths {d : ℕ} (i : Fin d) (r R : ℕ)
    (e : IssuedBond (waterCube d i r R)) :
    let k := waterCubeLayer i r e.val.1
    let s := waterCubeDirectionStep i e
    let t := (issuedNetwork (waterCube d i r R)).tail e
    let u := (issuedNetwork (waterCube d i r R)).head e
    waterCubeOppositeDepth i r true t.val = k ∧
    waterCubeOppositeDepth i r true u.val = k + s ∧
    waterCubeOppositeDepth i r false t.val = 2 * r + 1 - k ∧
    waterCubeOppositeDepth i r false u.val = 2 * r + 1 - k - s := by
  dsimp only
  have hc := waterCube_endpoint_coordinates i r R e
  have hs := waterCubeDirectionStep_le_one i e
  have hk := waterCubeLayer_lt i r R (Finset.mem_product.mp e.property).1
  simp only [waterCubeOppositeDepth, ite_true, Bool.false_eq_true, ite_false]
  omega

/-- Off the middle layer, BOTH endpoints qualify for the far-face half-space
estimate: positive target below the middle, negative target above it. -/
theorem waterCube_endpoint_far_depths {d : ℕ} (i : Fin d) (r R : ℕ)
    (e : IssuedBond (waterCube d i r R)) :
    let k := waterCubeLayer i r e.val.1
    let t := (issuedNetwork (waterCube d i r R)).tail e
    let u := (issuedNetwork (waterCube d i r R)).head e
    (k < r → 2 * waterCubeOppositeDepth i r true t.val ≤ 2 * r + 1 ∧
      2 * waterCubeOppositeDepth i r true u.val ≤ 2 * r + 1) ∧
    (r < k → 2 * waterCubeOppositeDepth i r false t.val ≤ 2 * r + 1 ∧
      2 * waterCubeOppositeDepth i r false u.val ≤ 2 * r + 1) := by
  dsimp only
  have hd := waterCube_endpoint_depths i r R e
  dsimp only at hd
  have hs := waterCubeDirectionStep_le_one i e
  omega

/-- At the middle layer, every endpoint-to-target distance is at least r.
Ordinary-arm estimates apply here without a half-space depth assertion. -/
theorem waterCube_middle_target_depths {d : ℕ} (i : Fin d) (r R : ℕ)
    (e : IssuedBond (waterCube d i r R))
    (hk : waterCubeLayer i r e.val.1 = r) :
    ∀ upper : Bool,
      r ≤ waterCubeTargetDepth i r upper ((issuedNetwork (waterCube d i r R)).tail e).val ∧
      r ≤ waterCubeTargetDepth i r upper ((issuedNetwork (waterCube d i r R)).head e).val := by
  have hd := waterCube_endpoint_depths i r R e
  dsimp only at hd
  have hs := waterCubeDirectionStep_le_one i e
  intro upper
  cases upper <;> simp only [waterCubeTargetDepth, Bool.not_false, Bool.not_true] <;> omega

end NearCritical
