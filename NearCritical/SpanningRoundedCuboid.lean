module

public import NearCritical.SpanningSourceCuboid

/-! Exact source rational-coordinate sets at arbitrary integer side length.
Clearing denominators retains the integer lattice intersection without a
rounding premise. NEW lem.arm.2dspanning first-exit geometry only. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Source Lambda_n is the integer cube of radius floor(n/2). -/
lemma mem_centeredBox_half_iff {d n : ℕ} (x : Vertex d) :
    x ∈ centeredBox d (n/2) ↔ ∀ i, 2*|x i| ≤ (n:ℤ) := by
  have hloNat : 2*(n/2) ≤ n := by omega
  have hhiNat : n ≤ 2*(n/2)+1 := by omega
  have hlo : 2*((n/2:ℕ):ℤ) ≤ (n:ℤ) := by exact_mod_cast hloNat
  have hhi : (n:ℤ) ≤ 2*((n/2:ℕ):ℤ)+1 := by exact_mod_cast hhiNat
  constructor
  · intro hx i
    have hi := abs_le.mpr (mem_centeredBox.mp hx i)
    omega
  · intro hx
    apply mem_centeredBox.mpr
    intro i
    have hi := hx i
    have ha := abs_nonneg (x i)
    apply abs_le.mp
    omega

/-- Source cuboid |z_j|<=n/8 and -3n/8<=z_i<=3n, expressed
exactly on integer vertices by clearing denominators. -/
def roundedSourceSpanningCuboid {d : ℕ} (n : ℕ) (f : Fin d × Bool) : Set (Vertex d) :=
  {z | -3*(n:ℤ) ≤ 8*spanningSignedHeight f z ∧
    8*spanningSignedHeight f z ≤ 24*(n:ℤ) ∧
      ∀ j, j ≠ f.1 → 8*|z j| ≤ (n:ℤ)}

/-- Source target2n e_i+[-n/8,n/8]^d, with exact integer intersection. -/
def roundedSourceSpanningTarget {d : ℕ} (n : ℕ) (f : Fin d × Bool) : Set (Vertex d) :=
  {z | 15*(n:ℤ) ≤ 8*spanningSignedHeight f z ∧
    8*spanningSignedHeight f z ≤ 17*(n:ℤ) ∧
      ∀ j, j ≠ f.1 → 8*|z j| ≤ (n:ℤ)}

lemma roundedSourceSpanningCuboid_subset_corridor {d : ℕ} (n : ℕ) (f : Fin d × Bool) :
    roundedSourceSpanningCuboid n f ⊆ spanningCorridor (n/2) f := by
  intro z hz
  have hhiNat : n ≤ 2*(n/2)+1 := by omega
  have hhi : (n:ℤ) ≤ 2*((n/2:ℕ):ℤ)+1 := by exact_mod_cast hhiNat
  have hR : 0 ≤ ((n/2:ℕ):ℤ) := by positivity
  refine ⟨?_,?_⟩
  · have hs := hz.1
    rcases f with ⟨i,s⟩
    cases s <;> simp_all [spanningSignedHeight]
    <;> omega
  · intro j hj
    have ht := hz.2.2 j hj
    omega

lemma roundedSourceSpanningTarget_subset_corridorTarget {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin d × Bool) :
    roundedSourceSpanningTarget n f ⊆ spanningCorridorTarget (n/2) f := by
  intro z hz
  have hloNat : 2*(n/2) ≤ n := by omega
  have hlo : 2*((n/2:ℕ):ℤ) ≤ (n:ℤ) := by exact_mod_cast hloNat
  have hn' : (1:ℤ) ≤ n := by exact_mod_cast hn
  have hs := hz.1
  rcases f with ⟨i,s⟩
  cases s <;> simp_all [spanningSignedHeight, spanningCorridorTarget]
  <;> omega

/-- Literal source directional events imply actual simultaneous spanning for
EVERY positive integer side length, with no divisibility or rounding premise. -/
theorem all_roundedSourceSpanningCuboids_subset_spanning {d n : ℕ} (hn : 1 ≤ n)
    (x : Vertex d) (hx : x ∈ centeredBox d (n/2)) :
    {ω : Configuration d | ∀ f : Fin d × Bool,
      ω ∈ connectionToSetEvent (roundedSourceSpanningCuboid n f) x (roundedSourceSpanningTarget n f)} ⊆
        finiteRootSpanningEvent (centeredBox d (n/2)) (signedCubeFace d (n/2)) x := by
  apply Set.Subset.trans ?_ (all_spanningCorridors_subset_spanning x hx)
  intro ω hω f
  exact connectionToSetEvent_mono (roundedSourceSpanningCuboid_subset_corridor n f)
    (roundedSourceSpanningTarget_subset_corridorTarget hn f) x (hω f)

end NearCritical
