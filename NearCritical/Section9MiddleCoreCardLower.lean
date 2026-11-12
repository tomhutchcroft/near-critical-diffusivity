module
public import NearCritical.Section8ExtensionSourceGeometry
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Actual volume lower bound for the open source middle core. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- The actual OPEN side-n/2 middle core contains an explicit coordinate grid.
The bound includes n=1 and needs no parity convention or assumed volume estimate. -/
theorem section9_middle_core_card_lower {d : ℕ} (i : Fin d) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ)^d/(8 : ℝ)^d ≤ ((section8ExtensionMiddleCore i n).card : ℝ) := by
  let g : (Fin d → Fin (n/8+1)) → Vertex d := fun k =>
    Pi.single i (n : ℤ) + fun j => ((k j).val : ℤ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hg : Function.Injective g := by
    intro k ℓ heq
    funext j
    apply Fin.ext
    have hj := congrFun heq j
    change (Pi.single i (n : ℤ) : Vertex d) j+((k j).val : ℤ) =
      (Pi.single i (n : ℤ) : Vertex d) j+((ℓ j).val : ℤ) at hj
    omega
  have hmem (k : Fin d → Fin (n/8+1)) : g k ∈ section8ExtensionMiddleCore i n := by
    apply (section8_mem_extension_middle_core i n (g k)).mpr
    intro j
    have hkNat : 8*(k j).val ≤ n := by have := (k j).isLt; omega
    have hkR : ((k j).val : ℝ) ≤ (n : ℝ)/8 := by
      have hh : (8 : ℝ)*((k j).val : ℝ) ≤ n := by exact_mod_cast hkNat
      linarith
    have hk0 : (0 : ℝ) ≤ (k j).val := Nat.cast_nonneg _
    have hcoord : (g k j : ℝ)-(if j=i then (n : ℝ) else 0) = ((k j).val : ℝ) := by
      by_cases hji : j = i
      · subst j
        simp [g,Pi.add_apply,Pi.single_apply,Int.cast_add,Int.cast_natCast]
      · simp [g,Pi.add_apply,Pi.single_apply,hji,Ne.symm hji,Int.cast_add,Int.cast_natCast]
    rw [hcoord]
    constructor <;> linarith
  have hsub : (Finset.univ : Finset (Fin d → Fin (n/8+1))).image g ⊆
      section8ExtensionMiddleCore i n := by
    intro y hy
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hy
    exact hmem k
  have hcard : (n/8+1)^d ≤ (section8ExtensionMiddleCore i n).card := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hg] at hh
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin] using hh
  have hfloor : n ≤ 8*(n/8+1) := by omega
  have hfloorR : (n : ℝ) ≤ 8*((n/8+1 : ℕ) : ℝ) := by exact_mod_cast hfloor
  have hbase : (n : ℝ)/8 ≤ ((n/8+1 : ℕ) : ℝ) := by linarith
  calc
    _ = ((n : ℝ)/8)^d := (div_pow (n : ℝ) 8 d).symm
    _ ≤ (((n/8+1 : ℕ) : ℝ))^d := pow_le_pow_left₀ (by positivity) hbase d
    _ = (((n/8+1)^d : ℕ) : ℝ) := (Nat.cast_pow (n/8+1) d).symm
    _ ≤ _ := by exact_mod_cast hcard

end NearCritical
