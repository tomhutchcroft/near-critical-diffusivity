module

public import NearCritical.SplitCrossStar
public import NearCritical.OpenEventHarris
public import NearCritical.BulkDomain

/-! Joining outward ray segments to the base connection in the outside
domain. Positive association supplies the cost of opening the segments. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical ENNReal

private theorem ray_reachable_of_vertices {d : ℕ} (ω : Configuration d) (D : Set (Vertex d))
    (a : Vertex d) (i : Fin d) (n : ℕ)
    (hD : ∀ k ≤ n, starTip a i k ∈ D)
    (hopen : ∀ e ∈ rayBonds a i n, ω e = true) :
    (restrictedGraph ω D).Reachable a (starTip a i n) := by
  have hreach : ∀ k ≤ n, (restrictedGraph ω D).Reachable a (starTip a i k) := by
    intro k
    induction k with
    | zero =>
        intro _
        have hz : coordinateRay i 0 = (0 : Vertex d) := by
          ext j
          by_cases hj : j = i <;> simp [coordinateRay, hj]
        simp [starTip, hz]
    | succ k ih =>
        intro hk
        have hb : (starTip a i k, i) ∈ rayBonds a i n :=
          Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
        have hstep : (restrictedGraph ω D).Adj (starTip a i k) (starTip a i (k + 1)) :=
          ⟨⟨_, hopen _ hb, Or.inl ⟨rfl, (rayBond_tip a i k).symm⟩⟩, hD k (by omega), hD _ hk⟩
        exact (ih (by omega)).trans hstep.reachable
  exact hreach n le_rfl

/-- Two positive coordinate segments can be attached to the ends of a
connection in a finite outside domain at a cost at most (p^{n+m}). -/
theorem outward_rays_connection_lower {d : ℕ} (p : unitInterval)
    (D : Finset (Vertex d)) (a b : Vertex d) (i j : Fin d) (n m : ℕ)
    (ha : ∀ k ≤ n, starTip a i k ∈ D) (hb : ∀ k ≤ m, starTip b j k ∈ D) :
    (p : ℝ) ^ (n + m) * (percolation d p).real
        (connectionToSetEvent (D : Set (Vertex d)) (starTip a i n) {starTip b j m}) ≤
      (percolation d p).real (connectionToSetEvent (D : Set (Vertex d)) a {b}) := by
  let S := rayBonds a i n ∪ rayBonds b j m
  let K := internalBondSet D ∪ S
  let A := connectionToSetEvent (D : Set (Vertex d)) (starTip a i n) {starTip b j m}
  let B := Set.pi (S : Set (Bond d)) (fun _ => ({true} : Set Bool))
  have hAi : BK.Increasing A := connectionToSetEvent_increasing _ _ _
  have hBi : BK.Increasing B := by
    intro ω θ hωθ hω e he
    exact hωθ e (hω e he)
  have hA : BK.truncation A K = A := by
    apply Set.Subset.antisymm (BK.truncation_subset hAi K)
    intro ω hω
    obtain ⟨hx, v, hv, hvD, hpath⟩ := hω
    refine ⟨hx, v, hv, hvD, hpath.mono ?_⟩
    intro u w h
    obtain ⟨⟨e, he, hEnds⟩, hu, hw⟩ := h
    have hendsD : e.1 ∈ D ∧ bondTip e ∈ D := by
      rcases hEnds with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨h₁ ▸ hu, h₂ ▸ hw⟩
      · exact ⟨h₁ ▸ hw, h₂ ▸ hu⟩
    have hK : e ∈ K := Finset.mem_union_left _ ((mem_internalBondSet _ _).mpr hendsD)
    exact ⟨⟨e, by simpa [Network.certificateConfiguration, hK] using he, hEnds⟩, hu, hw⟩
  have hB : BK.truncation B K = B := by
    apply Set.Subset.antisymm (BK.truncation_subset hBi K)
    intro ω hω e he
    have hK : e ∈ K := Finset.mem_union_right _ he
    simpa [Network.certificateConfiguration, hK] using hω e he
  have hH := percolation_truncation_harris d p hBi hAi K
  rw [hB, hA] at hH
  have hHR : (percolation d p).real B * (percolation d p).real A ≤
      (percolation d p).real (B ∩ A) := by
    simpa only [measureReal_def, ENNReal.toReal_mul] using
      (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
        (measure_ne_top _ _)).mpr hH
  have hmass : (percolation d p).real B = (p : ℝ) ^ S.card := by
    have h := congrArg ENNReal.toReal (percolation_open_cylinder d p S)
    simpa [B, measureReal_def, ENNReal.toReal_prod, ENNReal.toReal_ofReal p.2.1] using h
  have hcard : S.card ≤ n + m := by
    simpa [S, rayBonds_card] using Finset.card_union_le (rayBonds a i n) (rayBonds b j m)
  calc
    _ ≤ (percolation d p).real B * (percolation d p).real A := by
      rw [hmass]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one p.2.1 p.2.2 hcard) measureReal_nonneg
    _ ≤ _ := hHR
    _ ≤ _ := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro ω ⟨hopen, hconn⟩
      obtain ⟨_, v, hv, _, hp⟩ := hconn
      have hv' : v = starTip b j m := hv
      subst v
      have hp₁ := ray_reachable_of_vertices ω (D : Set (Vertex d)) a i n ha
        (fun e he => hopen e (Finset.mem_union_left _ he))
      have hp₂ := ray_reachable_of_vertices ω (D : Set (Vertex d)) b j m hb
        (fun e he => hopen e (Finset.mem_union_right _ he))
      have hz (k : Fin d) : coordinateRay k 0 = (0 : Vertex d) := by
        ext l
        by_cases hl : l = k <;> simp [coordinateRay, hl]
      have ha' : a ∈ D := by simpa [starTip, hz] using ha 0 (Nat.zero_le n)
      have hb' : b ∈ D := by simpa [starTip, hz] using hb 0 (Nat.zero_le m)
      exact ⟨ha', b, rfl, hb', hp₁.trans (hp.trans hp₂.symm)⟩

end NearCritical.SplitCrossDirect
