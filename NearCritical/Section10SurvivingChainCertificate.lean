module

public import NearCritical.SelectedNestChain
public import NearCritical.ChemicalCrossingAssembly
public import NearCritical.Section10ConditionalFlow
public import NearCritical.Section10RouteSites
public import NearCritical.TranslationInvariance

/-! The support step of `lem.chem.crossing`: nonzero conditional chain mass
selects an actual surviving outcome. Its local cluster data give the confined
certificate. The law producing those local data is a separate input. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped BigOperators

/-- An injectively indexed source route has at most two sites per level.
The count applies to the number of representative pieces, including the
terminal representative. -/
theorem source_route_piece_count {A : Type*} {M n : ℕ} (X : ℕ → A)
    (site : Fin (n + 1) → ℕ × A) (hinj : Function.Injective site)
    (hsite : ∀ j, site j ∈ routeSites M X) : n + 1 ≤ 2 * M := by
  classical
  let f : Fin (n + 1) → ↥(routeSites M X) := fun j => ⟨site j, hsite j⟩
  have hf : Function.Injective f := fun _ _ h => hinj (congrArg Subtype.val h)
  have hcard : n + 1 ≤ (routeSites M X).card := by
    simpa using Fintype.card_le_of_injective f hf
  apply hcard.trans
  unfold routeSites
  calc
    _ ≤ ∑ j ∈ Finset.range M, (routeLevelSites X j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range M, 2 := by
      apply Finset.sum_le_sum
      intro j _
      unfold routeLevelSites
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = 2 * M := by simp [mul_comm]

private theorem translated_box_point_of_face_height {d radius : ℕ}
    (a : Vertex d) (i : Fin d) {v : Vertex d} {h : ℤ}
    (hv : v ∈ translateSites a (chemicalCrossingSupport d radius i))
    (hh : h ≤ (radius : ℤ)) (hi : v i = a i + h) :
    ∃ x ∈ centeredBox d radius, x i = h ∧ a + x = v := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  have hxi : x i = h := by
    change a i + x i = a i + h at hi
    omega
  refine ⟨x, ?_, hxi, rfl⟩
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hx
  · have he := chemicalExitFace_coordinate i hx
    omega

/-- Positive total weight supplies a surviving route and choice in the support
of the flattened conditional law. -/
theorem exists_nonzero_chainWeight {R C : Type*} [Fintype R] [Fintype C]
    (μ w : R → ℝ) (κ ζ : R → C → ℝ)
    (hW : 0 < Network.conditionalChainMass μ w κ ζ) :
    ∃ r c, Network.conditionalChainWeight μ w κ ζ (r, c) ≠ 0 := by
  classical
  by_contra hnone
  rw [← Network.conditionalChainWeight_sum] at hW
  have hsum : (∑ i, Network.conditionalChainWeight μ w κ ζ i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_contra hi
    exact hnone ⟨i.1, i.2, hi⟩
  rw [hsum] at hW
  exact (lt_irrefl 0) hW

/-- A chain in the support of the source conditional law gives a crossing
certificate when its local data have the initial face and terminal open bond.
Only outcomes with nonzero weight need to provide data. -/
theorem chemicalChainCertificate_of_half_le_conditionalChainMass
    {d radius M : ℕ} {R C ι A : Type*} [Fintype R] [Fintype C]
    (a : Vertex d) (i : Fin d) (ω : Configuration d) {K B : ℝ}
    (X : R → ℕ → A) (μ w : R → ℝ) (κ ζ : R → C → ℝ)
    (hW : (1 / 2 : ℝ) ≤ Network.conditionalChainMass μ w κ ζ)
    (hdata : ∀ r c, Network.conditionalChainWeight μ w κ ζ (r, c) ≠ 0 →
      ∃ (n : ℕ) (tr : SelectedNestTrace d ι ω
          (translateSites a (chemicalCrossingSupport d radius i) : Set (Vertex d)) (2 * K) B n),
        (∃ site : Fin (n + 1) → ℕ × A, Function.Injective site ∧
          ∀ j, site j ∈ routeSites M (X r)) ∧
        (∃ x ∈ tr.interfaceSites 0 (tr.representative 0), x i = a i - (radius : ℤ)) ∧
        (∃ y ∈ tr.interfaceSites n (tr.representative n),
          y i = a i + (radius : ℤ) ∧ ω (y, i) = true)) :
    ω ∈ chemicalChainCertificateEvent a radius i (2 * K) B M := by
  obtain ⟨r, c, hc⟩ := exists_nonzero_chainWeight μ w κ ζ (by linarith)
  obtain ⟨n, tr, ⟨site, hinj, hsite⟩, ⟨u, hu, hui⟩, y, hysite, hyi, hopen⟩ :=
    hdata r c hc
  have hn := source_route_piece_count (X r) site hinj hsite
  have huD := tr.sites_subset 0 (Nat.zero_le n) (tr.interface_subset 0 (Nat.zero_le n) hu)
  have hyD := tr.sites_subset n le_rfl (tr.interface_subset n le_rfl hysite)
  obtain ⟨x, hx, hxi, hxu⟩ := translated_box_point_of_face_height a i huD
    (h := -(radius : ℤ)) (by omega) (by simpa only [sub_eq_add_neg] using hui)
  obtain ⟨v, hv, hvi, hvy⟩ := translated_box_point_of_face_height a i hyD le_rfl hyi
  let z := bondTip (v, i)
  have hz : z ∈ chemicalExitFace d radius i :=
    Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvi⟩, rfl⟩
  have htip : bondTip (y, i) = a + z := by
    rw [← hvy]
    exact bondTip_translate a (v, i)
  have hadj : (openGraph ω).Adj y (a + z) :=
    ⟨(y, i), hopen, Or.inl ⟨rfl, htip.symm⟩⟩
  have hzD : a + z ∈ translateSites a (chemicalCrossingSupport d radius i) :=
    (mem_translateSites a (chemicalCrossingSupport d radius i) z).mpr
      (Finset.mem_union.mpr (Or.inr hz))
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxi⟩, z, hz, y, n, hn,
    tr.geometry (hxu.symm ▸ hu) hysite, hadj, hyD, hzD⟩

end NearCritical.Section10
