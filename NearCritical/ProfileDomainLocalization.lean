module
public import NearCritical.ConnectionToSet
public import NearCritical.InhomogeneousExpectation

/-! Actual-law domain localization needed for the two-phase slab argument.
Restricted paths use only bonds with BOTH endpoints in the domain. No finite
cutoff, independence conclusion or probability equality is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory ProbabilityTheory
open scoped Classical

def domainClipConfiguration {d : ℕ} (S : Set (Vertex d)) (ω : Configuration d) : Configuration d :=
  fun e => if e.1 ∈ S ∧ bondTip e ∈ S then ω e else false

lemma measurable_domainClipConfiguration {d : ℕ} (S : Set (Vertex d)) :
    Measurable (domainClipConfiguration S) := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e.1 ∈ S ∧ bondTip e ∈ S
  · simpa [domainClipConfiguration,he] using measurable_pi_apply e
  · simp [domainClipConfiguration,he]

lemma restrictedGraph_eq_of_domain_agree {d : ℕ} (S : Set (Vertex d))
    (ω θ : Configuration d)
    (hagree : ∀ e : Bond d, e.1 ∈ S ∧ bondTip e ∈ S → ω e = θ e) :
    restrictedGraph ω S = restrictedGraph θ S := by
  have hle : ∀ α β : Configuration d,
      (∀ e : Bond d, e.1 ∈ S ∧ bondTip e ∈ S → α e = β e) →
      restrictedGraph α S ≤ restrictedGraph β S := by
    intro α β hαβ x y hxy
    obtain ⟨⟨e,he,hends⟩,hx,hy⟩ := hxy
    have hi : e.1 ∈ S ∧ bondTip e ∈ S := by
      rcases hends with ⟨hxb,hyt⟩ | ⟨hyb,hxt⟩
      · exact ⟨hxb ▸ hx,hyt ▸ hy⟩
      · exact ⟨hyb ▸ hy,hxt ▸ hx⟩
    exact ⟨⟨e,(hαβ e hi).symm.trans he,hends⟩,hx,hy⟩
  exact le_antisymm (hle ω θ hagree) (hle θ ω (fun e he => (hagree e he).symm))

lemma restrictedGraph_domainClip {d : ℕ} (S : Set (Vertex d)) (ω : Configuration d) :
    restrictedGraph (domainClipConfiguration S ω) S = restrictedGraph ω S := by
  apply restrictedGraph_eq_of_domain_agree
  intro e he
  simp [domainClipConfiguration,he]

lemma connectionToSetEvent_domainClip {d : ℕ} (S : Set (Vertex d)) (x : Vertex d)
    (A : Set (Vertex d)) :
    domainClipConfiguration S ⁻¹' connectionToSetEvent S x A = connectionToSetEvent S x A := by
  ext ω
  change (x ∈ S ∧ ∃ y, y ∈ A ∧ y ∈ S ∧
    (restrictedGraph (domainClipConfiguration S ω) S).Reachable x y) ↔ _
  rw [restrictedGraph_domainClip]
  rfl

/-- The full clipped product laws agree, even for infinite domains. -/
theorem percolationProfile_domainClip_map_eq {d : ℕ} (S : Set (Vertex d))
    (r s : Bond d → unitInterval)
    (hagree : ∀ e : Bond d, e.1 ∈ S ∧ bondTip e ∈ S → r e = s e) :
    (percolationProfile d r).map (domainClipConfiguration S) =
      (percolationProfile d s).map (domainClipConfiguration S) := by
  have hmap (q : Bond d → unitInterval) :
      (percolationProfile d q).map (domainClipConfiguration S) =
      Measure.infinitePi (fun e : Bond d => (bernoulliMeasure true false (q e)).map
        (fun b : Bool => if e.1 ∈ S ∧ bondTip e ∈ S then b else false)) := by
    exact Measure.infinitePi_map_pi (fun e : Bond d => bernoulliMeasure true false (q e))
      (f := fun (e : Bond d) (b : Bool) => if e.1 ∈ S ∧ bondTip e ∈ S then b else false)
      (fun e => measurable_of_finite _)
  rw [hmap,hmap]
  congr 1
  funext e
  by_cases he : e.1 ∈ S ∧ bondTip e ∈ S
  · rw [hagree e he]
  · simp [he]

/-- Actual restricted-connection probabilities depend ONLY on internal rates.
This supplies the homogeneous-law identification for source band suffixes. -/
theorem connectionToSet_profile_eq_of_internal_rates {d : ℕ} (S : Set (Vertex d))
    (r s : Bond d → unitInterval)
    (hagree : ∀ e : Bond d, e.1 ∈ S ∧ bondTip e ∈ S → r e = s e)
    (x : Vertex d) (A : Set (Vertex d)) :
    percolationProfile d r (connectionToSetEvent S x A) =
      percolationProfile d s (connectionToSetEvent S x A) := by
  have hmeas := measurableSet_connectionToSetEvent S x A
  have hclip := measurable_domainClipConfiguration S
  calc
    _ = (percolationProfile d r).map (domainClipConfiguration S) (connectionToSetEvent S x A) := by
      rw [Measure.map_apply hclip hmeas,connectionToSetEvent_domainClip]
    _ = (percolationProfile d s).map (domainClipConfiguration S) (connectionToSetEvent S x A) := by
      rw [percolationProfile_domainClip_map_eq S r s hagree]
    _ = _ := by rw [Measure.map_apply hclip hmeas,connectionToSetEvent_domainClip]

end NearCritical
