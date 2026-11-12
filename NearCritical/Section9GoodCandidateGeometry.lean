module
public import NearCritical.Section9AvoidanceGoodExit
public import NearCritical.Section9AvoidanceSourceComparison
public import NearCritical.Section9MiddleGeometry

/-! Good last exits supply the exact source oriented-middle endpoint guard. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Both endpoints of an actual good last exit lie in S2=T12∩T23. If the
outer endpoint were outside T12, the actual available crossing would put its
inner endpoint in the forbidden exit face, contradicting the good-index guard.
No scale guard or pivotal-event identity is assumed. -/
theorem section9_good_last_exit_candidate_mem_oriented_middle {d : ℕ}
    (i : Fin d) (n : ℕ) (C F₃ : Finset (Vertex d))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (t : (Vertex d × Vertex d) × Bond d)
    (ht : t ∈ section9AvoidanceGoodLastExitCandidates
      (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) C
      (section9FiniteEndCube i n (2*(n : ℝ))) F₃ (section9ExitFace i n ∩ C)) :
    t.1 ∈ orientedLatticePairs (section9FiniteMiddle i n) := by
  obtain ⟨htJ,huNotV⟩ := Finset.mem_filter.mp ht
  have hm := Finset.mem_filter.mp htJ
  have hR := Finset.mem_product.mp (Finset.mem_product.mp hm.1).1
  have hbAvailable := (Finset.mem_product.mp hm.1).2
  have huC := hm.2.1
  have hends := hm.2.2.2
  have huL := hCL huC
  have hvL : t.1.2 ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) := by
    by_contra hvNotL
    have hguard := section9_source_exit_face_exterior_guard i n C
      (section9FiniteEndCube i n (2*(n : ℝ))) F₃ hCL t.2 hbAvailable
    have huV : t.1.1 ∈ section9ExitFace i n ∩ C := by
      rcases hends with ⟨huBase,hvTip⟩ | ⟨hvBase,huTip⟩
      · have hbaseC : t.2.1 ∈ C := huBase ▸ huC
        have htipNot : bondTip t.2 ∉ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) := by
          intro htipL
          exact hvNotL (hvTip.symm ▸ htipL)
        exact huBase.symm ▸ hguard.1 hbaseC htipNot
      · have htipC : bondTip t.2 ∈ C := huTip ▸ huC
        have hbaseNot : t.2.1 ∉ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) := by
          intro hbaseL
          exact hvNotL (hvBase.symm ▸ hbaseL)
        exact huTip.symm ▸ hguard.2 htipC hbaseNot
    exact huNotV huV
  have huMiddle : t.1.1 ∈ section9FiniteMiddle i n := by
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.mem_inter.mpr ⟨huL,hR.1⟩
  have hvMiddle : t.1.2 ∈ section9FiniteMiddle i n := by
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.mem_inter.mpr ⟨hvL,hR.2⟩
  have hadj : (openGraph (fun _ : Bond d => true)).Adj t.1.1 t.1.2 :=
    ⟨t.2,rfl,hends⟩
  exact (mem_orientedLatticePairs (section9FiniteMiddle i n) t.1.1 t.1.2).mpr
    ⟨huMiddle,hvMiddle,hadj⟩

end NearCritical
