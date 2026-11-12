module

public import NearCritical.Bernoulli

@[expose] public section
namespace NearCritical

/-- The unordered endpoints determine the positive-coordinate bond. -/
theorem section9_bond_endpoints_injective {d : ℕ} :
    Function.Injective (fun b : Bond d => s(b.1, bondTip b)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  rcases Sym2.eq_iff.mp h with ⟨hxy, ht⟩ | ⟨hxt, hty⟩
  · change x = y at hxy
    subst y
    have hij : i = j := by
      by_contra hne
      have hi := congrFun ht i
      simp [bondTip, hne] at hi
    subst j
    rfl
  · change x = bondTip (y, j) at hxt
    change bondTip (x, i) = y at hty
    have hi := congrFun hty i
    have hxi := congrFun hxt i
    by_cases hij : i = j
    · subst j
      simp [bondTip] at hi hxi
      omega
    · simp [bondTip, hij] at hi hxi
      omega

/-- An open adjacency at the endpoints of a selected physical bond
forces its particular Bernoulli coordinate to be true. -/
theorem section9_bond_open_of_adj {d : ℕ} {η : Configuration d}
    {e : Vertex d × Vertex d} {b : Bond d}
    (hends : s(b.1, bondTip b) = s(e.1, e.2))
    (he : (openGraph η).Adj e.1 e.2) : η b = true := by
  obtain ⟨c, hc, h | h⟩ := he
  · have hce : s(c.1, bondTip c) = s(e.1, e.2) :=
      Sym2.eq_iff.mpr (Or.inl ⟨h.1.symm, h.2.symm⟩)
    have hcb := section9_bond_endpoints_injective (hce.trans hends.symm)
    simpa only [hcb] using hc
  · have hce : s(c.1, bondTip c) = s(e.1, e.2) :=
      Sym2.eq_iff.mpr (Or.inr ⟨h.1.symm, h.2.symm⟩)
    have hcb := section9_bond_endpoints_injective (hce.trans hends.symm)
    simpa only [hcb] using hc

end NearCritical
