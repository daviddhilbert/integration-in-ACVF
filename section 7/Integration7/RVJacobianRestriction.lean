import Integration7.RVVolumeMorphisms

/-! Defined Jacobians agree on nested correspondences. This compares two
actual tangent graphs; it does not assert existence at singular points. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

theorem polynomialTangent_mono {K : Type*} [Field K] {d : ℕ}
    {C D : Set (Fin d → K)} (hCD : C ⊆ D) {p v : Fin d → K}
    (h : IsPolynomialTangent C p v) : IsPolynomialTangent D p v :=
  fun P hP => h P (fun z hz => hP z (hCD hz))

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rvJacobian_eq_of_subset {C D : Set (Fin (n + n) → CanonicalRV.RVSort M)}
    (hCD : C ⊆ D) {t s : Fin n → CanonicalRV.RVSort M} {ω η : CanonicalRV.RVSort M}
    (hC : IsRVJacobianAt C t s ω) (hD : IsRVJacobianAt D t s η) : ω = η := by
  obtain ⟨_, _, _, L, hL, _, hω⟩ := hC
  obtain ⟨_, _, _, K, hK, _, hη⟩ := hD
  have hnorm : normalizedCorrespondence C t s ⊆ normalizedCorrespondence D t s :=
    fun z hz => ⟨hCD hz.1, hz.2⟩
  have he : L = K := by
    apply LinearMap.ext
    intro x
    exact (hK x (L x)).mp (polynomialTangent_mono hnorm ((hL x (L x)).mpr rfl))
  exact hω.trans ((congrArg (fun A => ((∏ i, s i) / ∏ i, t i) *
    SpecialTransformations.Section4.ResiduePurity.residueRV (LinearMap.toMatrix' A).det) he).trans hη.symm)

end IntegrationInACVF.Section7
